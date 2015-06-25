{-# LANGUAGE RecursiveDo, FlexibleContexts, ConstraintKinds, RankNTypes,
             ViewPatterns, RecordWildCards, ScopedTypeVariables,
             QuasiQuotes, TemplateHaskell #-}
module Haskell.OS where

import Control.Applicative
import Control.Monad.Reader
import Control.Lens

import Data.List

import Haskell.Word
import Haskell.Machine
import Haskell.Assembler hiding
  ( nop, const_, mov, binop, load, store, jump, bnz, jal
  , jumpEpc, addRule, getTag, putTag, halt )
import qualified Haskell.Assembler as A

import Haskell.ImplicitEffects
import Haskell.ImplicitEffects.QQ

import Language.Haskell.TH (mkName)
import Haskell.OS.TH.Accessors

--------------------------------------------------------------------------------
-- GENERAL
--------------------------------------------------------------------------------

-- Notationally nice (and dodges some polymorphism issues)
r0,  r1,  r2,  r3,  r4,  r5,  r6,  r7,  r8,  r9,  r10, r11, r12, r13, r14, r15 :: Reg
r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31 :: Reg
r0  = 0  ; r1  = 1  ; r2  = 2  ; r3  = 3  ; r4  = 4  ; r5  = 5  ; r6  = 6  ; r7  = 7
r8  = 8  ; r9  = 9  ; r10 = 10 ; r11 = 11 ; r12 = 12 ; r13 = 13 ; r14 = 14 ; r15 = 15
r16 = 16 ; r17 = 17 ; r18 = 18 ; r19 = 19 ; r20 = 20 ; r21 = 21 ; r22 = 22 ; r23 = 23
r24 = 24 ; r25 = 25 ; r26 = 26 ; r27 = 27 ; r28 = 28 ; r29 = 29 ; r30 = 30 ; r31 = 31

-- These are more about monomorphism and less about notation :-)
i0,  i1,  i2,  i3,  i4,  i5,  i6,  i7,  i8,  i9,  i10, i11, i12, i13, i14, i15 :: Imm
i16, i17, i18, i19, i20, i21, i22, i23, i24, i25, i26, i27, i28, i29, i30, i31 :: Imm
i0  = 0  ; i1  = 1  ; i2  = 2  ; i3  = 3  ; i4  = 4  ; i5  = 5  ; i6  = 6  ; i7  = 7
i8  = 8  ; i9  = 9  ; i10 = 10 ; i11 = 11 ; i12 = 12 ; i13 = 13 ; i14 = 14 ; i15 = 15
i16 = 16 ; i17 = 17 ; i18 = 18 ; i19 = 19 ; i20 = 20 ; i21 = 21 ; i22 = 22 ; i23 = 23
i24 = 24 ; i25 = 25 ; i26 = 26 ; i27 = 27 ; i28 = 28 ; i29 = 29 ; i30 = 30 ; i31 = 31

nop     :: [eff|MonadSymAssembler m => m ()|]
const_  :: [eff|MonadSymAssembler m => !Imm -> !Reg -> m ()|]
mov     :: [eff|MonadSymAssembler m => !Reg -> !Reg -> m ()|]
binop   :: [eff|MonadSymAssembler m => Binop -> !Reg -> !Reg -> !Reg -> m ()|]
load    :: [eff|MonadSymAssembler m => !Reg -> !Reg -> m ()|]
store   :: [eff|MonadSymAssembler m => !Reg -> !Reg -> m ()|]
jump    :: [eff|MonadSymAssembler m => !Reg -> m ()|]
bnz     :: [eff|MonadSymAssembler m => !Reg -> !Imm -> m ()|]
jal     :: [eff|MonadSymAssembler m => !Reg -> m ()|]
jumpEpc :: [eff|MonadSymAssembler m => m ()|]
addRule :: [eff|MonadSymAssembler m => m ()|]
getTag  :: [eff|MonadSymAssembler m => !Reg -> !Reg -> m ()|]
putTag  :: [eff|MonadSymAssembler m => !Reg -> !Reg -> !Reg -> m ()|]
halt    :: [eff|MonadSymAssembler m => m ()|]

nop     =                  A.nop
const_  = bindEffectful2   A.const_
mov     = bindEffectful2   A.mov
binop   = bindEffectful3 . A.binop
load    = bindEffectful2   A.load
store   = bindEffectful2   A.store
jump    = bindEffectful1   A.jump
bnz     = bindEffectful2   A.bnz
jal     = bindEffectful1   A.jal
jumpEpc =                  A.jumpEpc
addRule =                  A.addRule
getTag  = bindEffectful2   A.getTag
putTag  = bindEffectful3   A.putTag
halt    =                  A.halt

infiniteLoop :: [eff|MonadSymAssembler m => !Reg -> m () -> m ()|]
infiniteLoop loopR body = mdo
  const_ loopAddr loopR
  loopAddr <- hereImm
  body
  jump loopR

-- @ifz r ifZero ifNonzero@: If @r@ is zero, execute @ifZero@; otherwise, if it
-- is nonzero, execute @ifNonzero@.  /Do not modify @r@ inside @ifZero@!/
ifz :: [eff|MonadSymAssembler m => !Reg -> m () -> m () -> m ()|]
ifz r ifZero ifNonzero = mdo {
  bnz r (nonzeroAddr - zeroAddr + 1);
    zeroAddr <- hereImm;
    ifZero;
  bnz r (doneAddr - nonzeroAddr + 1); -- Unconditionally skip the else block
    nonzeroAddr <- hereImm;
    ifNonzero;
  doneAddr <- hereImm;
  return () }

addrsAround :: MonadSymAssembler m => m () -> m (Imm, Imm)
addrsAround asm = (,) <$> hereImm <* asm <*> (subtract 1 <$> hereImm)

withAddrsAround :: MonadSymAssembler m => m a -> m (a,(Imm, Imm))
withAddrsAround asm =
  (\pre x post -> (x,(pre,post))) <$> hereImm <*> asm <*> (subtract 1 <$> hereImm)

-- ra = 0 is special; register 1 is caller-save; registers 2+ are callee-save
callerSaveMin, callerSaveMax, calleeSaveMin, calleeSaveMax, userRegMin, userRegMax :: Reg
callerSaveMin = r1
callerSaveMax = r1
calleeSaveMin = callerSaveMax + 1
calleeSaveMax = r23
userRegMin    = callerSaveMin
userRegMax    = calleeSaveMax

userRegs, callerSaveRegs, calleeSaveRegs :: [Reg]
userRegs       = [userRegMin    .. userRegMax]
callerSaveRegs = [callerSaveMin .. callerSaveMax]
calleeSaveRegs = [calleeSaveMin .. calleeSaveMax]

regAfter :: [eff|MonadSymAssembler m => String -> !Reg -> Integer -> m Reg|]
regAfter who base i = do
  Reg (unsignedWord -> r) <- effectful base
  let r' = r + i + 1
  if r' <= toInteger (maxBound :: Reg)
    then pure $ reg r'
    else asmError $ who ++ ": Register %r" ++ show r' ++ " out of range"

--------------------------------------------------------------------------------
-- USER-LEVEL PROCESSES
--------------------------------------------------------------------------------

newtype OSParameters = OSParameters { _yieldAddrVal :: Imm }
                  deriving (Eq, Ord, Show)
makeLensesWith (classyRules & lensClass %~ \orig name ->
                 let result = orig name
                 in if name == ''OSParameters
                    then result & traverse._2 .~ mkName "osParameters"
                    else result)
               ''OSParameters
makeMonadicAccessors ''OSParameters

-- NOTE: '_sharedAddrVal' /cannot/ be strict!  Otherwise, the knot-tying we do
-- later triggers an infinite loop immediately.
--
-- Also, do the registers *really* need to live here?  Could they be global
-- values?
data ProcessParameters = ProcessParameters { _sharedAddrVal :: Imm
                                           , _yieldRVal     :: {-!-}Reg
                                           , _sharedPtrRVal :: {-!-}Reg
                                           , _loopbackRVal  :: {-!-}Reg
                                           , _tempRVal      :: {-!-}Reg }
                       deriving (Eq, Ord, Show)
makeClassy           ''ProcessParameters
makeMonadicAccessors ''ProcessParameters

type UserProgram env prog = ( MonadSymAssembler prog
                            , MonadReader env prog
                            , HasOSParameters env
                            , HasProcessParameters env )

data UserCodeParameters =
  UserCodeParameters { _userOSParameters      :: OSParameters
                     , _userProcessParameters :: ProcessParameters }
  deriving (Eq, Ord, Show)
makeClassy ''UserCodeParameters
instance HasOSParameters      UserCodeParameters where osParameters      = userOSParameters
instance HasProcessParameters UserCodeParameters where processParameters = userProcessParameters

freeReg :: UserProgram env prog => Integer -> prog Reg
freeReg = regAfter "freeReg" tempR

processSetup :: UserProgram env prog => prog () -> prog ()
processSetup extra = do
  const_ yieldAddr  yieldR
  const_ sharedAddr sharedPtrR
  extra

processLoop :: UserProgram env prog => [eff'|!Reg -> prog ()|] -> prog ()
processLoop body = do
  infiniteLoop loopbackR $ do
    load  sharedPtrR tempR
    body  tempR
    store sharedPtrR tempR
    jal   yieldR

process :: UserProgram env prog => prog () -> [eff'|!Reg -> prog ()|] -> prog ()
process init body = program $ do
  processSetup init
  processLoop  body

add1Process :: UserProgram env prog => prog ()
add1Process = do
  oneR <- freeReg 0
  process (const_ i1 oneR) $ \localR -> binop ADD localR oneR localR

mul2Process :: UserProgram env prog => prog ()
mul2Process = do
  twoR <- freeReg 0
  process (const_ i2 twoR) $ \localR -> binop MUL localR twoR localR

-- The information about the user code needed for compartmentalization.  Not
-- lensy because it's really just for temporary internal use.  The shared
-- address is filled in lazily, and so cannot be strict.
data UserCodeInfo = UserCodeInfo { userAdd1Compartment :: (Imm,Imm)
                                 , userMul2Compartment :: (Imm,Imm)
                                 , userSharedAddr      :: Imm }
                  deriving (Eq, Ord, Show)

-- All of the user code: both processes and their shared address (which is part
-- of the first process)
userCode :: [eff|MonadSymAssembler m => !Imm -> m UserCodeInfo|]
userCode yieldAddrE = program $ mdo
  _yieldAddrVal <- effectful yieldAddrE
  let _yieldRVal : _sharedPtrRVal : _loopbackRVal : _tempRVal : _ = calleeSaveRegs
      _sharedAddrVal = userSharedAddr info
      userParams = UserCodeParameters
                     { _userOSParameters      = OSParameters{..}
                     , _userProcessParameters = ProcessParameters{..} }
  
  info <- flip runReaderT userParams $ do
    (userSharedAddr, userAdd1Compartment) <-
      withAddrsAround . program $ add1Process *> reserveImm 1
    userMul2Compartment <-
      addrsAround mul2Process
    pure UserCodeInfo{..}
  pure info

--------------------------------------------------------------------------------
-- THE SCHEDULER (INCLUDING YIELD)
--------------------------------------------------------------------------------

data SchedulerParameters = SchedulerParameters { _pidAddrVal   :: Imm
                                               , _proc1AddrVal :: Imm
                                               , _proc2AddrVal :: Imm }
makeClassy           ''SchedulerParameters
makeMonadicAccessors ''SchedulerParameters

type SchedulerProgram env prog = ( MonadSymAssembler prog
                                 , MonadReader env prog
                                 , HasSchedulerParameters env )

-- A process info block stores pc/ra, then all the callee-save registers
pinfoSize :: MWord
pinfoSize = 1 + (widenReg (calleeSaveMax - calleeSaveMin) + 1)
  -- 1 word for the stored pc to jump back to, plus one word for each register
  -- to save.

-- 'stempR' is caller-save!
stempR :: Reg
stempR = callerSaveMin

schedulerSetProcAddr :: SchedulerProgram env prog => prog ()
schedulerSetProcAddr =
  ifz stempR (const_ proc1Addr stempR) (const_ proc2Addr stempR)

schedulerForeachCalleeSaveReg :: MonadSymAssembler m
                              => [eff'|!Reg -> m ()|] -> m ()
schedulerForeachCalleeSaveReg f =
  mapM_ (\r -> binop ADD stempR ra stempR >> f r) calleeSaveRegs

-- Saves the callee-save registers using only the single caller-save register,
-- plus ra (after saving it).
schedulerSaveRegisters :: SchedulerProgram env prog => prog ()
schedulerSaveRegisters = do
  const_ pidAddr stempR
  load   stempR  stempR
  schedulerSetProcAddr
  store  stempR ra
  const_ i1 ra
  schedulerForeachCalleeSaveReg $ store stempR

schedulerChangePid :: SchedulerProgram env prog => prog ()
schedulerChangePid = do
  -- 'ra' still holds 1
  let stemp'R = stempR + 1
  const_    pidAddr stemp'R
  load      stemp'R stempR
  binop SUB ra stempR stempR -- Swap the pc between 0 and 1
  store     stemp'R stempR

schedulerCallProcess :: SchedulerProgram env prog => prog ()
schedulerCallProcess = do
  -- 'ra' still holds 1
  schedulerSetProcAddr
  schedulerForeachCalleeSaveReg $ load stempR
  const_ pidAddr stempR
  load   stempR stempR
  schedulerSetProcAddr
  load   stempR ra
  const_ i0 stempR
  jump   ra

schedulerYield :: SchedulerProgram env prog => prog ()
schedulerYield = do
  schedulerSaveRegisters
  schedulerChangePid
  schedulerCallProcess

schedulerInit :: [eff|SchedulerProgram env prog => !Imm -> !Imm -> prog ()|]
schedulerInit proc1 proc2 = do
  let stemp'R = stempR + 1
      storeImm addr val = do
        const_ addr stempR
        const_ val  stemp'R
        store  stempR stemp'R
  storeImm pidAddr   i0
  storeImm proc1Addr proc1
  storeImm proc2Addr proc2
  mapM_ (const_ i0) [stempR, stemp'R] -- Clear registers

-- The information about the scheduler needed for various purposes (mostly
-- compartmentalization).  Not lensy because it's really just for temporary
-- internal use.
data SchedulerInfo = SchedulerInfo { schedulerInitCompartment  :: (Imm,Imm)
                                   , schedulerYieldCompartment :: (Imm,Imm)
                                   , schedulerPIDAddr          :: {-!-}Imm
                                   , schedulerProc1Addr        :: {-!-}Imm
                                   , schedulerProc2Addr        :: {-!-}Imm }
            deriving (Eq, Ord, Show)

-- The complete scheduler: initialization code and the @yield@ system call.
scheduler :: [eff|MonadSymAssembler m => !Imm -> !Imm -> m SchedulerInfo|]
scheduler proc1E proc2E = program $ do
  -- We want to use @proc1@ and @proc2@ in a different monad
  -- (@ReaderT SchedulerParameters m@), so we get a pure value out of @proc1@
  -- and @proc2@.  I don't quite get why we need to give them type
  -- signatures... something to do with polymorphism, I guess.
  (proc1 :: Imm) <- effectful proc1E
  (proc2 :: Imm) <- effectful proc2E

  -- These names get bound in both the 'SchedulerParameters' and the
  -- 'SchedulerInfo', so....  (I'm sorry.)
  _pidAddrVal   @ schedulerPIDAddr   <- reserveImm 1
  _proc1AddrVal @ schedulerProc1Addr <- reserveImm pinfoSize
  _proc2AddrVal @ schedulerProc2Addr <- reserveImm pinfoSize
  
  flip runReaderT SchedulerParameters{..} $ do
    schedulerInitCompartment <- addrsAround . program $ do
      -- At boot-time, we start the scheduler...
      schedulerInit proc1 proc2
      -- ...clear out our registers...
      mapM_ (const_ i0) [stempR, stempR + 1]
      -- ...and then we jump to the first process.
      const_ proc1 ra
      jump   ra
    -- Later, we may come back to @yield@; it lives here, at the end of the OS
    -- code block.
    schedulerYieldCompartment <- addrsAround schedulerYield
    pure SchedulerInfo{..}

--------------------------------------------------------------------------------
-- THE BOOT-TIME TAGGING KERNEL
--------------------------------------------------------------------------------

-- As with '_sharedAddrVal', these fields must be lazy (see above).  This is the
-- 'Imm' counterpart to 'Haskell.Machine.SyscallAddresses' -- the words are
-- smaller, so we couldn't fit the whole word "Address" :-)
data SyscallAddrs = SyscallAddrs { _isolateAddrVal           :: Imm
                                 , _addToJumpTargetsAddrVal  :: Imm
                                 , _addToStoreTargetsAddrVal :: Imm }
                  deriving (Eq, Ord, Show)
makeClassy           ''SyscallAddrs
makeMonadicAccessors ''SyscallAddrs

widenSyscalls :: SyscallAddrs -> SyscallAddresses
widenSyscalls addrs =
  SyscallAddresses { isolateAddress           = widenImm $ addrs^.isolateAddrVal
                   , addToJumpTargetsAddress  = widenImm $ addrs^.addToJumpTargetsAddrVal
                   , addToStoreTargetsAddress = widenImm $ addrs^.addToStoreTargetsAddrVal }

-- Note: the kernel is prior to the whole user/nonuser caller/callee register
-- stuff, so these can be any register we want -- /except/ for `ra`!
data KernelRegisters = KernelRegisters { _oneRVal     :: {-!-}Reg
                                       , _serviceRVal :: {-!-}Reg
                                       , _ktempRVal   :: {-!-}Reg }
                     deriving (Eq, Ord, Show)
makeClassy           ''KernelRegisters
makeMonadicAccessors ''KernelRegisters

data KernelParameters =
  KernelParameters { _kernelSyscallAddrs    :: SyscallAddrs
                   , _kernelKernelRegisters :: KernelRegisters }
  deriving (Eq, Ord, Show)
makeClassy ''KernelParameters
instance HasSyscallAddrs    KernelParameters where syscallAddrs    = kernelSyscallAddrs
instance HasKernelRegisters KernelParameters where kernelRegisters = kernelKernelRegisters

type KernelProgram env prog = ( MonadSymAssembler prog
                              , MonadReader env prog
                              , HasSyscallAddrs env 
                              , HasKernelRegisters env )

freeRegK :: KernelProgram env prog => Integer -> prog Reg
freeRegK = regAfter "freeRegK" ktempR

-- Collapses contiguous runs into a @(min,max)@ pair.
collapse :: (Enum a, Eq a) => [a] -> [(a,a)]
collapse []     = []
collapse (x:xs) = go x x xs where
  go l h []     = [(l,h)]
  go l h (x:xs) | succ h == x = go l x xs
                | otherwise   = (l,h) : go x x xs
    -- It's safe to use 'succ' here, because @x > h@.

-- Store the list of ranges to the location stored in @reg@; returns the amount
-- of space used/needed
storeRanges :: [eff|KernelProgram env prog => !Reg -> [(Imm,Imm)] -> prog Imm|]
storeRanges reg ranges = do
  let count = genericLength ranges
  
  const_ count ktempR
  store  reg ktempR

  -- This pattern match /must/ be lazy, as the compartments may come from the
  -- future; we must be careful not to actually force such values in any way, on
  -- pain of infinite loops.  (We could also solve this problem by returning
  -- individual tuple components or reconstructing any tuple @range@ as @(fst
  -- range, snd range)@.  This seems nicer, however.)
  forM_ ranges $ \ ~(low,high) -> do
    binop ADD reg oneR reg
    const_    low ktempR
    store     reg ktempR
    
    binop ADD reg oneR reg
    const_    high ktempR
    store     reg ktempR
  
  pure $ 1 + 2*count

isolate :: [eff|KernelProgram env prog
        => [(Imm,Imm)] -> [(Imm,Imm)] -> [(Imm,Imm)]
        -> !Reg -> !Imm
        -> prog Imm|]
isolate addrs jumpTargets storeTargets reg argsAddr = do
  let setArg argR arg = do
        mov reg argR
        storeRanges reg arg
  
  needed <- sum <$> sequence
    [ const_ argsAddr reg    *> setArg syscallArg1 addrs
    , binop ADD reg oneR reg *> setArg syscallArg2 jumpTargets
    , binop ADD reg oneR reg *> setArg syscallArg3 storeTargets ]
  const_ isolateAddr serviceR
  jal serviceR
  pure needed

addToJumpTargets :: [eff|KernelProgram env prog => !Imm -> prog ()|]
addToJumpTargets jumpTarget = do
  const_ jumpTarget           syscallArg1
  const_ addToJumpTargetsAddr serviceR
  jal    serviceR

addToStoreTargets :: [eff|KernelProgram env prog => !Imm -> prog ()|]
addToStoreTargets storeTarget = do
  const_ storeTarget           syscallArg1
  const_ addToStoreTargetsAddr serviceR
  jal    serviceR

kernel :: MonadSymAssembler m
       => SyscallAddrs
       -> SchedulerInfo -> UserCodeInfo
       -> m ()
kernel _kernelSyscallAddrs ~SchedulerInfo{..} ~UserCodeInfo{..} = program $ do
  -- The info record pattern matches /must/ be lazy, as they come from the
  -- future; we must be careful not to actually force such values in any way, on
  -- pain of infinite loops.  We haven't encountered this problem before because
  -- we've just passed around whole values from the future, not ones we needed
  -- to break apart.
  let _oneRVal : _serviceRVal : _ktempRVal : _ = [ra+1..]
      _kernelKernelRegisters = KernelRegisters{..}
  
  flip runReaderT KernelParameters{..} $ mdo
    -- Set up registers
    const_ i1 oneR
    
    -- Set up the compartments!  Important: they must be set up in /dependency
    -- order/.  This means that if compartment $c$ can jump or write to anywhere
    -- in compartment $d$, then compartment $c$ must be split off /first/.
    -- Otherwise, when the kernel attempts to grant $c$ jump/write access to a
    -- part of $d$, it won't have permission, as the kernel will no longer own
    -- those addresses!  If there are cycles, they can be broken by granting the
    -- kernel explicit jump/write access.
    --
    -- This shows up twice in the kernel
    --
    --   1. The kernel must claim the start of the @yield@ service as a jump
    --      target, even though it does not jump to it, to break a cycle:
    --      @yield@ must have jump access to all of the userland code, and all
    --      of the userland code must have access to the start of @yield@.
    --
    --   2. The second user compartment, for the multiply-by-two process, must
    --      be set up before the first user compartment, for the add-one
    --      process; this is because the add-one process holds the shared
    --      address.
    let applyAllTo x = ($ x) . sequence
        runSyscalls  = sequence . applyAllTo argSpace . applyAllTo (freeRegK 0)
        start        = join (,) . fst
        singleAddrs  = map (join (,))
          -- This wants to be @collapse . sort@, but alas, it can't -- that
          -- performs the dreaded computation on values from the future.
          -- Luckily, these doesn't cost us very much.

    addToJumpTargets (fst schedulerInitCompartment)  -- We take this jump
    addToJumpTargets (fst schedulerYieldCompartment) -- Isolation dependency
    argSpace <- reserveImm . widenImm . maximum =<< runSyscalls
      [ isolate          [schedulerInitCompartment]
                         [start userAdd1Compartment]
                         (singleAddrs [schedulerPIDAddr, schedulerProc1Addr, schedulerProc2Addr])
      , isolate          [schedulerYieldCompartment]
                         [userAdd1Compartment, userMul2Compartment]
                         []
      , isolate          [userMul2Compartment]
                         [start schedulerYieldCompartment]
                         (singleAddrs [userSharedAddr])
      , isolate          [userAdd1Compartment]
                         [start schedulerYieldCompartment]
                         [] ]
      
    -- Clear registers; first the monadic ones, and then the pure ones :-)
    mapM_ (const_ i0) [oneR, serviceR, ktempR, freeRegK 0]
    mapM_ (const_ i0) [syscallRet, syscallArg1, syscallArg2, syscallArg3 ]
    
    -- Jump to the scheduler initialization code
    const_ (fst schedulerInitCompartment) ra
    jump ra

--------------------------------------------------------------------------------
-- THE WHOLE OS
--------------------------------------------------------------------------------

-- The information about the OS one might want for either debugging or running
-- purposes
data OSInfo = OSInfo { _osSharedAddress    :: {-!-}MWord
                     , _osYieldAddress     :: {-!-}MWord
                     , _osAdd1Address      :: {-!-}MWord
                     , _osMul2Address      :: {-!-}MWord
                     , _osSyscallAddresses :: {-!-}SyscallAddresses }
            deriving (Eq, Ord, Show)
makeLenses ''OSInfo

wholeOS :: MonadSymAssembler m => m OSInfo
wholeOS = program $ mdo
  -- Compartmentalization kernel code
  kernel syscalls schedulerInfo userCodeInfo
  
  -- OS code
  schedulerInfo@SchedulerInfo{..} <- scheduler add1Address mul2Address
  let yieldAddress = fst schedulerYieldCompartment
  
  -- User code
  userCodeInfo@UserCodeInfo{..} <- userCode yieldAddress
  let add1Address = fst userAdd1Compartment
      mul2Address = fst userMul2Compartment
  
  -- Syscalls
  end <- hereImm
  let _isolateAddrVal           = 100 * ((end `quot` 100) + 1)
      _addToJumpTargetsAddrVal  = _isolateAddrVal + 100
      _addToStoreTargetsAddrVal = _addToJumpTargetsAddrVal + 100
      syscalls                  = SyscallAddrs{..}
      -- We put the syscalls at multiples of 100 so they're easy to spot; as
      -- long as they're out of range, it doesn't matter.
  
  -- The final result
  return OSInfo{ _osSharedAddress            = widenImm      userSharedAddr
               , _osYieldAddress             = widenImm      yieldAddress
               , _osAdd1Address              = widenImm      add1Address
               , _osMul2Address              = widenImm      mul2Address
               , _osSyscallAddresses         = widenSyscalls syscalls }

osInfo     :: OSInfo
osSyscalls :: SyscallAddresses
os         :: State
(osInfo, osSyscalls, os) = case runAssembler wholeOS of
  Right (osInfo, osMem) ->
    (osInfo, osInfo^.osSyscallAddresses, initialState osMem [r0..userRegMax])
  Left err ->
    error $ "Could not build OS: " ++ err

os0 :: State
os0 = os

stepOS' :: Integral i => i -> (i, State)
stepOS' = flip (stepMany' osSyscalls) os0

stepOS :: Integral i => i -> Maybe State
stepOS = flip (stepMany osSyscalls) os0
