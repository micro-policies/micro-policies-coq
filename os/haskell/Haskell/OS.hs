{-# LANGUAGE RecursiveDo, FlexibleContexts, ConstraintKinds, RankNTypes,
             ViewPatterns, RecordWildCards, ScopedTypeVariables,
             QuasiQuotes, TemplateHaskell #-}
module Haskell.OS where

import Control.Applicative
import Control.Monad.Reader

import Control.Lens

import Haskell.Util
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

newtype OSParameters = OSParameters { _yieldAddrVal :: Imm }
                  deriving (Eq, Ord, Show)
makeLensesWith (classyRules & lensClass %~ \orig name ->
                 let result = orig name
                 in if name == ''OSParameters
                    then result & traverse._2 .~ mkName "osParameters"
                    else result)
               ''OSParameters
makeMonadicAccessors ''OSParameters

data ProcessParameters = ProcessParameters { _sharedAddrVal :: !Imm
                                           , _yieldRVal     :: !Reg
                                           , _sharedPtrRVal :: !Reg
                                           , _loopbackRVal  :: !Reg
                                           , _tempRVal      :: !Reg }
                       deriving (Eq, Ord, Show)
makeClassy ''ProcessParameters
makeMonadicAccessors ''ProcessParameters

type UserProgram env prog = ( MonadSymAssembler prog
                            , MonadReader env prog
                            , HasOSParameters env
                            , HasProcessParameters env )

freeReg :: UserProgram env prog => Integer -> prog Reg
freeReg i = do
  Reg (unsignedWord -> r) <- tempR
  let r' = r + i + 1
  if r' <= unsignedWord (regWord maxBound)
    then pure $ reg r'
    else asmError $ "freeReg: Register %r" ++ show r' ++ " out of range"

-- ra = 0 is special; register 1 is caller-save; registers 2+ are callee-save
callerSaveMin, callerSaveMax, calleeSaveMin, userRegMin, userRegMax :: Reg
callerSaveMin = r1
callerSaveMax = r1
calleeSaveMin = callerSaveMax + 1
calleeSaveMax = r15
userRegMin    = callerSaveMin
userRegMax    = calleeSaveMax

userRegs, callerSaveRegs, calleeSaveRegs :: [Reg]
userRegs       = [userRegMin    .. userRegMax]
callerSaveRegs = [callerSaveMin .. callerSaveMax]
calleeSaveRegs = [calleeSaveMin .. calleeSaveMax]

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
process init body = do
  processSetup init
  processLoop  body

add1Process :: UserProgram env prog => prog ()
add1Process = program $ do
  oneR <- freeReg 0
  process (const_ i1 oneR) $ \localR -> binop ADD localR oneR localR

mul2Process :: UserProgram env prog => prog ()
mul2Process = program $ do
  twoR <- freeReg 0
  process (const_ i2 twoR) $ \localR -> binop MUL localR twoR localR

-- A process info block stores pc/ra, then all the callee-save registers
pinfoSize :: MWord
pinfoSize = mword $ 1 + (int calleeSaveMax - int calleeSaveMin + 1)
  where int = unsignedWord . regWord
  -- 1 word for the stored pc to jump back to, plus one word for each register
  -- to save.

data SchedulerParameters = SchedulerParameters { _pidAddrVal   :: !Imm
                                               , _prog1AddrVal :: !Imm
                                               , _prog2AddrVal :: !Imm }
makeClassy ''SchedulerParameters
makeMonadicAccessors ''SchedulerParameters

type SchedulerProgram env prog = ( MonadSymAssembler prog
                                 , MonadReader env prog
                                 , HasSchedulerParameters env )

-- 'stempR' is caller-save!
stempR :: Reg
stempR = callerSaveMin

schedulerSetProgAddr :: SchedulerProgram env prog => prog ()
schedulerSetProgAddr = ifz stempR (const_ prog1Addr stempR) (const_ prog2Addr stempR)

schedulerForeachCalleeSaveReg :: MonadSymAssembler m => [eff'|!Reg -> m ()|] -> m ()
schedulerForeachCalleeSaveReg f =
  mapM_ (\r -> binop ADD stempR ra stempR >> f r) calleeSaveRegs

-- Saves the callee-save registers using only the single caller-save register,
-- plus ra (after saving it).
schedulerSaveRegisters :: SchedulerProgram env prog => prog ()
schedulerSaveRegisters = do
  const_ pidAddr stempR
  load   stempR  stempR
  schedulerSetProgAddr
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

schedulerCallProgram :: SchedulerProgram env prog => prog ()
schedulerCallProgram = do
  -- 'ra' still holds 1
  schedulerSetProgAddr
  schedulerForeachCalleeSaveReg $ load stempR
  const_ pidAddr stempR
  load   stempR stempR
  schedulerSetProgAddr
  load   stempR ra
  const_ i0 stempR
  jump   ra

schedulerYield :: SchedulerProgram env prog => prog ()
schedulerYield = do
  schedulerSaveRegisters
  schedulerChangePid
  schedulerCallProgram

schedulerInit :: [eff|SchedulerProgram env prog => !Imm -> !Imm -> prog ()|]
schedulerInit prog1 prog2 = do
  let stemp'R = stempR + 1
      storeImm addr val = do
        const_ addr stempR
        const_ val  stemp'R
        store  stempR stemp'R
  storeImm pidAddr   i0
  storeImm prog1Addr prog1
  storeImm prog2Addr prog2

scheduler' :: [eff|SchedulerProgram env prog => !Imm -> !Imm -> prog ()|]
scheduler' prog1 prog2 = do
    -- At boot-time, we start the scheduler...
    schedulerInit prog1 prog2
    -- ...then we jump to the first program.
    const_ prog1 ra
    jump   ra
    -- Later, we may come back to @yield@; it lives here, at the end of the OS
    -- code block.
    schedulerYield

-- The complete scheduler: boot code and the @yield@ system call.  It returns
-- the address of @yield@.
scheduler :: [eff|MonadSymAssembler m => !Imm -> !Imm -> m Imm|]
scheduler prog1 prog2 = program $ do
  -- We want to use @prog1@ and @prog2@ in a different monad
  -- (@ReaderT SchedulerParameters m@), so we get a pure value out of @prog1@
  -- and @prog2@.  I don't quite get why we need to give them type
  -- signatures... something to do with polymorphism, I guess.
  (prog1' :: Imm) <- effectful prog1
  (prog2' :: Imm) <- effectful prog2
  
  _pidAddrVal   <- reserveImm 1
  _prog1AddrVal <- reserveImm pinfoSize
  _prog2AddrVal <- reserveImm pinfoSize
  flip runReaderT SchedulerParameters{..} $ do
    -- At boot-time, we start the scheduler...
    schedulerInit prog1' prog2'
    -- ...then we jump to the first program.
    const_ prog1' ra
    jump   ra
    -- Later, we may come back to @yield@; it lives here, at the end of the OS
    -- code block.
    hereImm <* schedulerYield
