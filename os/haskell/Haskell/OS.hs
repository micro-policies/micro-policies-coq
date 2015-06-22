{-# LANGUAGE RecursiveDo, RecordWildCards, TemplateHaskell #-}
module Haskell.OS where

import Control.Applicative
import Control.Monad.Reader

import Control.Lens

import Haskell.Util
import Haskell.Machine
import Haskell.Assembler hiding
  ( nop, const_, mov, binop, load, store, jump, bnz, jal
  , jumpEpc, addRule, getTag, putTag, halt )
import qualified Haskell.Assembler as A

import Language.Haskell.TH (mkName)
import Haskell.OS.TH.Accessors

newtype OSParameters = OSParameters { _yieldAddressVal :: Imm }
                  deriving (Eq, Ord, Show)
makeLensesWith (classyRules & lensClass %~ \orig name ->
                 let result = orig name
                 in if name == ''OSParameters
                    then result & traverse._2 .~ mkName "osParameters"
                    else result)
               ''OSParameters

data ProcessParameters = ProcessParameters { _sharedAddressVal :: !Imm
                                           , _yieldRVal        :: !Reg
                                           , _sharedPtrRVal    :: !Reg
                                           , _loopbackRVal     :: !Reg
                                           , _tempRVal         :: !Reg }
                       deriving (Eq, Ord, Show)
makeClassy ''ProcessParameters

data Parameters = Parameters { _subOSParameters      :: OSParameters
                             , _subProcessParameters :: ProcessParameters }
                deriving (Eq, Ord, Show)
makeLenses ''Parameters
instance HasOSParameters      Parameters where osParameters      = subOSParameters
instance HasProcessParameters Parameters where processParameters = subProcessParameters


makeMonadicAccessors ''OSParameters
makeMonadicAccessors ''ProcessParameters

type Program = SymAssemblerT (Reader Parameters)

r0 , r1,  r2 , r3 , r4 , r5 , r6 , r7  :: Applicative f => f Reg
r8,  r9,  r10, r11, r12, r13, r14, r15 :: Applicative f => f Reg
r16, r17, r18, r19, r20, r21, r22, r23 :: Applicative f => f Reg
r24, r25, r26, r27, r28, r29, r30, r31 :: Applicative f => f Reg
r0  = pure 0  ; r1  = pure 1  ; r2  = pure 2  ; r3  = pure 3
r4  = pure 4  ; r5  = pure 5  ; r6  = pure 6  ; r7  = pure 7
r8  = pure 8  ; r9  = pure 9  ; r10 = pure 10 ; r11 = pure 11
r12 = pure 12 ; r13 = pure 13 ; r14 = pure 14 ; r15 = pure 15
r16 = pure 16 ; r17 = pure 17 ; r18 = pure 18 ; r19 = pure 19
r20 = pure 20 ; r21 = pure 21 ; r22 = pure 22 ; r23 = pure 23
r24 = pure 24 ; r25 = pure 25 ; r26 = pure 26 ; r27 = pure 27
r28 = pure 28 ; r29 = pure 29 ; r30 = pure 30 ; r31 = pure 31

nop     :: MonadFix m => SymAssemblerT m ()
const_  :: MonadFix m => SymAssemblerT m Imm -> SymAssemblerT m Reg -> SymAssemblerT m ()
mov     :: MonadFix m => SymAssemblerT m Reg -> SymAssemblerT m Reg -> SymAssemblerT m ()
binop   :: MonadFix m => Binop -> SymAssemblerT m Reg -> SymAssemblerT m Reg -> SymAssemblerT m Reg -> SymAssemblerT m ()
load    :: MonadFix m => SymAssemblerT m Reg -> SymAssemblerT m Reg -> SymAssemblerT m ()
store   :: MonadFix m => SymAssemblerT m Reg -> SymAssemblerT m Reg -> SymAssemblerT m ()
jump    :: MonadFix m => SymAssemblerT m Reg -> SymAssemblerT m ()
bnz     :: MonadFix m => SymAssemblerT m Reg -> SymAssemblerT m Imm -> SymAssemblerT m ()
jal     :: MonadFix m => SymAssemblerT m Reg -> SymAssemblerT m ()
jumpEpc :: MonadFix m => SymAssemblerT m ()
addRule :: MonadFix m => SymAssemblerT m ()
getTag  :: MonadFix m => SymAssemblerT m Reg -> SymAssemblerT m Reg -> SymAssemblerT m ()
putTag  :: MonadFix m => SymAssemblerT m Reg -> SymAssemblerT m Reg -> SymAssemblerT m Reg -> SymAssemblerT m ()
halt    :: MonadFix m => SymAssemblerT m ()

nop     =         A.nop
const_  = bind2   A.const_
mov     = bind2   A.mov
binop   = bind3 . A.binop
load    = bind2   A.load
store   = bind2   A.store
jump    = bind1   A.jump
bnz     = bind2   A.bnz
jal     = bind1   A.jal
jumpEpc =         A.jumpEpc
addRule =         A.addRule
getTag  = bind2   A.getTag
putTag  = bind3   A.putTag
halt    =         A.halt


callerSaveMin, calleeSaveMin, userRegMax :: Applicative f => f Reg
callerSaveMin = r1
calleeSaveMin = r2
userRegMax    = r23

-- Somewhat ugly...
callerSaveRegs, calleeSaveRegs :: Applicative f => f [Reg]
callerSaveRegs = liftA2 enumFromTo callerSaveMin $ (subtract 1 <$>) calleeSaveMin
calleeSaveRegs = liftA2 enumFromTo calleeSaveMin $ (subtract 1 <$>) userRegMax

infiniteLoop :: MonadFix m => Reg -> SymAssemblerT m () -> SymAssemblerT m ()
infiniteLoop loopR body = mdo
  A.const_ loopAddr loopR
  loopAddr <- hereImm
  body
  A.jump loopR
