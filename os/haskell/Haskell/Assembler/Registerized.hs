{-# LANGUAGE PolyKinds, DataKinds, TypeFamilies, UndecidableInstances,
             TypeOperators,
             GeneralizedNewtypeDeriving,
             ConstraintKinds, GADTs, TemplateHaskell #-}
module Haskell.Assembler.Registerized (
  SymAssemblerR(), getSymAssemblerR, runSymAssemblerR, execSymAssemblerR,
  reserve,
  here, reservedSegment,
  asmError, asmDelayedError,
  program,
  nop, const_, mov, binop, load, store, jump, bnz, jal,
  jumpEpc, addRule, getTag, putTag,
  halt,
  tryMWordImm,
  immediateTooBigMsg, addrToImm, addrToImm',
  hereImm, reserveImm
  ) where

import Haskell.Word
import Haskell.Machine hiding (EQ)
import qualified Haskell.Assembler as A
import Haskell.Assembler (tryMWordImm, immediateTooBigMsg)

import Control.Applicative hiding (Const(..))
import Control.Monad.Fix

import Data.Singletons.TH
import Data.Promotion.Prelude
import Data.Promotion.Prelude.List

import GHC.Exts (Constraint)

singletons [d|
  data R = R0  | R1  | R2  | R3  | R4  | R5  | R6  | R7
         | R8  | R9  | R10 | R11 | R12 | R13 | R14 | R15
         | R16 | R17 | R18 | R19 | R20 | R21 | R22 | R23
         | R24 | R25 | R26 | R27 | R28 | R29 | R30 | R31
         deriving (Eq, Ord, Enum, Bounded, Read, Show)
{- Template Haskell requires weird indentation
-}|]

type REG r = SR r

toReg :: REG r -> Reg
toReg = reg . toInteger . fromEnum . fromSing

r0  :: REG R0
r1  :: REG R1
r2  :: REG R2
r3  :: REG R3
r4  :: REG R4
r5  :: REG R5
r6  :: REG R6
r7  :: REG R7
r8  :: REG R8
r9  :: REG R9
r10 :: REG R10
r11 :: REG R11
r12 :: REG R12
r13 :: REG R13
r14 :: REG R14
r15 :: REG R15
r16 :: REG R16
r17 :: REG R17
r18 :: REG R18
r19 :: REG R19
r20 :: REG R20
r21 :: REG R21
r22 :: REG R22
r23 :: REG R23
r24 :: REG R24
r25 :: REG R25
r26 :: REG R26
r27 :: REG R27
r28 :: REG R28
r29 :: REG R29
r30 :: REG R30
r31 :: REG R31
( r0,  r1,  r2,  r3,  r4,  r5,  r6,  r7,
  r8,  r9,  r10, r11, r12, r13, r14, r15,
  r16, r17, r18, r19, r20, r21, r22, r23,
  r24, r25, r26, r27, r28, r29, r30, r31) =
  ( SR0,  SR1,  SR2,  SR3,  SR4,  SR5,  SR6,  SR7
  , SR8,  SR9,  SR10, SR11, SR12, SR13, SR14, SR15
  , SR16, SR17, SR18, SR19, SR20, SR21, SR22, SR23
  , SR24, SR25, SR26, SR27, SR28, SR29, SR30, SR31 )

newtype SymAssemblerR (rs :: [R]) a
  = SymAssemblerR { getSymAssemblerR :: A.SymAssembler a }
  deriving (Functor, Applicative, Monad, MonadFix)

runSymAssemblerR :: proxy rs -> SymAssemblerR rs a -> Either String (a,[MWord])
runSymAssemblerR _ = A.runAssembler . getSymAssemblerR

execSymAssemblerR :: proxy rs -> SymAssemblerR rs a -> Either String [MWord]
execSymAssemblerR _ = A.execAssembler . getSymAssemblerR

reserve :: MWord -> SymAssemblerR rs MWord
reserve = SymAssemblerR . A.reserve

here :: SymAssemblerR rs MWord
here = SymAssemblerR A.here

reservedSegment :: SymAssemblerR rs MWord
reservedSegment = SymAssemblerR A.reservedSegment

asmError :: String -> SymAssemblerR rs a
asmError = SymAssemblerR . A.asmError

asmDelayedError :: Maybe String -> SymAssemblerR rs ()
asmDelayedError = SymAssemblerR . A.asmDelayedError

-- Need registerized variants
program :: SymAssemblerR rs a -> SymAssemblerR rs a
program = SymAssemblerR . A.program . getSymAssemblerR

type family Subset (xs :: [a]) (ys :: [a]) :: Constraint where
  Subset '[]       ys = ()
  Subset (x ': xs) ys = (Elem x ys ~ True, Subset xs ys)

type family Disjoint (xs :: [a]) (ys :: [a]) :: Constraint where
  Disjoint '[]       ys = ()
  Disjoint (x ': xs) ys = (Elem x ys ~ False, Disjoint xs ys)

nop     :: SymAssemblerR rs ()
const_  :: Subset '[r] rs => Imm -> REG r -> SymAssemblerR rs ()
mov     :: Subset '[rA,rB] rs => REG rA -> REG rB -> SymAssemblerR rs ()
binop   :: Subset '[rA,rB,rC] rs => Binop -> REG rA -> REG rB -> REG rC -> SymAssemblerR rs ()
load    :: Subset '[rA,rB] rs => REG rA -> REG rB -> SymAssemblerR rs ()
store   :: Subset '[rA,rB] rs => REG rA -> REG rB -> SymAssemblerR rs ()
jump    :: Subset '[r] rs => REG r -> SymAssemblerR rs ()
bnz     :: Subset '[r] rs => REG r -> Imm -> SymAssemblerR rs ()
jal     :: Subset '[r] rs => REG r -> SymAssemblerR rs ()
jumpEpc :: SymAssemblerR rs ()
addRule :: SymAssemblerR rs ()
getTag  :: Subset '[rA,rB] rs => REG rA -> REG rB -> SymAssemblerR rs ()
putTag  :: Subset '[rA,rB,rC] rs => REG rA -> REG rB -> REG rC -> SymAssemblerR rs ()
halt    :: SymAssemblerR rs ()

nop                = SymAssemblerR $ A.nop
const_    i r      = SymAssemblerR $ A.const_    i (toReg r)
mov       rA rB    = SymAssemblerR $ A.mov       (toReg rA) (toReg rB)
binop bop rA rB rC = SymAssemblerR $ A.binop bop (toReg rA) (toReg rB) (toReg rC)
load      rA rB    = SymAssemblerR $ A.load      (toReg rA) (toReg rB)
store     rA rB    = SymAssemblerR $ A.store     (toReg rA) (toReg rB)
jump      r        = SymAssemblerR $ A.jump      (toReg r)
bnz       r i      = SymAssemblerR $ A.bnz       (toReg r) i
jal       r        = SymAssemblerR $ A.jal       (toReg r)
jumpEpc            = SymAssemblerR $ A.jumpEpc
addRule            = SymAssemblerR $ A.addRule
getTag    rA rB    = SymAssemblerR $ A.getTag    (toReg rA) (toReg rB)
putTag    rA rB rC = SymAssemblerR $ A.putTag    (toReg rA) (toReg rB) (toReg rC)
halt               = SymAssemblerR $ A.halt

addrToImm :: MWord -> SymAssemblerR rs Imm
addrToImm = SymAssemblerR . A.addrToImm

addrToImm' :: MWord -> SymAssemblerR rs Imm
addrToImm' = SymAssemblerR . A.addrToImm'

hereImm :: SymAssemblerR rs Imm
hereImm = SymAssemblerR A.hereImm

reserveImm :: MWord -> SymAssemblerR rs Imm
reserveImm = SymAssemblerR . A.reserveImm
