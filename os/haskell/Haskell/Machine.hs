{-# LANGUAGE GeneralizedNewtypeDeriving, TemplateHaskell, PatternSynonyms #-}
module Haskell.Machine where

import qualified Finset
import qualified Symbolic
import qualified Symbolic0

import Int_32 hiding (unsafeCoerce)
import Common hiding (unsafeCoerce)
import Types

import Haskell.TH
import Haskell.Util
import Haskell.Types
import Haskell.Word

import Language.Haskell.TH
import Control.Applicative
import Data.Monoid
import Data.Maybe
import Data.List
import Data.Coerce
import Data.Set (Set)
import qualified Data.Set as S

type MWord' = Word $(litT . numTyLit $ word_size      concrete_int_32_mt)
type Reg'   = Word $(litT . numTyLit $ reg_field_size concrete_int_32_mt)
type Imm'   = Word $(litT . numTyLit $ imm_size       concrete_int_32_mt)

newtype MWord = MWord { mwordWord :: MWord' }
              deriving (Eq, Ord, Bounded, Enum, Num, Real, Integral)
newtype Reg   = Reg { regWord :: Reg' }
              deriving (Eq, Ord, Bounded, Enum, Num, Real, Integral)
newtype Imm   = Imm { immWord :: Imm' }
              deriving (Eq, Ord, Bounded, Enum, Num, Real, Integral)

instance Show MWord where
  showsPrec p = showsPrec p . mwordWord

instance Show Reg where
  showsPrec p = (("%r" ++) .) . showsPrec p . regWord

instance Show Imm where
  showsPrec p = (('#' :) .) . showsPrec p . immWord

mword :: Integer -> MWord
mword = fromInteger

reg :: Integer -> Reg
reg = fromInteger

imm :: Integer -> Imm
imm = fromInteger

type Binop = Coq_binop

retypeData ''Coq_instr "Instr"
           [(''Coq_binop, ''Binop), (''Coq_reg, ''Reg), (''Coq_imm, ''Imm)]
           id
           [''Eq, ''Ord, ''Show]

coqInstr :: Instr -> Coq_instr
coqInstr = unsafeCoerce

fromCoqInstr :: Coq_instr -> Instr
fromCoqInstr = unsafeCoerce

type Internal = Symbolic0.Sym__Coq_compartmentalization_internal

type State = Symbolic.Symbolic__Coq_state

type WhereFrom = Coq_where_from
type CID       = MWord
type CIDSet    = Set CID

retypeData ''Symbolic0.Sym__Coq_pc_tag "PCTag"
           [(''Coq_mword, ''CID)]
           (fromMaybe <*> stripPrefix "Sym__")
           [''Eq, ''Ord, ''Show]

-- This should be `unsafeCoerce`ible with ()
data RegTag = REG deriving (Eq, Ord, Bounded, Enum, Show, Read)

retypeData ''Symbolic0.Sym__Coq_data_tag "DataTag"
           [(''Coq_mword, ''CID), (''Finset.Coq_set_of, ''CIDSet)]
           (fromMaybe <*> stripPrefix "Sym__")
           [''Eq, ''Ord, ''Show]

instance Monoid RegTag where
  mempty        = REG
  _ `mappend` _ = REG
  mconcat _     = REG

mt :: Coq_machine_types
mt = concrete_int_32_mt

ops :: Coq_machine_ops
ops = concrete_int_32_ops

sp :: Symbolic.Symbolic__Coq_params
sp = Symbolic0._Sym__sym_compartmentalization Int_32.concrete_int_32_mt

mem :: State -> PartMap MWord (Atom MWord DataTag)
mem = unsafeCoerce $ Symbolic._Symbolic__mem mt sp

regs :: State -> PartMap Reg (Atom MWord RegTag)
regs = unsafeCoerce $ Symbolic._Symbolic__regs mt sp

pc :: State -> Atom MWord PCTag
pc = unsafeCoerce $ Symbolic._Symbolic__pc mt sp

internal :: State -> Internal
internal = unsafeCoerce $ Symbolic._Symbolic__internal mt sp

decodeInstr :: MWord -> Maybe Instr
decodeInstr = fmap fromCoqInstr . decode_instr mt ops . coqWord . mwordWord

instrAt :: Integral i => State -> i -> Maybe Instr
instrAt s n = decodeInstr . val . snd =<< (mem s ?? n)
