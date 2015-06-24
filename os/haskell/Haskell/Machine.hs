{-# LANGUAGE GeneralizedNewtypeDeriving, TemplateHaskell, PatternSynonyms,
             RecordWildCards, TupleSections, BangPatterns #-}
module Haskell.Machine (
  module Haskell.Machine,
  Coq_binop(..), Coq_where_from(..)
  ) where

import qualified Finset
import qualified Symbolic
import qualified Symbolic0

import Int_32 hiding (unsafeCoerce)
import Common hiding (unsafeCoerce)
import Types  hiding (ra)
import qualified Types

import Os (step_os)

import Haskell.RetypeData.TH
import Haskell.Types
import Haskell.Word

import Language.Haskell.TH
import Control.Applicative
import Data.Monoid
import Data.Maybe
import Data.List
import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M

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

retypeData ''Coq_instr "Instr" Nothing
           [(''Coq_binop, ''Binop), (''Coq_reg, ''Reg), (''Coq_imm, ''Imm)]
           id
           [''Eq, ''Ord, ''Show]
           "coqInstr" "unsafeFromCoqInstr"

type WhereFrom = Coq_where_from
type CID       = MWord
type CIDSet    = Set CID

retypeData ''Symbolic0.Sym__Coq_pc_tag "PCTag" Nothing
           [(''Coq_mword, ''CID), (''Coq_where_from, ''WhereFrom)]
           (fromMaybe <*> stripPrefix "Sym__")
           [''Eq, ''Ord, ''Show]
           "coqPCTag" "unsafeFromCoqPCTag"

-- This should be `unsafeCoerce`ible with ()
data RegTag = REG deriving (Eq, Ord, Bounded, Enum, Show, Read)

retypeData ''Symbolic0.Sym__Coq_data_tag "DataTag" Nothing
           [(''Coq_mword, ''CID), (''Finset.Coq_set_of, ''CIDSet)]
           (fromMaybe <*> stripPrefix "Sym__")
           [''Eq, ''Ord, ''Show]
           "coqDataTag" "unsafeFromCoqDataTag"

coqRegTag :: RegTag -> ()
coqRegTag = unsafeCoerce

-- Not really unsafe...
unsafeFromCoqRegTag :: () -> RegTag
unsafeFromCoqRegTag = unsafeCoerce

instance Monoid RegTag where
  mempty        = REG
  _ `mappend` _ = REG
  mconcat _     = REG

retypeData ''Symbolic0.Sym__Coq_compartmentalization_internal "Internal"
           (Just ["nextId", "isolateTag", "addToJumpTargetsTag", "addToStoreTargetsTag"])
           [(''Coq_mword, ''MWord), (''Symbolic0.Sym__Coq_data_tag, ''DataTag)]
           (fromMaybe <*> stripPrefix "Sym__")
           [''Eq, ''Ord, ''Show]
           "coqInternal" "unsafeFromCoqInternal"

mt :: Coq_machine_types
mt = concrete_int_32_mt

ops :: Coq_machine_ops
ops = concrete_int_32_ops

sp :: Symbolic.Symbolic__Coq_params
sp = Symbolic0._Sym__sym_compartmentalization mt

ra :: Reg
ra = Reg . unsafeFromCoqWord $ Types.ra mt ops

type CoqState = Symbolic.Symbolic__Coq_state
data State = State { mem      :: Map MWord (Atom MWord DataTag)
                   , regs     :: Map Reg   (Atom MWord RegTag)
                   , pc       :: Atom MWord PCTag
                   , internal :: Internal }
           deriving (Eq, Ord, Show)
  -- We can safely use 'M.toAscList' and 'M.fromAscList' because Haskell's
  -- 'MWords' are ordered the same way as the underlying Coq words are in Coq.

coqState :: State -> CoqState
coqState State{..} = Symbolic.Symbolic__State (unsafeCoerce $ M.toAscList mem)
                                              (unsafeCoerce $ M.toAscList regs)
                                              (unsafeCoerce pc)
                                              (unsafeCoerce internal)

fromCoqState :: CoqState -> State
fromCoqState (Symbolic.Symbolic__State mem regs pc internal) =
  State { mem      = M.fromAscList $ unsafeCoerce mem
        , regs     = M.fromAscList $ unsafeCoerce regs
        , pc       = unsafeCoerce pc
        , internal = unsafeCoerce internal }

coqStateMem :: CoqState -> PartMap MWord (Atom MWord DataTag)
coqStateMem = unsafeCoerce $ Symbolic._Symbolic__mem mt sp

coqStateRegs :: CoqState -> PartMap Reg (Atom MWord RegTag)
coqStateRegs = unsafeCoerce $ Symbolic._Symbolic__regs mt sp

coqStatePC :: CoqState -> Atom MWord PCTag
coqStatePC = unsafeCoerce $ Symbolic._Symbolic__pc mt sp

coqStateInternal :: CoqState -> Internal
coqStateInternal = unsafeCoerce $ Symbolic._Symbolic__internal mt sp

encodeInstr :: Instr -> MWord
encodeInstr = MWord . unsafeFromCoqWord . encode_instr mt ops . coqInstr

decodeInstr :: MWord -> Maybe Instr
decodeInstr = fmap unsafeFromCoqInstr . decode_instr mt ops . coqWord . mwordWord

instrAt :: State -> MWord -> Maybe Instr
instrAt s n = decodeInstr . val =<< M.lookup n (mem s)

initialState :: [MWord] -> [Reg] -> State
initialState memData allRegs =
  let syscallCids    = S.fromList [0..2]
      userCid        = 3
      userTag        = DATA userCid syscallCids syscallCids
      syscallTag cid = DATA cid (S.singleton userCid) (S.singleton userCid)
  in State { mem      = M.fromAscList . zip [0..] $ map (:@ userTag) memData
           , regs     = M.fromAscList $ map (,0:@REG) allRegs
           , pc       = 0 :@ PC INTERNAL userCid
           , internal = Internal { nextId               = userCid + 1
                                 , isolateTag           = syscallTag 0
                                 , addToJumpTargetsTag  = syscallTag 1
                                 , addToStoreTargetsTag = syscallTag 2 } }

-- TODO I really ought to think about memoization for the step functions

coqStep :: CoqState -> Maybe CoqState
coqStep = step_os
  -- FIXME this is WRONG, it needs to deal with the syscall addresses

coqStepMany' :: Integral i => i -> CoqState -> (i, CoqState)
coqStepMany' = go 0 where
  go !k n s | n <= 0    = (k,s)
            | otherwise = maybe (k,s) (go (k+1) (n-1)) $ coqStep s

coqStepMany :: Integral i => i -> CoqState -> Maybe CoqState
coqStepMany n s | n <= 0    = return s
                | otherwise = coqStepMany (n-1) =<< coqStep s

step :: State -> Maybe State
step = fmap fromCoqState . coqStep . coqState

stepMany' :: Integral i => i -> State -> (i, State)
stepMany' i = fmap fromCoqState . coqStepMany' i . coqState

stepMany :: Integral i => i -> State -> Maybe State
stepMany i = fmap fromCoqState . coqStepMany i . coqState
