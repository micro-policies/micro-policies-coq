{-# LANGUAGE TypeSynonymInstances, PatternSynonyms #-}
module Haskell.Types where

import Types

import Control.Applicative
import Data.Bifunctor

type PartMap  k v = [(k,v)]
type PartMap'   v = PartMap () v

type Atom = Coq_atom
pattern v :@ t = Atom v t
infix 9 :@

val :: Atom v t -> v
val = vala

tag :: Atom v t -> t
tag = taga

instance Bifunctor Atom where
  bimap vf tf (v :@ t) = vf v :@ tf t
