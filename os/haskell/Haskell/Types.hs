module Haskell.Types (module Haskell.Types, Atom(..)) where

import Types

type PartMap  k v = [(k,v)]
type PartMap'   v = PartMap () v

-- These could also be lenses...

val :: Atom v t -> v
val = vala

tag :: Atom v t -> t
tag = taga
