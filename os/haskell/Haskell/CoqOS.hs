module Haskell.CoqOS where

import Haskell.Machine
import Os (symbolic_os)

coqOS :: State
coqOS = fromCoqState symbolic_os

stepCoqOS' :: Integral i => i -> (i, State)
stepCoqOS' = flip stepMany' coqOS

stepCoqOS :: Integral i => i -> Maybe State
stepCoqOS = flip stepMany coqOS
