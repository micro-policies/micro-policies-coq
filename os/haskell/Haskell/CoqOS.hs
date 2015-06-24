module Haskell.CoqOS where

import Haskell.Machine
import Os (symbolic_os, syscall_addrs)

coqOS :: State
coqOS = fromCoqState symbolic_os

coqOSSyscalls :: SyscallAddresses
coqOSSyscalls = unsafeFromCoqSyscallAddresses syscall_addrs

stepCoqOS' :: Integral i => i -> (i, State)
stepCoqOS' = flip (stepMany' coqOSSyscalls) coqOS

stepCoqOS :: Integral i => i -> Maybe State
stepCoqOS = flip (stepMany coqOSSyscalls) coqOS
