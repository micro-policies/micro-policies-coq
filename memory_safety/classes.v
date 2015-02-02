Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.ssrnat.
Require Import common.types.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Class memory_syscall_addrs mt := {
  malloc_addr : mword mt;
  free_addr : mword mt;
  size_addr : mword mt;
  base_addr : mword mt;
  eq_addr : mword mt
}.
