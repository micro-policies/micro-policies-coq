Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Require Import common.common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section classes.

Context `{t : machine_types}.

Class memory_syscall_addrs := {
  malloc_addr : mword t;
  free_addr : mword t;
  size_addr : mword t;
  base_addr : mword t;
  eq_addr : mword t
}.

End classes.
