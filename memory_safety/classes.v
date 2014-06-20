Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Require Import common.common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section classes.

Context `{t : machine_types}.

Class memory_syscall_addrs := {
  malloc_addr : word t;
  free_addr : word t;
  size_addr : word t;
  base_addr : word t;
  eq_addr : word t
}.

End classes.