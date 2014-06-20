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
  sizeof_addr : word t;
  basep_addr : word t;
  offp_addr : word t;
  eqp_addr : word t
}.

End classes.