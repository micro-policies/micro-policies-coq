Require Import common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section classes.

Context `{t : machine_types}.

Class memory_syscall_addrs := {
  malloc_addr : word t;
  free_addr : word t
}.

End classes.