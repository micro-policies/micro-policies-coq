Require Import Coq.Classes.SetoidDec.
Require Import common.

Section WithClasses.

Context {t : machine_types}.

Class sealing_syscall_addrs := {
  mkkey_addr  : word t;
  seal_addr   : word t;
  unseal_addr : word t
}.

End WithClasses.
