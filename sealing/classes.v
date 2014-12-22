Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Require Import common.common.

Section WithClasses.

Context {t : machine_types}.

Class sealing_syscall_addrs := {
  mkkey_addr  : mword t;
  seal_addr   : mword t;
  unseal_addr : mword t
}.

End WithClasses.
