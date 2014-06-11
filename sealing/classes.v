Require Import Coq.Classes.SetoidDec.
Require Import common.

Section WithClasses.

Context {t : machine_types}.

Class sealing_key := {
  key       : Type
}.

Context {sk : sealing_key}.

Class sealing_key_ops := {
  max_key : key;
  inc_key : key -> key;
  eq_key :> EqDec (eq_setoid key)
}.

Class sealing_syscall_addrs := {
  mkkey_addr  : word t;
  seal_addr   : word t;
  unseal_addr : word t
}.

End WithClasses.
