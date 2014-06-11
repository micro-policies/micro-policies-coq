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

(* These should be shared between as many machines as possible *)

Require Import utils.

Class partial_map map key val := {
  get : map -> key -> option val;
  upd : map -> key -> val -> option map
}.

Class partial_map_spec map key val (pm : partial_map map key val) := {
  mem_axioms : PartMaps.axioms get upd
}.

Class syscall_regs := {
  syscall_ret  : reg t;
  syscall_arg1 : reg t;
  syscall_arg2 : reg t
}.

End WithClasses.
