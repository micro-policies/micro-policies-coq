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

Class smemory dom := {
  memory    : Type;

  get_mem : memory -> word t -> option dom;
  upd_mem : memory -> word t -> dom -> option memory;

  (* could factor this out? *)
  mem_axioms : PartMaps.axioms get_mem upd_mem
}.

(* This is basically the same as smemory,
   can't we share one partial map class? *)
Class sregisters dom := {
  registers : Type;

  get_reg : registers -> reg t -> option dom;
  upd_reg : registers -> reg t -> dom -> option registers;

  (* could factor this out? *)
  reg_axioms : PartMaps.axioms get_reg upd_reg
}.

Class syscall_regs := {
  syscall_ret  : reg t;
  syscall_arg1 : reg t;
  syscall_arg2 : reg t
}.

End WithClasses.
