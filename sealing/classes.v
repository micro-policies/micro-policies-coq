
Require Import common.

Section WithClasses.

Context {t : machine_types}.

Class sealing_key := {
  key       : Type
}.

Class sealing_syscall_addrs := {
  mkkey_addr  : word t;
  seal_addr   : word t;
  unseal_addr : word t
}.

(* These should be shared between as many machines as possible *)

Require Import utils.

Class smemory tag := {
  memory    : Type;

  get_mem : memory -> word t -> option (atom (word t) tag);
  upd_mem : memory -> word t -> atom (word t) tag -> option memory;

  mem_axioms : PartMaps.axioms get_mem upd_mem
}.

(* This is basically the same as smemory,
   can't we share one partial map class? *)
Class sregisters tag := {
  registers : Type;

  get_reg : registers -> reg t -> option (atom (word t) tag);
  upd_reg : registers -> reg t -> atom (word t) tag -> option registers;

  reg_axioms : PartMaps.axioms get_reg upd_reg
}.

Class syscall_regs := {
  syscall_ret  : reg t;
  syscall_arg1 : reg t;
  syscall_arg2 : reg t
}.

End WithClasses.
