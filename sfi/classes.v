Require Import eqtype.
Require Import lib.utils lib.partial_maps lib.ordered common.common.
Set Bullet Behavior "Strict Subproofs".

Section WithClasses.

Generalizable All Variables.

Import PartMaps.

Class abstract_params (t : machine_types) := {
  memory    :  Type;
  mem_class :> partial_map memory (word t) (word t);
  registers :  Type;
  reg_class :> partial_map registers (reg t) (word t)
}.

Class params_spec `(ap : abstract_params t) :=
  { mem_axioms :> PartMaps.axioms (@mem_class t ap)
  ; reg_axioms :> PartMaps.axioms (@reg_class t ap) }.

Class sfi_syscall_addrs (t : machine_types) := {
  isolate_addr              : word t;
  add_to_jump_targets_addr  : word t;
  add_to_shared_memory_addr : word t
}.

End WithClasses.
