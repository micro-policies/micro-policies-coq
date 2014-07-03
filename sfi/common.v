Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import lib.utils lib.partial_maps lib.ordered common.common.
Set Bullet Behavior "Strict Subproofs".

Generalizable All Variables.

Import PartMaps.

Class abstract_params (t : machine_types) := {
  word_map       :  Type -> Type;
  word_map_class :> partial_map word_map (word t);
  reg_map        :  Type -> Type;
  reg_map_class  :> partial_map reg_map (reg t)
}.

Definition memory (t : machine_types) {ap : abstract_params t} := word_map (word t).
Definition registers (t : machine_types) {ap : abstract_params t} := reg_map (word t).

Class params_spec `(ap : abstract_params t) :=
  { word_map_axioms :> PartMaps.axioms (@word_map_class t ap)
  ; reg_map_axioms :> PartMaps.axioms (@reg_map_class t ap) }.

Class sfi_syscall_addrs (t : machine_types) := {
  isolate_addr              : word t;
  add_to_jump_targets_addr  : word t;
  add_to_shared_memory_addr : word t
}.

Inductive where_from :=
| INTERNAL : where_from
| JUMPED   : where_from.

Definition where_from_eq (S1 S2 : where_from) : bool :=
  match S1, S2 with
    | INTERNAL , INTERNAL | JUMPED , JUMPED => true
    | _ , _                                 => false
  end.

Lemma where_from_eqP : Equality.axiom where_from_eq.
Proof. by move=> [|] [|] /=; apply: (iffP idP). Qed.

Definition where_from_eqMixin := EqMixin where_from_eqP.
Canonical where_from_eqType := Eval hnf in EqType where_from where_from_eqMixin.
