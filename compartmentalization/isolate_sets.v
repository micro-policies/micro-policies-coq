Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.ssrnat Ssreflect.seq Ssreflect.fintype MathComp.finset MathComp.ssrint.
Require Import CoqUtils.word CoqUtils.partmap.

Require Import lib.utils common.types.
Require Import compartmentalization.ranges.

Set Bullet Behavior "Strict Subproofs".
Import DoNotation.

Generalizable All Variables.

Section WithClasses.

Context  {mt           : machine_types}
         {ops          : machine_ops mt}
         {spec         : machine_ops_spec ops}
         {V            : Type}
         (to_word      : V -> mword mt).

Open Scope word_scope.

Definition isolate_get_range (m : {partmap mword mt -> V}) (p : mword mt) : option {set (mword mt)} :=
  do! low  <- m p;
  do! high <- m (p + 1);
  Some [set i : mword mt in range (to_word low) (to_word high)].

Fixpoint isolate_get_ranges (m : {partmap mword mt -> V})
                            (p : mword mt)
                            (n : nat) : option {set (mword mt)} :=
  match n with
    | O    => Some set0
    | S n' => do! here <- isolate_get_range m p;
              do! rest <- isolate_get_ranges m (p + as_word 2) n';
              Some (here :|: rest)
  end.

Definition isolate_create_set (m : {partmap mword mt -> V})
                              (base : mword mt) : option {set (mword mt)} :=
  do! pairs <- m base;
  isolate_get_ranges m (base + 1) (val (to_word pairs)).

Local Notation "x ?= y" := (x = Some y) (at level 70, no associativity).

End WithClasses.
