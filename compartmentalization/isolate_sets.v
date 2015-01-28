Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype finset ssrint.
Require Import word partmap.

Require Import lib.utils common.types.
Require Import compartmentalization.ranges.

Set Bullet Behavior "Strict Subproofs".
Import DoNotation.

Generalizable All Variables.

Section WithClasses.

Context  {t            : machine_types}
         {ops          : machine_ops t}
         {spec         : machine_ops_spec ops}
         {V            : Type}
         (to_word      : V -> mword t).

Open Scope word_scope.

Definition isolate_get_range (m : {partmap mword t -> V}) (p : mword t) : option {set (mword t)} :=
  do! low  <- m p;
  do! high <- m (p + 1);
  Some [set i : mword t in range (to_word low) (to_word high)].

Fixpoint isolate_get_ranges (m : {partmap mword t -> V})
                            (p : mword t)
                            (n : nat) : option {set (mword t)} :=
  match n with
    | O    => Some set0
    | S n' => do! here <- isolate_get_range m p;
              do! rest <- isolate_get_ranges m (p + as_word 2) n';
              Some (here :|: rest)
  end.

Definition isolate_create_set (m : {partmap mword t -> V})
                              (base : mword t) : option {set (mword t)} :=
  do! pairs <- m base;
  isolate_get_ranges m (base + 1) (eqtype.val (to_word pairs)).

Local Notation "x ?= y" := (x = Some y) (at level 70, no associativity).

End WithClasses.
