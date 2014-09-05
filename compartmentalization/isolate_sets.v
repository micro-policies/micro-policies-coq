Require Import List ZArith Arith Sorted Bool.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype finset.

Require Import lib.Integers lib.utils lib.partial_maps common.common.
Require Import compartmentalization.ranges.

Set Bullet Behavior "Strict Subproofs".
Import DoNotation.
Import PartMaps.

Generalizable All Variables.

Section WithClasses.

Context  {t            : machine_types}
         {ops          : machine_ops t}
         {spec         : machine_ops_spec ops}
        `{pm           : partial_map Map (word t)}
         {V            : Type}
         (to_word      : V -> word t).

Open Scope word_scope.

Definition isolate_get_range (M : Map V) (p : word t) : option {set (word t)} :=
  do! low  <- get M p;
  do! high <- get M (p + 1);
  Some [set i : word t in range (to_word low) (to_word high)].

Fixpoint isolate_get_ranges (M : Map V)
                            (p : word t)
                            (n : nat) : option {set (word t)} :=
  match n with
    | O    => Some set0
    | S n' => do! here <- isolate_get_range M p;
              do! rest <- isolate_get_ranges M (p + 2) n';
              Some (here :|: rest)
  end.

Definition isolate_create_set (M : Map V)
                              (base : word t) : option {set (word t)} :=
  do! pairs <- get M base;
  isolate_get_ranges M (base + 1) (Z.to_nat (Word.signed (to_word pairs))).

Local Notation "x ?= y" := (x = Some y) (at level 70, no associativity).

Local Ltac isolate_fn_is_set :=
  let H := fresh in
  intros until 0; intros H;
  let unfix gen f n := first [ gen; induction n; intros; simpl in H;
                               [solve [inversion H; auto]|]
                             | unfold f in H; simpl in H ] in
  match type of H with
      | ?f ?a ?b ?c ?n ?= ?X => unfix ltac:(gdep c; gdep b; gdep a; gdep X) f n
      | ?f ?a ?b ?n    ?= ?X => unfix ltac:(gdep b; gdep a; gdep X)         f n
      | ?f ?a ?n       ?= ?X => unfix ltac:(gdep a; gdep X)                 f n
      | ?f ?n          ?= ?X => unfix ltac:(gdep X)                         f n
  end ;
  repeat match type of H with (do! _ <- ?x; _) ?= _ =>
    destruct x eqn:?; simpl in H; [|discriminate H]
  end;
  inversion H; subst;
  eauto 4.

End WithClasses.
