From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq fintype finfun.
From CoqUtils Require Import hseq ord fset partmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Dev.

Parameter Σ : finType.

Record rifAutomaton := RifAutomaton {
  rif_states : nat;
  rif_trans : {ffun 'I_rif_states * Σ -> 'I_rif_states};
  rif_prins : {ffun 'I_rif_states -> {fset nat}}
}.

Definition tag_of_rifAutomaton r : { n : nat &
                                     ({ffun 'I_n * Σ -> 'I_n} *
                                      {ffun 'I_n -> {fset nat}})%type } :=
  @Tagged nat (rif_states r) _ (rif_trans r, rif_prins r).

Definition rifAutomaton_of_tag (r : { n : nat &
                                      ({ffun 'I_n * Σ -> 'I_n} *
                                       {ffun 'I_n -> {fset nat}})%type }) : rifAutomaton :=
  RifAutomaton (tagged r).1 (tagged r).2.

Lemma tag_of_rifAutomatonK : cancel tag_of_rifAutomaton rifAutomaton_of_tag.
Proof. by case. Qed.

Definition rifAutomaton_eqMixin := CanEqMixin tag_of_rifAutomatonK.
Canonical rifAutomaton_eqType := EqType rifAutomaton rifAutomaton_eqMixin.

Record rifLabel := RifLabel {
  rif_rules :> rifAutomaton;
  rif_state : 'I_(rif_states rif_rules)
}.

Definition rif_step (l : rifLabel) (F : Σ) : rifLabel :=
  RifLabel (rif_trans l (rif_state l, F)).

Definition rif_steps (l : rifLabel) (Fs : seq Σ) : rifLabel :=
  foldl rif_step l Fs.

(*
Definition rif_leq (l1 l2 : rifLabel) : Prop :=
  forall Fs, fsubset (rif_prins (rif_rules l1) (rif_state (rif_steps l1 Fs)))
                     (rif_prins l2 (rif_state (rif_steps l2 Fs))).
*)

End Dev.
