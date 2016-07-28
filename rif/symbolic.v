From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq fintype finfun.
From CoqUtils Require Import hseq ord fset partmap.
From MicroPolicies Require Import common.types symbolic.symbolic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Ord.

Variables m n : nat.

Lemma ord_pair_proof : #|{:'I_m * 'I_n}| = (m * n)%N.
Proof. by rewrite card_prod !card_ord. Qed.

Definition ord_pair (i : 'I_m) (j : 'I_n) :=
  cast_ord ord_pair_proof (enum_rank (i, j)).

Definition ord_unpair (i : 'I_(m * n)) : 'I_m * 'I_n :=
  enum_val (cast_ord (esym ord_pair_proof) i).

Lemma ord_pairK i j : ord_unpair (ord_pair i j) = (i, j).
Proof. by rewrite /ord_pair /ord_unpair cast_ordK enum_rankK. Qed.

End Ord.

Section Dev.

Parameter Σ : finType.

Local Open Scope fset_scope.

Record rifAutomaton := RifAutomaton {
  rif_states : nat;
  rif_trans : {ffun 'I_rif_states * Σ -> 'I_rif_states};
  rif_prins : {ffun 'I_rif_states -> {fset nat}}
}.

Implicit Types r : rifAutomaton.

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

Definition ra_join r1 r2 :=
  @RifAutomaton
    (rif_states r1 * rif_states r2)
    [ffun p =>
       let ix := ord_unpair p.1 in
       ord_pair (rif_trans r1 (ix.1, p.2)) (rif_trans r2 (ix.2, p.2))]
    [ffun ix =>
       let ix := ord_unpair ix in
       rif_prins r1 ix.1 :|: rif_prins r2 ix.2].

Definition rif_run r (i : 'I_(rif_states r)) (Fs : seq Σ) :=
  foldl (fun i F => rif_trans r (i, F)) i Fs.

Lemma rif_run_join r1 r2 (i1 : 'I_(rif_states r1)) (i2 : 'I_(rif_states r2)) (Fs : seq Σ) :
  @rif_run (ra_join r1 r2) (ord_pair i1 i2) Fs
  = ord_pair (rif_run i1 Fs) (rif_run i2 Fs).
Proof.
elim: Fs i1 i2 => [|F Fs IH] i1 i2 //=.
by rewrite ffunE /= ord_pairK /= IH.
Qed.

Lemma ra_joinPl r1 r2 i1 i2 Fs :
  fsubset (rif_prins r1 (rif_run i1 Fs))
          (rif_prins (ra_join r1 r2)
                     (@rif_run (ra_join r1 r2) (ord_pair i1 i2) Fs)).
Proof.
by rewrite rif_run_join /= ffunE ord_pairK /= fsubsetUl.
Qed.

Lemma ra_joinPr r1 r2 i1 i2 Fs :
  fsubset (rif_prins r2 (rif_run i2 Fs))
          (rif_prins (ra_join r1 r2)
                     (@rif_run (ra_join r1 r2) (ord_pair i1 i2) Fs)).
Proof.
by rewrite rif_run_join /= ffunE ord_pairK /= fsubsetUr.
Qed.

Lemma ra_join_min r1 r2 r3 i1 i2 i3 Fs :
  fsubset (rif_prins (ra_join r1 r2)
                     (@rif_run (ra_join r1 r2) (ord_pair i1 i2) Fs))
          (rif_prins r3 (rif_run i3 Fs))
  = fsubset (rif_prins r1 (rif_run i1 Fs))
            (rif_prins r3 (rif_run i3 Fs)) &&
    fsubset (rif_prins r2 (rif_run i2 Fs))
            (rif_prins r3 (rif_run i3 Fs)).
Proof.
by rewrite rif_run_join /= ffunE ord_pairK fsubUset.
Qed.

Record rifLabel := RifLabel {
  rif_rules :> rifAutomaton;
  rif_state : 'I_(rif_states rif_rules)
}.

Implicit Types l : rifLabel.

Definition rl_leq l1 l2 : Prop :=
  forall Fs, fsubset (rif_prins _ (rif_run (rif_state l1) Fs))
                     (rif_prins _ (rif_run (rif_state l2) Fs)).

Axiom rl_leqb : rel rifLabel.
Axiom rl_leqbP : forall l1 l2, reflect (rl_leq l1 l2) (rl_leqb l1 l2).

Definition rl_join l1 l2 :=
  @RifLabel (ra_join l1 l2) (ord_pair (rif_state l1) (rif_state l2)).

Lemma rl_joinPl l1 l2 : rl_leqb l1 (rl_join l1 l2).
Proof. by apply/rl_leqbP=> Fs; apply/ra_joinPl. Qed.

Lemma rl_joinPr l1 l2 : rl_leqb l2 (rl_join l1 l2).
Proof. by apply/rl_leqbP=> Fs; apply/ra_joinPr. Qed.

Lemma rl_join_min l1 l2 l3 :
  rl_leqb (rl_join l1 l2) l3 =
  rl_leqb l1 l3 && rl_leqb l2 l3.
Proof.
apply/rl_leqbP/andP; rewrite /rl_leq.
  move=> H; split; apply/rl_leqbP; rewrite /rl_leq=> Fs; move/(_ Fs) in H.
    exact: (fsubset_trans (ra_joinPl (rif_state l1) (rif_state l2) Fs)).
  exact: (fsubset_trans (ra_joinPr (rif_state l1) (rif_state l2) Fs)).
case=> /rl_leqbP H1 /rl_leqbP H2 Fs; move/(_ Fs) in H1; move/(_ Fs) in H2.
by rewrite /rl_join (lock rif_prins) /= -lock ra_join_min H1.
Qed.

End Dev.
