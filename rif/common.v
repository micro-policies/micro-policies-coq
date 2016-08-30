From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq fintype finfun.
From CoqUtils Require Import hseq ord fset partmap word.
From MicroPolicies Require Import lib.utils common.types.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Ord.

(* Basic lemmas about pairing ordinals *)

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

Section Common.

Local Open Scope fset_scope.

(** The [readers] type encodes who is allowed to observe a piece of
    data. [Anybody] means that there are no restrictions, while
    [Readers r] means that only principals in the finite set [r] are
    allowed to see the data. *)

CoInductive readers :=
| Readers of {fset nat}
| Anybody.

Implicit Types rs : readers.

Definition option_of_readers rs :=
  if rs is Readers rs then Some rs else None.

Definition readers_of_option o :=
  if o is Some rs then Readers rs else Anybody.

Lemma option_of_readersK : cancel option_of_readers readers_of_option.
Proof. by case. Qed.

Definition readers_eqMixin := CanEqMixin option_of_readersK.
Canonical readers_eqType := Eval hnf in EqType readers readers_eqMixin.

(** We order readers by restrictiveness; the higher a set, the more
    restrictions it imposes. *)

Definition readers_leq rs1 rs2 :=
  match rs1, rs2 with
  | Anybody, _ => true
  | Readers rs1, Readers rs2 => fsubset rs1 rs2
  | _, _ => false
  end.

Lemma readers_leq_refl : reflexive readers_leq.
Proof. case=> //= rs; by rewrite fsubsetxx. Qed.

Lemma readers_leq_trans : transitive readers_leq.
Proof.
move=> rs2 [rs1|] //=; case: rs2=> //= rs2 [rs3|] //=.
exact: fsubset_trans.
Qed.

Lemma readers_leq_antisym : antisymmetric readers_leq.
Proof.
by case=> [rs1|] [rs2|] //=; rewrite -eqEfsubset => /eqP ->.
Qed.

Infix "⊑ᵣ" := readers_leq (at level 50).

Definition readers_join rs1 rs2 :=
  match rs1, rs2 with
  | Anybody, rs | rs, Anybody => rs
  | Readers rs1, Readers rs2 => Readers (rs1 :|: rs2)
  end.

Infix "⊔ᵣ" := readers_join (at level 40, left associativity).

Lemma readers_joinC : commutative readers_join.
Proof. by case=> [rs1|] [rs2|] //=; rewrite fsetUC. Qed.

Lemma readers_joinL rs1 rs2 : rs1 ⊑ᵣ rs1 ⊔ᵣ rs2.
Proof.
by case: rs1 rs2 => //= rs1 [rs2|]; [rewrite fsubsetUl|rewrite fsubsetxx].
Qed.

Lemma readers_joinR rs1 rs2 : rs2 ⊑ᵣ rs1 ⊔ᵣ rs2.
Proof. by rewrite readers_joinC readers_joinL. Qed.

Lemma readers_join_min rs1 rs2 rs3 :
  rs1 ⊔ᵣ rs2 ⊑ᵣ rs3 = (rs1 ⊑ᵣ rs3) && (rs2 ⊑ᵣ rs3).
Proof.
case: rs1 rs2 rs3=> //= rs1 [rs2|] [rs3|] //=; last by rewrite andbT.
by rewrite fsubUset.
Qed.

(** A RIF automaton describes which principals are allowed to read a
    value after a sequence of operations. These operations are given
    in the type [Σ], which forms the alphabet of the automaton. Each
    state of the automaton describes who is allowed to read a value at
    a particular moment. *)

Variable Σ : finType.

Record rifAutomaton := RifAutomaton {

  (* The number of states of the automaton. *)
  rif_states : nat;

  (* The transition function. *)
  rif_trans : {ffun 'I_rif_states * Σ -> 'I_rif_states};

  (* The interpretation function, which lists who is allowed to read a
     value on each state. *)
  rif_readers : {ffun 'I_rif_states -> readers}

}.

Implicit Types r : rifAutomaton.

Definition tag_of_rifAutomaton r : { n : nat &
                                     ({ffun 'I_n * Σ -> 'I_n} *
                                      {ffun 'I_n -> readers})%type } :=
  @Tagged nat (rif_states r) _ (rif_trans r, rif_readers r).

Definition rifAutomaton_of_tag (r : { n : nat &
                                      ({ffun 'I_n * Σ -> 'I_n} *
                                       {ffun 'I_n -> readers})%type }) : rifAutomaton :=
  RifAutomaton (tagged r).1 (tagged r).2.

Lemma tag_of_rifAutomatonK : cancel tag_of_rifAutomaton rifAutomaton_of_tag.
Proof. by case. Qed.

Definition rifAutomaton_eqMixin := CanEqMixin tag_of_rifAutomatonK.
Canonical rifAutomaton_eqType := EqType rifAutomaton rifAutomaton_eqMixin.

(** We order RIF automata by how restrictive they are: if [r1] always
    allows more readers than [r2] for any sequence of operations, then
    [r1] is below [r2]. (Note that we just give the join operation of
    this poset for now.) *)

Definition ra_bot :=
  @RifAutomaton 1 [ffun _ => Sub 0 erefl] [ffun _ => Anybody].

Notation "⊥ₐ" := ra_bot.

Definition ra_join r1 r2 :=
  @RifAutomaton
    (rif_states r1 * rif_states r2)
    [ffun p =>
       let ix := ord_unpair p.1 in
       ord_pair (rif_trans r1 (ix.1, p.2)) (rif_trans r2 (ix.2, p.2))]
    [ffun ix =>
       let ix := ord_unpair ix in
       rif_readers r1 ix.1 ⊔ᵣ rif_readers r2 ix.2].

Infix "⊔ₐ" := ra_join (at level 40, left associativity).

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
  rif_readers r1 (rif_run i1 Fs) ⊑ᵣ
  rif_readers (r1 ⊔ₐ r2) (@rif_run (r1 ⊔ₐ r2) (ord_pair i1 i2) Fs).
Proof.
by rewrite rif_run_join /= ffunE ord_pairK /= readers_joinL.
Qed.

Lemma ra_joinPr r1 r2 i1 i2 Fs :
  rif_readers r2 (rif_run i2 Fs) ⊑ᵣ
  rif_readers (r1 ⊔ₐ r2) (@rif_run (r1 ⊔ₐ r2) (ord_pair i1 i2) Fs).
Proof.
by rewrite rif_run_join /= ffunE ord_pairK /= readers_joinR.
Qed.

Lemma ra_join_min r1 r2 r3 i1 i2 i3 Fs :
  rif_readers (r1 ⊔ₐ r2) (@rif_run (r1 ⊔ₐ r2) (ord_pair i1 i2) Fs) ⊑ᵣ
  rif_readers r3 (rif_run i3 Fs)
  = (rif_readers r1 (rif_run i1 Fs) ⊑ᵣ rif_readers r3 (rif_run i3 Fs)) &&
    (rif_readers r2 (rif_run i2 Fs) ⊑ᵣ rif_readers r3 (rif_run i3 Fs)).
Proof.
by rewrite rif_run_join /= ffunE ord_pairK readers_join_min.
Qed.

(** A RIF label packs an automaton with a current state. We lift the
    order relation on RIF automata to labels. *)

Record rifLabel := RifLabel {
  rif_rules :> rifAutomaton;
  rif_state : 'I_(rif_states rif_rules)
}.

Definition rl_bot :=
  @RifLabel ra_bot (@Ordinal 1 0 erefl).

Notation "⊥ₗ" := rl_bot.

Implicit Types l : rifLabel.

Definition tag_of_rifLabel l :=
  Tagged (fun ra => 'I_(rif_states ra)) (rif_state l).

Definition rifLabel_of_tag (x : {ra : rifAutomaton & 'I_(rif_states ra)}) :=
  RifLabel (tagged x).

Lemma tag_of_rifLabelK : cancel tag_of_rifLabel rifLabel_of_tag.
Proof. by case. Qed.

Definition rifLabel_eqMixin := CanEqMixin tag_of_rifLabelK.
Canonical rifLabel_eqType := EqType rifLabel rifLabel_eqMixin.

Definition rl_leq l1 l2 : Prop :=
  forall Fs, rif_readers _ (rif_run (rif_state l1) Fs) ⊑ᵣ
             rif_readers _ (rif_run (rif_state l2) Fs).

Axiom rl_leqb : rel rifLabel.
Axiom rl_leqbP : forall l1 l2, reflect (rl_leq l1 l2) (rl_leqb l1 l2).

Definition rl_join l1 l2 :=
  @RifLabel (ra_join l1 l2) (ord_pair (rif_state l1) (rif_state l2)).

Infix "⊑ₗ" := rl_leqb (at level 50).
Infix "⊔ₗ" := rl_join (at level 40, left associativity).

Lemma rl_joinPl l1 l2 : l1 ⊑ₗ l1 ⊔ₗ l2.
Proof. by apply/rl_leqbP=> Fs; apply/ra_joinPl. Qed.

Lemma rl_joinPr l1 l2 : l2 ⊑ₗ l1 ⊔ₗ l2.
Proof. by apply/rl_leqbP=> Fs; apply/ra_joinPr. Qed.

Lemma rl_join_min l1 l2 l3 :
  l1 ⊔ₗ l2 ⊑ₗ l3 =
  (l1 ⊑ₗ l3) && (l2 ⊑ₗ l3).
Proof.
apply/rl_leqbP/andP; rewrite /rl_leq.
  move=> H; split; apply/rl_leqbP; rewrite /rl_leq=> Fs; move/(_ Fs) in H.
    exact: (readers_leq_trans (ra_joinPl (rif_state l1) (rif_state l2) Fs)).
  exact: (readers_leq_trans (ra_joinPr (rif_state l1) (rif_state l2) Fs)).
case=> /rl_leqbP H1 /rl_leqbP H2 Fs; move/(_ Fs) in H1; move/(_ Fs) in H2.
by rewrite /rl_join (lock rif_readers) /= -lock ra_join_min H1.
Qed.

Lemma rl_leq_refl : reflexive rl_leqb.
Proof.
by move=> l; apply/rl_leqbP=> Fs; rewrite readers_leq_refl.
Qed.

Lemma rl_leq_trans : transitive rl_leqb.
Proof.
move=> l2 l1 l3 /rl_leqbP H12 /rl_leqbP H23.
apply/rl_leqbP=> Fs; move/(_ Fs) in H12; move/(_ Fs) in H23.
exact: readers_leq_trans H23.
Qed.

Definition rl_trans l F :=
  @RifLabel l (rif_trans l (rif_state l, F)).

Definition rl_readers l :=
  rif_readers l (rif_state l).

Variable mt : machine_types.

(** We model the machine's observable behavior using a trace of events
    stored in the internal state. This trace can only be accessed
    through the output and reclassify system services, as described below. *)

CoInductive event :=

(** [Output out rs] corresponds to sending the word [out] through an
    output channel. The set of readers [rs] marks which principals are
    capable of observing that output. *)

| Output of mword mt & readers

(** [Reclassify rl F] represents the reclassification of a piece of
    data tagged with label [rl] according to reclassifier [F]. *)

| Reclassify of rifLabel & Σ.

Definition sum_of_event e :=
  match e with
  | Output x rs => inl (x, rs)
  | Reclassify rl F => inr (rl, F)
  end.

Definition event_of_sum x :=
  match x with
  | inl (x, rs) => Output x rs
  | inr (rl, F) => Reclassify rl F
  end.

Lemma sum_of_eventK : cancel sum_of_event event_of_sum.
Proof. by case. Qed.

Definition event_eqMixin := CanEqMixin sum_of_eventK.
Canonical event_eqType := Eval hnf in EqType event event_eqMixin.

Section Indist.

Context {T : eqType}.
Variable t : T -> readers.

Definition indist rs (ra1 ra2 : T) :=
  (t ra1 ⊑ᵣ rs) || (t ra2 ⊑ᵣ rs) ==> (ra1 == ra2).

Lemma indist_refl rl : reflexive (indist rl).
Proof. by move=> ra; rewrite /indist eqxx implybT. Qed.

Lemma indist_sym rl : symmetric (indist rl).
Proof. by move=> ra1 ra2; rewrite /indist orbC eq_sym. Qed.

Lemma indist_trans rl : transitive (indist rl).
Proof.
move=> ra2 ra1 ra3; rewrite /indist => e1 e2.
apply/implyP=> /orP [e|e].
  by move: e1 e2; rewrite e /= => /eqP <-; rewrite e => /eqP ->.
by move: e2 e1; rewrite e orbT /= => /eqP ->; rewrite e orbT /= => /eqP ->.
Qed.

End Indist.

Fixpoint observe rs es :=
  if es is e :: es' then
    match e with
      | Output out rs' =>
        if ~~ (rs ⊑ᵣ rs' ) then out :: observe rs es'
        else observe rs es'
    | Reclassify rl F =>
      if (rs ⊑ᵣ rl_readers rl) && ~~ (rs ⊑ᵣ rl_readers (rl_trans rl F)) then
        [::]
      else observe rs es'
    end
  else [::].

End Common.

Delimit Scope rif_scope with rif.
Infix "⊑ᵣ" := readers_leq (at level 50) : rif_scope.
Infix "⊔ᵣ" := readers_join (at level 40, left associativity) : rif_scope.
Notation "⊥ₐ" := (@ra_bot _) : rif_scope.
Infix "⊔ₐ" := (@ra_join _) (at level 40, left associativity) : rif_scope.
Notation "⊥ₗ" := (@rl_bot _) : rif_scope.
Infix "⊑ₗ" := (@rl_leqb _) (at level 50) : rif_scope.
Infix "⊔ₗ" := (@rl_join _) (at level 40, left associativity) : rif_scope.
