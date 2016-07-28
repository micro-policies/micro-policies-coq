From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq fintype finfun.
From CoqUtils Require Import hseq ord fset partmap.
From MicroPolicies Require Import common.types symbolic.symbolic.

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

Section Dev.

Parameter Σ : finType.

Local Open Scope fset_scope.

Record rifAutomaton := RifAutomaton {
  rif_states : nat;
  rif_trans : {ffun 'I_rif_states * Σ -> 'I_rif_states};
  rif_prins : {ffun 'I_rif_states -> {fset nat}}
}.

Definition ra_bot :=
  @RifAutomaton 1 [ffun _ => Sub 0 erefl] [ffun _ => fset0].

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

Definition rl_bot :=
  @RifLabel ra_bot (@Ordinal 1 0 erefl).

Local Notation "⊥" := rl_bot.

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
  forall Fs, fsubset (rif_prins _ (rif_run (rif_state l1) Fs))
                     (rif_prins _ (rif_run (rif_state l2) Fs)).

Axiom rl_leqb : rel rifLabel.
Axiom rl_leqbP : forall l1 l2, reflect (rl_leq l1 l2) (rl_leqb l1 l2).

Definition rl_join l1 l2 :=
  @RifLabel (ra_join l1 l2) (ord_pair (rif_state l1) (rif_state l2)).

Infix "⊑" := rl_leqb (at level 50).
Infix "⊔" := rl_join (at level 40, left associativity).

Lemma rl_joinPl l1 l2 : l1 ⊑ l1 ⊔ l2.
Proof. by apply/rl_leqbP=> Fs; apply/ra_joinPl. Qed.

Lemma rl_joinPr l1 l2 : l2 ⊑ l1 ⊔ l2.
Proof. by apply/rl_leqbP=> Fs; apply/ra_joinPr. Qed.

Lemma rl_join_min l1 l2 l3 :
  l1 ⊔ l2 ⊑ l3 =
  (l1 ⊑ l3) && (l2 ⊑ l3).
Proof.
apply/rl_leqbP/andP; rewrite /rl_leq.
  move=> H; split; apply/rl_leqbP; rewrite /rl_leq=> Fs; move/(_ Fs) in H.
    exact: (fsubset_trans (ra_joinPl (rif_state l1) (rif_state l2) Fs)).
  exact: (fsubset_trans (ra_joinPr (rif_state l1) (rif_state l2) Fs)).
case=> /rl_leqbP H1 /rl_leqbP H2 Fs; move/(_ Fs) in H1; move/(_ Fs) in H2.
by rewrite /rl_join (lock rif_prins) /= -lock ra_join_min H1.
Qed.

Lemma rl_leq_refl : reflexive rl_leqb.
Proof.
by move=> l; apply/rl_leqbP=> Fs; rewrite fsubsetxx.
Qed.

Lemma rl_leq_trans : transitive rl_leqb.
Proof.
move=> l2 l1 l3 /rl_leqbP H12 /rl_leqbP H23.
apply/rl_leqbP=> Fs; move/(_ Fs) in H12; move/(_ Fs) in H23.
exact: fsubset_trans H23.
Qed.

Inductive mem_tag :=
| MemInstr of Σ
| MemData  of rifLabel.

Definition sum_of_mem_tag t :=
  match t with
  | MemInstr F => inl F
  | MemData l => inr l
  end.

Definition mem_tag_of_sum t :=
  match t with
  | inl F => MemInstr F
  | inr l => MemData l
  end.

Lemma sum_of_mem_tagK : cancel sum_of_mem_tag mem_tag_of_sum.
Proof. by case. Qed.

Definition mem_tag_eqMixin := CanEqMixin sum_of_mem_tagK.
Canonical mem_tag_eqType := EqType mem_tag mem_tag_eqMixin.

Import Symbolic.

Definition rif_tags := {|
  pc_tag_type    := rifLabel_eqType;
  reg_tag_type   := rifLabel_eqType;
  mem_tag_type   := mem_tag_eqType;
  entry_tag_type := unit_eqType
|}.

Definition instr_rules
  (op : opcode) (tpc : rifLabel) (ti : Σ) (ts : hseq (tag_type rif_tags) (inputs op)) :
  option (ovec rif_tags op) :=
  let ret := fun rtpc (rt : type_of_result rif_tags (outputs op)) => Some (@OVec rif_tags op rtpc rt) in
  match op, ts, ret with
  | NOP, _, ret                             => ret tpc tt
  | CONST, [hseq lold], ret                 => ret tpc ⊥
  | MOV, [hseq l; lold], ret                => ret tpc l
  | BINOP b, [hseq l1; l2; lold], ret       => ret tpc (l1 ⊔ l2)
  | LOAD, [hseq l1; MemData l2; lold], ret  => ret tpc (l1 ⊔ l2)
  | STORE, [hseq l1; l2; MemData lold], ret => if l1 ⊔ tpc ⊑ lold then ret tpc (MemData (l1 ⊔ l2 ⊔ tpc))
                                               else None
  | JUMP, [hseq l], ret                     => ret (l ⊔ tpc) tt
  | BNZ, [hseq l], ret                      => ret (l ⊔ tpc) tt
  | JAL, [hseq l1; lold], ret               => None
  | _, _, _                                 => None
  end.

Definition transfer (iv : ivec rif_tags) : option (vovec rif_tags (op iv)) :=
  match iv with
  | IVec (OP op) tpc ti ts =>
    match ti with
    | MemInstr F => @instr_rules op tpc F ts
    | MemData _ => None
    end
  | IVec SERVICE _ _ _ => None
  end.

Global Instance sym_rif : params := {
  ttypes := rif_tags;

  transfer := transfer;

  internal_state := unit_eqType
}.

End Dev.
