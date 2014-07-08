Require Import Coq.Classes.SetoidDec Coqlib utils.
Require Import Compare_dec ZArith. (* For instances *)
Require lib.Integers lib.FiniteMaps. (* For instances *)

Create HintDb ordered discriminated.

(*** Type classes and instances ***)

Generalizable Variables A.

Class Ordered A `{eqdec : ! EqDec (eq_setoid A)} :=
  { compare          : A -> A -> comparison
  ; compare_refl     : forall a,     compare a a = Eq
  ; compare_asym     : forall a b,   compare a b = CompOpp (compare b a)
  ; compare_eq       : forall a b,   compare a b = Eq -> a = b
  ; compare_lt_trans : forall a b c, compare a b = Lt -> compare b c = Lt ->
                                     compare a c = Lt
  ; compare_gt_trans : forall a b c, compare a b = Gt -> compare b c = Gt ->
                                     compare a c = Gt }.

Hint Resolve @compare_refl @compare_asym
             @compare_eq @compare_lt_trans @compare_gt_trans
  : ordered.

Delimit Scope ordered_scope with ordered.
Open Scope ordered_scope.
  
Instance nat_ordered : Ordered nat.
Proof.
  apply Build_Ordered with nat_compare; intros until 0.
  - apply nat_compare_eq_iff; reflexivity.
  - specialize (nat_compare_spec a b); intros CS.
    inversion CS as [EQ COMP | LT COMP | GT COMP].
    + subst; rewrite <- COMP; reflexivity.
    + apply nat_compare_gt in LT; rewrite LT; reflexivity.
    + apply nat_compare_lt in GT; rewrite GT; reflexivity.
  - apply nat_compare_eq_iff.
  - repeat rewrite <- nat_compare_lt; apply Lt.lt_trans.
  - repeat rewrite <- nat_compare_gt; apply Gt.gt_trans.
Defined.

Instance Z_eqdec : EqDec (eq_setoid Z) := Z.eq_dec.
Instance Z_ordered : Ordered Z.
Proof.
  apply Build_Ordered with Z.compare; intros until 0.
  - apply Z.compare_refl.
  - apply Z.compare_antisym.
  - apply Z.compare_eq.
  - apply Zcompare_Lt_trans.
  - apply Zcompare_Gt_trans.
Defined.

Require Integers.

Module IntOrdered (WS : Integers.WORDSIZE).
  (* We need integers that are indexable and orderable, so... *)
  Module IntIndexed := FiniteMaps.IntIndexed WS.
  Import IntIndexed.
  Import Integers.Word.

  Instance int_eqdec : EqDec (eq_setoid IntIndexed.t) := @eqType_EqDec (@Integers.int_eqType _).
  
  Definition int_compare (a b : IntIndexed.t) : comparison :=
    if a == b
    then Eq
    else if lt a b
         then Lt
         else Gt.
  
  Instance int_ordered : Ordered t.
  Proof.
    apply Build_Ordered with int_compare; unfold int_compare; intros.
    - destruct (a == a); [reflexivity | congruence].
    - destruct (a == b) as [ | NEQAB], (b == a) as [ | NEQBA]; auto; try congruence.
      unfold lt;
        destruct (zlt (signed a) (signed b)), (zlt (signed b) (signed a));
        try solve [auto | omega].
      assert (E : signed a = signed b) by omega.
      generalize (eq_signed _ a b). rewrite E. rewrite zeq_true.
      intros TRUE.
      generalize (eq_false _  _ _ NEQAB). congruence.
    - destruct (a == b); [auto | destruct (lt a b); discriminate].
    - unfold lt in *;
        destruct (a == b), (b == c),
                 (zlt (signed a) (signed b)), (zlt (signed b) (signed c));
        try congruence.
      destruct (a == c), (zlt (signed a) (signed c)); ssubst;
        first [reflexivity | omega].
    - unfold lt in *;
        destruct (a == b) as [|NEQAB], (b == c) as [|NEQBC],
                 (zlt (signed a) (signed b)), (zlt (signed b) (signed c));
        try congruence.
      destruct (a == c), (zlt (signed a) (signed c)); ssubst;
        try first [reflexivity | omega].
      assert (E : signed b = signed c) by omega.
      generalize (eq_signed _ b c). rewrite E. rewrite zeq_true.
      intros TRUE.
      generalize (eq_false _  _ _ NEQBC). congruence.
  Defined.
End IntOrdered.

Instance comparison_eqdec : EqDec (eq_setoid comparison).
Proof. cbv; intros c1 c2; fold (c1 <> c2); decide equality. Defined.

Definition comparison_compare (c1 c2 : comparison) :=
  match c1 , c2 with
    | Lt , Lt => Eq
    | Lt , Eq => Lt
    | Lt , Gt => Lt
    | Eq , Lt => Gt
    | Eq , Eq => Eq
    | Eq , Gt => Lt
    | Gt , Lt => Gt
    | Gt , Eq => Gt
    | Gt , Gt => Eq
  end.

Instance comparison_ordered : Ordered comparison.
Proof.
  apply Build_Ordered with comparison_compare;
    repeat destruct 0; simpl; congruence.
Defined.

Infix "<=>" := compare (at level 70, no associativity) : ordered_scope.

Section binary_ops_props.

Context `{ORD : Ordered A}.
Variables a b : A.

Definition ltb : bool := (a <=> b) ==  Lt.
Definition gtb : bool := (a <=> b) ==  Gt.
Definition leb : bool := (a <=> b) =/= Gt.
Definition geb : bool := (a <=> b) =/= Lt.
              
Definition lt : Prop := (a <=> b) =  Lt.
Definition gt : Prop := (a <=> b) =  Gt.
Definition le : Prop := (a <=> b) <> Gt.
Definition ge : Prop := (a <=> b) <> Lt.

End binary_ops_props.

Infix "<?"  := ltb : ordered_scope.
Infix ">?"  := gtb : ordered_scope.
Infix "<=?" := leb : ordered_scope.
Infix ">=?" := geb : ordered_scope.

Infix "<"  := lt : ordered_scope.
Infix ">"  := gt : ordered_scope.
Infix "<=" := le : ordered_scope.
Infix ">=" := ge : ordered_scope.

Notation "x <? y <? z" := ((x <? y) && (y <? z))
  (at level 70, y at next level, no associativity) : ordered_scope.
Notation "x <? y <=? z" := ((x <? y) && (y <=? z))
  (at level 70, y at next level, no associativity) : ordered_scope.
Notation "x <=? y <? z" := ((x <=? y) && (y <? z))
  (at level 70, y at next level, no associativity) : ordered_scope.
Notation "x <=? y <=? z" := ((x <=? y) && (y <=? z))
  (at level 70, y at next level, no associativity) : ordered_scope.

Notation "x >? y >? z" := ((x >? y) && (y >? z))
  (at level 70, y at next level, no associativity) : ordered_scope.
Notation "x >? y >=? z" := ((x >? y) && (y >=? z))
  (at level 70, y at next level, no associativity) : ordered_scope.
Notation "x >=? y >? z" := ((x >=? y) && (y >? z))
  (at level 70, y at next level, no associativity) : ordered_scope.
Notation "x >=? y >=? z" := ((x >=? y) && (y >=? z))
  (at level 70, y at next level, no associativity) : ordered_scope.

Notation "x < y < z" := (x < y /\ y < z)
  (at level 70, y at next level, no associativity) : ordered_scope.
Notation "x < y <= z" := (x < y /\ y <= z)
  (at level 70, y at next level, no associativity) : ordered_scope.
Notation "x <= y < z" := (x <= y /\ y < z)
  (at level 70, y at next level, no associativity) : ordered_scope.
Notation "x <= y <= z" := (x <= y /\ y <= z)
  (at level 70, y at next level, no associativity) : ordered_scope.

Notation "x > y > z" := (x > y /\ y > z)
  (at level 70, y at next level, no associativity) : ordered_scope.
Notation "x > y >= z" := (x > y /\ y >= z)
  (at level 70, y at next level, no associativity) : ordered_scope.
Notation "x >= y > z" := (x >= y /\ y > z)
  (at level 70, y at next level, no associativity) : ordered_scope.
Notation "x >= y >= z" := (x >= y /\ y >= z)
  (at level 70, y at next level, no associativity) : ordered_scope.

Section reflections.

Context `{ORD : Ordered A}.
Variables a b c : A.

Local Ltac solve_bool_prop :=
  compute -[compare]; destruct (a <=> b); simpl; split;
    try solve [ congruence
              | let H := fresh in intros H; contradict H; congruence ].

Lemma ltb_lt : a <?  b = true <-> a <  b. Proof. solve_bool_prop. Qed.
Lemma gtb_gt : a >?  b = true <-> a >  b. Proof. solve_bool_prop. Qed.
Lemma leb_le : a <=? b = true <-> a <= b. Proof. solve_bool_prop. Qed.
Lemma geb_ge : a >=? b = true <-> a >= b. Proof. solve_bool_prop. Qed.


Lemma ltb_nlt : a <?  b = false <-> ~ a <  b. Proof. solve_bool_prop. Qed.
Lemma gtb_ngt : a >?  b = false <-> ~ a >  b. Proof. solve_bool_prop. Qed.
Lemma leb_nle : a <=? b = false <-> ~ a <= b. Proof. solve_bool_prop. Qed.
Lemma geb_nge : a >=? b = false <-> ~ a >= b. Proof. solve_bool_prop. Qed.

Local Ltac solve_cases :=
  compute -[compare]; destruct_with_eqn (a <=> b); congruence.

Lemma lt_cases : if a <?  b then a <  b else a >= b. Proof. solve_cases. Qed.
Lemma gt_cases : if a >?  b then a >  b else a <= b. Proof. solve_cases. Qed.
Lemma le_cases : if a <=? b then a <= b else a >  b. Proof. solve_cases. Qed.
Lemma ge_cases : if a >=? b then a >= b else a <  b. Proof. solve_cases. Qed.

End reflections.

Lemma leltb_lelt (A : Type) (eqdec : EqDec (eq_setoid A)) (ORD : Ordered A) (a b c : A) :
  a <=? b <? c = true <-> a <= b < c.
Proof.
constructor.
  intro leltb.
  apply andb_true_iff in leltb.
  destruct leltb as [leb ltb].
  apply leb_le in leb.
  apply ltb_lt in ltb.
  now split.
destruct 1.
apply andb_true_iff.
split.
  now apply leb_le.
now apply ltb_lt.
Qed.

Hint Resolve @ltb_lt   @gtb_gt   @leb_le   @geb_ge
             @ltb_nlt  @gtb_ngt  @leb_nle  @geb_nge
             @lt_cases @gt_cases @le_cases @ge_cases
  : ordered.

Section reflexivity_irreflexivity.

Context `{ORD : Ordered A}.
Variable a : A.

Local Ltac solve_same :=
  unfold ltb,gtb,leb,geb,lt,gt,le,ge; rewrite compare_refl;
    solve [auto | congruence].

Lemma ltb_irrefl : a <?  a = false. Proof. solve_same. Qed.
Lemma gtb_irrefl : a >?  a = false. Proof. solve_same. Qed.
Lemma leb_refl   : a <=? a = true.  Proof. solve_same. Qed.
Lemma geb_refl   : a >=? a = true.  Proof. solve_same. Qed.

Lemma lt_irrefl : ~ a < a. Proof. solve_same. Qed.
Lemma gt_irrefl : ~ a > a. Proof. solve_same. Qed.
Lemma le_refl   : a <= a.  Proof. solve_same. Qed.
Lemma ge_refl   : a >= a.  Proof. solve_same. Qed.

End reflexivity_irreflexivity.  

Hint Resolve @ltb_irrefl @gtb_irrefl @leb_refl @geb_refl
             @lt_irrefl  @gt_irrefl  @le_refl  @ge_refl
  : ordered.

Section nonstrict_equivalences.

Context `{ORD : Ordered A}.
Variables a b : A.

Local Ltac solve_bool :=
  unfold ltb,gtb,leb,geb;
  destruct (a <=> b) eqn:E; simpl; try congruence;
  destruct (_ == _); simpl; auto; ssubst;
  first [apply compare_eq in E | rewrite compare_refl in E];
  congruence.

Local Notation DECOMPOSE_B lax strict := (lax a b = (strict a b || (a == b)))
  (only parsing).

Lemma leb_is_ltb_or_eq : DECOMPOSE_B leb ltb. Proof. solve_bool. Qed.
Lemma geb_is_gtb_or_eq : DECOMPOSE_B geb gtb. Proof. solve_bool. Qed.

Local Ltac solve_to :=
  unfold lt,gt,le,ge; destruct (a <=> b) eqn:E;
    solve [eauto with ordered | congruence].

Local Ltac solve_from :=
  unfold lt,gt,le,ge; destruct 1; [|subst; rewrite compare_refl]; congruence.

Lemma le__lt_or_eq : a <= b -> {a < b} + {a = b}. Proof. solve_to.   Qed.
Lemma ge__gt_or_eq : a >= b -> {a > b} + {a = b}. Proof. solve_to.   Qed.
Lemma lt_or_eq__le : {a < b} + {a = b} -> a <= b. Proof. solve_from. Qed.
Lemma gt_or_eq__ge : {a > b} + {a = b} -> a >= b. Proof. solve_from. Qed.

Local Ltac solve_iff :=
  split;
  [ intro H; first [apply le__lt_or_eq in H | apply ge__gt_or_eq in H]
  | destruct 1; first [apply lt_or_eq__le | apply gt_or_eq__ge] ];
  tauto.

(* These use `or' instead of `sumbool' because `iff' is in `Prop'. *)
Corollary le_iff_lt_or_eq : a <= b <-> a < b \/ a = b. Proof. solve_iff. Qed.
Corollary ge_iff_gt_or_eq : a >= b <-> a > b \/ a = b. Proof. solve_iff. Qed.

End nonstrict_equivalences.

Hint Resolve @le__lt_or_eq @ge__gt_or_eq
             @lt_or_eq__le @gt_or_eq__ge
  : ordered.

Section relationships.

Context `{ORD : Ordered A}.
Variables a b : A.

Local Ltac solve_eq := intros; subst; auto with ordered.
  
Lemma eq__leb  : a = b -> a <=? b = true.  Proof. solve_eq. Qed.
Lemma eq__nltb : a = b -> a <?  b = false. Proof. solve_eq. Qed.
Lemma eq__geb  : a = b -> a >=? b = true.  Proof. solve_eq. Qed.
Lemma eq__ngtb : a = b -> a >?  b = false. Proof. solve_eq. Qed.

Lemma eq__le  : a = b -> a <= b.  Proof. solve_eq. Qed.
Lemma eq__nlt : a = b -> ~ a < b. Proof. solve_eq. Qed.
Lemma eq__ge  : a = b -> a >= b.  Proof. solve_eq. Qed.
Lemma eq__ngt : a = b -> ~ a > b. Proof. solve_eq. Qed.

Local Ltac solve_cmp :=
  try rewrite leb_is_ltb_or_eq; try rewrite geb_is_gtb_or_eq;
  intros H; rewrite H; auto.

Lemma ltb__leb : a <? b = true -> a <=? b = true. Proof. solve_cmp. Qed.
Lemma gtb__geb : a >? b = true -> a >=? b = true. Proof. solve_cmp. Qed.

Lemma lt__le : a < b -> a <= b. Proof. auto with ordered. Qed.
Lemma gt__le : a > b -> a >= b. Proof. auto with ordered. Qed.

Local Ltac solve_flip :=
  cbv -[compare]; rewrite (compare_asym b a);
  destruct (a <=> b); simpl; congruence.

Lemma ltb_is_gtb : (a <?  b) = (b >?  a). Proof. solve_flip. Qed.
Lemma leb_is_geb : (a <=? b) = (b >=? a). Proof. solve_flip. Qed.

Lemma lt__gt : a <  b -> b >  a. Proof. solve_flip. Qed.
Lemma gt__lt : a >  b -> b <  a. Proof. solve_flip. Qed.
Lemma le__ge : a <= b -> b >= a. Proof. solve_flip. Qed.
Lemma ge__le : a >= b -> b <= a. Proof. solve_flip. Qed.

Ltac solve_negb :=
  unfold ltb,gtb,leb,geb,nequiv_dec; destruct ((a <=> b) == _); reflexivity.

Ltac solve_not :=
  split; auto;
  unfold lt,gt,le,ge; intros;
  match goal with
    | H : ~ ((a <=> b) <> ?C) |- _ =>
      destruct ((a <=> b) == C) eqn:CMP; [tauto | exfalso; auto]
  end.

Lemma ltb_not_geb : a <?  b = negb (a >=? b). Proof. solve_negb. Qed. 
Lemma gtb_not_leb : a >?  b = negb (a <=? b). Proof. solve_negb. Qed.
Lemma leb_not_gtb : a <=? b = negb (a >?  b). Proof. solve_negb. Qed.
Lemma geb_not_ltb : a >=? b = negb (a <?  b). Proof. solve_negb. Qed.

Lemma lt_not_ge : a <  b <-> ~ a >= b. Proof. solve_not. Qed.
Lemma gt_not_le : a >  b <-> ~ a <= b. Proof. solve_not. Qed.
Lemma le_not_gt : a <= b <-> ~ a >  b. Proof. solve_not. Qed.
Lemma ge_not_lt : a >= b <-> ~ a <  b. Proof. solve_not. Qed.

End relationships.
(* Need to generalize the variables *)
Section relationships'.

Context `{ORD : Ordered A}.
Variables a b : A.

Local Ltac solve_flip_iff :=
  split; try solve [apply lt__gt | apply gt__lt | apply le__ge | apply ge__le].

Corollary lt_iff_gt : a <  b <-> b >  a. Proof. solve_flip_iff. Qed.
Corollary le_iff_ge : a <= b <-> b >= a. Proof. solve_flip_iff. Qed.

End relationships'.

Hint Resolve @eq__leb  @eq__nltb @eq__geb @eq__ngtb
             @eq__le   @eq__nlt  @eq__ge  @eq__ngt
             @ltb__leb @gtb__geb
             @lt__le @gt__le
             @ltb_is_gtb @leb_is_geb
             @lt__gt @gt__lt @le__ge @ge__le
             @ltb_not_geb @gtb_not_leb @leb_not_gtb @geb_not_ltb
  : ordered.

Section decidability.

Context `{ORD : Ordered A}.
Variables a b : A.

Lemma trichotomy : {a < b} + {a = b} + {a > b}.
Proof.
  cbv -[compare]; destruct (a <=> b) eqn:E; try apply compare_eq in E; auto.
Qed.

Local Ltac solve_two   := destruct trichotomy; auto with ordered.
Local Ltac solve_three := destruct trichotomy as [[?|?]|?]; auto with ordered.
Local Ltac solve_dec   := solve [solve_two | solve_three].

Corollary le_gt_dec : {a <= b} + {a > b}. Proof. solve_dec. Qed.
Corollary ge_lt_dec : {a >= b} + {a < b}. Proof. solve_dec. Qed.

Corollary le_lt_dec : {a <= b} + {b < a}.
Proof. destruct le_gt_dec; auto with ordered. Qed.
Corollary ge_gt_dec : {a >= b} + {b > a}.
Proof. destruct ge_lt_dec; auto with ordered. Qed.

End decidability.

Section transitivity.

Context `{ORD : Ordered A}.
Variables a b c : A.

Local Ltac prim_trans AB BC :=
  simpl;
  try first [ generalize (compare_lt_trans _ _ _ AB BC)
            | generalize (compare_gt_trans _ _ _ AB BC) ];
  congruence.

Local Ltac solve_trans_strict :=
  unfold ltb,gtb;
  destruct ((a <=> b) == _) as [AB|AB],
           ((b <=> c) == _) as [BC|BC],
           ((a <=> c) == _) as [AC|AC];
  prim_trans AB BC.

Local Ltac solve_trans_eq :=
  unfold leb,geb;
  destruct (a <=> b) eqn:AB, (b <=> c) eqn:BC, (a <=> c) eqn:AC;
  unfold nequiv_dec; simpl; try congruence;
  try apply compare_eq in AB; try apply compare_eq in BC; subst;
  solve [ try rewrite compare_refl in AC; congruence
        | prim_trans AB BC ].

Local Ltac solve_trans :=
  repeat rewrite <- ltb_lt;
  repeat rewrite <- gtb_gt;
  repeat rewrite <- leb_le;
  repeat rewrite <- geb_ge;
  solve [solve_trans_strict | solve_trans_eq].

Local Notation TRANS_B rel :=
  (rel a b = true -> rel b c = true -> rel a c = true)
  (only parsing).

Lemma ltb_trans : TRANS_B ltb. Proof. solve_trans. Qed.
Lemma gtb_trans : TRANS_B gtb. Proof. solve_trans. Qed.
Lemma leb_trans : TRANS_B leb. Proof. solve_trans. Qed.
Lemma geb_trans : TRANS_B geb. Proof. solve_trans. Qed.

Local Notation TRANS rel :=
  (rel a b -> rel b c -> rel a c)
  (only parsing).

Lemma lt_trans : TRANS lt. Proof. solve_trans. Qed.
Lemma gt_trans : TRANS gt. Proof. solve_trans. Qed.
Lemma le_trans : TRANS le. Proof. solve_trans. Qed.
Lemma ge_trans : TRANS ge. Proof. solve_trans. Qed.

Local Ltac mixed_bool :=
  first [rewrite leb_is_ltb_or_eq | rewrite geb_is_gtb_or_eq];
  rewrite orb_true_iff;
  destruct (_ == _).

Local Ltac mixed_prop :=
  first [rewrite le_iff_lt_or_eq | rewrite ge_iff_gt_or_eq];
  match goal with |- context[?x = ?y] => destruct (x == y) end.

Local Ltac solve_mixed :=
  first [mixed_bool | mixed_prop]; simpl; ssubst;
  intros; try match goal with H : _ \/ _ |- _ => destruct H; [|congruence] end;
  eauto 2 using ltb_trans, gtb_trans, lt_trans, gt_trans.
  
Local Notation SL_TRANS_B strict lax :=
  (strict a b = true -> lax b c = true -> strict a c = true)
  (only parsing).

Local Notation LS_TRANS_B lax strict :=
  (lax a b = true -> strict b c = true -> strict a c = true)
  (only parsing).

Lemma ltb_leb_trans : SL_TRANS_B ltb leb. Proof. solve_mixed. Qed.
Lemma gtb_geb_trans : SL_TRANS_B gtb geb. Proof. solve_mixed. Qed.
Lemma leb_ltb_trans : LS_TRANS_B leb ltb. Proof. solve_mixed. Qed.
Lemma geb_gtb_trans : LS_TRANS_B geb gtb. Proof. solve_mixed. Qed.
  
Local Notation SL_TRANS strict lax :=
  (strict a b -> lax b c -> strict a c)
  (only parsing).

Local Notation LS_TRANS lax strict :=
  (lax a b -> strict b c -> strict a c)
  (only parsing).

Lemma lt_le_trans : SL_TRANS lt le. Proof. solve_mixed. Qed.
Lemma gt_ge_trans : SL_TRANS gt ge. Proof. solve_mixed. Qed.
Lemma le_lt_trans : LS_TRANS le lt. Proof. solve_mixed. Qed.
Lemma ge_gt_trans : LS_TRANS ge gt. Proof. solve_mixed. Qed.

End transitivity.  

Hint Resolve @ltb_trans     @gtb_trans     @leb_trans     @geb_trans
             @lt_trans      @gt_trans      @le_trans      @ge_trans
             @ltb_leb_trans @gtb_geb_trans @leb_ltb_trans @geb_gtb_trans
             @lt_le_trans   @gt_ge_trans   @le_lt_trans   @ge_gt_trans
  : ordered.

Section asymmetry.

Context `{ORD : Ordered A}.
Variable a b : A.

Local Ltac solve_asym :=
  do 2 intro;
  first [ eapply lt_irrefl with b, lt_trans; eassumption
        | eapply gt_irrefl with b, gt_trans; eassumption ].

(* We deal with the `Prop' case first because the reasoning is easier and we can
   reflect the `bool' case into it. *)

Lemma lt_asym : a < b -> ~ b < a. Proof. solve_asym. Qed.
Lemma gt_asym : a > b -> ~ b > a. Proof. solve_asym. Qed.

Local Ltac solve_sym_eq :=
  repeat rewrite le_iff_lt_or_eq; repeat rewrite ge_iff_gt_or_eq;
  destruct 1,1; solve [congruence | elim lt_asym; auto | elim gt_asym; auto].

Lemma le_sym_eq : a <= b -> b <= a -> a = b. Proof. solve_sym_eq. Qed.
Lemma ge_sym_eq : a >= b -> b >= a -> a = b. Proof. solve_sym_eq. Qed.

Local Ltac solve_bool :=
  first [ rewrite ltb_lt, ltb_nlt; apply lt_asym
        | rewrite gtb_gt, gtb_ngt; apply gt_asym
        | repeat rewrite leb_le; apply le_sym_eq
        | repeat rewrite geb_ge; apply ge_sym_eq ].

Lemma ltb_asym : a <? b = true -> b <? a = false. Proof. solve_bool. Qed.
Lemma gtb_asym : a >? b = true -> b >? a = false. Proof. solve_bool. Qed.

Local Notation EQ_SYM_B rel := (rel a b = true -> rel b a = true -> a = b)
  (only parsing).

Lemma leb_sym_eq : EQ_SYM_B leb. Proof. solve_bool. Qed.  
Lemma geb_sym_eq : EQ_SYM_B geb. Proof. solve_bool. Qed.

End asymmetry.

Hint Resolve @ltb_asym @gtb_asym @leb_sym_eq @geb_sym_eq
             @lt_asym  @gt_asym  @le_sym_eq  @ge_sym_eq
  : ordered.

(* I could continue proving theorems -- so many theorems!  But I'm hopeful this
   will, at least initially, be enough. *)
