Require Import List Bool ZArith.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Require Import lib.Integers lib.utils common.common lib.ordered.
Require Import lib.list_utils lib.set_utils.
Set Bullet Behavior "Strict Subproofs".

Section WithClasses.

Context {t    : machine_types}
        {ops  : machine_ops t}
        {spec : machine_ops_spec ops}.

Import ListNotations.
Local Notation word := (word t).
Open Scope word_scope.

Fixpoint range' (meas : nat) (l h : word) : list word :=
  match meas , l <=> h with
    | O       , _  => []
    | S meas' , Lt => l :: range' meas' (l + 1) h
    | S meas' , Eq => [l]
    | S meas' , Gt => []
  end.

Lemma addw_succ : forall w1 w2 : word,
  w1 < w2 -> Word.unsigned (w1 + 1)%w = (Word.unsigned w1 + 1)%Z.
Proof.
  move => x y LT.
  rewrite -{1}(Word.repr_unsigned _ x) /Word.one Word.add_repr.
  apply Word.unsigned_repr.
  rewrite /lt IntOrdered.compare_unsigned in LT.
  move: (Word.unsigned_range x) (Word.unsigned_range y) => H1 H2.
  have H3: (Word.unsigned x < Word.unsigned y)%Z by auto.
  rewrite /Word.max_unsigned.
  omega.
Qed.

Lemma lebw_succ : forall x y : word, x < y -> x <? x + 1 = true.
Proof.
  move => x y /(addw_succ _) H.
  rewrite /ltb !IntOrdered.compare_unsigned H.
  case E: (Word.unsigned _ ?= Word.unsigned _ + _)%Z => //=.
  - move/Z.compare_eq_iff: E => E. omega.
  - move/Z.compare_gt_iff: E => E. omega.
Qed.

Theorem range'_set : forall meas l h,
  is_set (range' meas l h) = true.
Proof.
  induction meas as [|meas]; simpl; [reflexivity|].
  intros l h; destruct (l <=> h) eqn:CMP; try reflexivity.
  simpl; rewrite IHmeas.
  destruct meas; simpl; [reflexivity|].
  case CMP': (l + 1 <=> h); try
    try solve [ reflexivity | rewrite andb_true_r; eapply lebw_succ; eassumption ].
Qed.

Theorem range'_elts_ok : forall meas l h e,
  In e (range' meas l h) -> l <= e <= h.
Proof.
  induction meas as [|meas]; [inversion 1|].
  simpl; intros until 0; intros IN.
  destruct (l <=> h) eqn:CMP; simpl in *.
  - apply compare_eq in CMP; destruct IN as [EQ|[]];
      repeat progress subst; auto 2 with ordered.
  - destruct IN as [EQ | IN]; subst; auto with ordered.
    apply IHmeas in IN; destruct IN as [LT LE].
    assert (l < l + 1) by (eapply ltb_lt,lebw_succ; eassumption).
    split; eauto with ordered.
  - inversion IN.
Qed.

Definition range (l h : word) :=
  range' (Z.to_nat ((Word.unsigned h - Word.unsigned l) + 1)%Z) l h.

Corollary range_set : forall l h, is_set (range l h) = true.
Proof. intros until 0; apply range'_set. Qed.
Hint Resolve range_set.

Corollary range_elts_ok : forall l h e,
  In e (range l h) -> l <= e <= h.
Proof. intros until 0; apply range'_elts_ok. Qed.

Lemma addw_le : forall x y : word,
  x < y -> x + 1 <= y.
Proof.
  move => x y LT.
  rewrite /le IntOrdered.compare_unsigned (addw_succ _ _ LT).
  move => /Z.compare_gt_iff ?.
  rewrite /lt IntOrdered.compare_unsigned in LT.
  move: LT => /Z.compare_lt_iff LT. omega.
Qed.

Theorem range_elts_all : forall l h e,
  l <= e <= h -> In e (range l h).
Proof.
  unfold range; intros l h e [LE EH];
    assert (LH : l <= h) by eauto with ordered.
  remember (Z.to_nat ((Word.unsigned h - Word.unsigned l) + 1)%Z) as meas eqn:meas_def'.
  assert (meas_def : meas = S (Z.to_nat (Word.unsigned h - Word.unsigned l))). {
    rewrite Z2Nat.inj_add in meas_def'.
    - rewrite plus_comm in meas_def'; simpl in meas_def'; exact meas_def'.
    - clear meas.
      move: LH => /(le__lt_or_eq _ _) [LH | ->].
      + rewrite /lt IntOrdered.compare_unsigned in LH.
        move/Z.compare_lt_iff: LH => LH. omega.
      + move/Z.compare_gt_iff => H. omega.
    - move/Z.compare_gt_iff => ?. omega.
  }
  clear meas_def'; gdep e; gdep h; gdep l; induction meas; intros;
    simpl in *; inversion meas_def; subst; clear meas_def.
  destruct (l <=> h) eqn:CMP.
  - apply compare_eq in CMP; apply le__lt_or_eq in EH; apply le__lt_or_eq in LE;
      subst; destruct EH,LE; auto with ordered.
    elim (lt_asym h e); assumption.
  - simpl. apply le__lt_or_eq in LE; destruct LE as [LE | LE]; auto.
    right; apply IHmeas; eauto using addw_le.
    erewrite addw_succ by eassumption.
    replace (Word.unsigned h - (Word.unsigned l + 1))%Z
       with (Word.unsigned h - Word.unsigned l - 1)%Z
         by omega.
    rewrite <- Z2Nat.inj_succ.
    + f_equal; omega.
    + rewrite IntOrdered.compare_unsigned in CMP.
      move/Z.compare_lt_iff: CMP => CMP. omega.
  - contradiction.
Qed.

Corollary range_elts : forall l h e,
  In e (range l h) <-> l <= e <= h.
Proof. split; [apply range_elts_ok | apply range_elts_all]. Qed.

Corollary range_empty : forall l h,
  range l h = [] <-> l > h.
Proof.
  intros; rewrite nil_iff_not_in; split.
  - intros NOT_IN; apply gt_not_le; intros LE.
    apply NOT_IN with l, range_elts; auto with ordered.
  - intros GT e IN. apply range_elts in IN.
    destruct IN; assert (l <= h) by eauto 2 with ordered; auto.
Qed.

End WithClasses.

Hint Resolve range_set.
