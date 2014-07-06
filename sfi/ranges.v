Require Import List Bool ZArith.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Require Import lib.utils common.common lib.ordered.
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

Lemma addw_succ : forall w1 w2,
  w1 < w2 -> word_to_Z (w1 + Z_to_word 1)%w = (word_to_Z w1 + 1)%Z.
Proof.
  intros x y LT.
  rewrite <- (word_to_ZK x) at 1; rewrite <- (word_to_ZK 1).
  rewrite addwP.
  repeat rewrite Z_to_wordK;
    try solve [ reflexivity
              | generalize min_word_bound, max_word_bound; omega ].
  assert (word_to_Z min_word <= word_to_Z x)%Z by
    (rewrite <- word_to_Z_le; apply lew_min).
  assert (word_to_Z y <= word_to_Z max_word)%Z by 
    (rewrite <- word_to_Z_le; apply lew_max).
  assert (word_to_Z x < word_to_Z max_word)%Z by
    (apply word_to_Z_lt in LT; omega).
  omega.
Qed.  

Lemma lebw_succ : forall x y, x < y -> x <? x + 1 = true.
Proof.
  intros x y LT. apply addw_succ in LT.
  rewrite word_to_Z_ltb LT Z.ltb_lt; omega.
Qed.

Theorem range'_set : forall meas l h,
  is_set (range' meas l h) = true.
Proof.
  induction meas as [|meas]; simpl; [reflexivity|].
  intros l h; destruct (l <=> h) eqn:CMP; try reflexivity.
  simpl; rewrite IHmeas.
  destruct meas; simpl; [reflexivity|].
  destruct (l + 1 <=> h) eqn:CMP';
    solve [ reflexivity | rewrite andb_true_r; eapply lebw_succ; eassumption ].
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
  range' (Z.to_nat ((word_to_Z h - word_to_Z l) + 1)%Z) l h.

Corollary range_set : forall l h, is_set (range l h) = true.
Proof. intros until 0; apply range'_set. Qed.
Hint Resolve range_set.

Corollary range_elts_ok : forall l h e,
  In e (range l h) -> l <= e <= h.
Proof. intros until 0; apply range'_elts_ok. Qed.

Lemma addw_le : forall x y,
  x < y -> x + 1 <= y.
Proof.
  intros x y LT.
  apply word_to_Z_le.
  erewrite addw_succ by eassumption.
  apply word_to_Z_lt in LT.
  omega.
Qed.

Theorem range_elts_all : forall l h e,
  l <= e <= h -> In e (range l h).
Proof.
  unfold range; intros l h e [LE EH];
    assert (LH : l <= h) by eauto with ordered.
  remember (Z.to_nat ((word_to_Z h - word_to_Z l) + 1)%Z) as meas eqn:meas_def'.
  assert (meas_def : meas = S (Z.to_nat (word_to_Z h - word_to_Z l))). {
    rewrite Z2Nat.inj_add in meas_def'; try solve [vm_compute; inversion 1].
    - rewrite plus_comm in meas_def'; simpl in meas_def'; exact meas_def'.
    - apply Z.le_0_sub, word_to_Z_le; exact LH.
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
    replace (word_to_Z h - (word_to_Z l + 1))%Z
       with (word_to_Z h - word_to_Z l - 1)%Z
         by omega.
    rewrite <- Z2Nat.inj_succ.
    + f_equal; omega.
    + rewrite Z.sub_1_r; apply Zlt_0_le_0_pred, Z.lt_0_sub, word_to_Z_lt;
        exact CMP.
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
