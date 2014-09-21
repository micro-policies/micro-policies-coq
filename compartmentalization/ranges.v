Require Import List Bool ZArith.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Require Import lib.Integers lib.utils common.common lib.ordered.
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

End WithClasses.
