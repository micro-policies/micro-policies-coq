Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
Require Import div ssrint intdiv.
Require Import ord word partmap.
Require Import lib.utils common.common.
Set Bullet Behavior "Strict Subproofs".

Section WithClasses.

Context {t    : machine_types}
        {ops  : machine_ops t}
        {spec : machine_ops_spec ops}.

Local Notation word := (mword t).
Open Scope word_scope.
Open Scope ord_scope.

(*
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
*)

Lemma leqw_succ : forall x y : word, x < y -> x < x + 1.
Proof.
move=> [[x Px]] [[y Py]]; do !rewrite !/Ord.leq /=.
rewrite -!ltnNge !modz_nat !absz_nat !modn_mod.
case: (word_size t) Px Py => [|k Px Py Pxy] /=.
  by rewrite expn0 modn1; case: x y => [|x] [|y].
rewrite !modn_small ?(addn1, leqnn) //;
  try by rewrite -{1}(expn0 2) ltn_exp2l.
by apply: (@leq_trans y.+1).
Qed.

Definition range (l h : word) := [pred e | l <= e <= h].

Lemma addw_le : forall x y : word,
  x < y -> x + 1 <= y.
Proof.
move=> [[x Px]] [[y Py]]; do !rewrite !/Ord.leq /=.
rewrite -!ltnNge /= !modz_nat !absz_nat !modn_mod.
case: (word_size t) Px Py => [|k Px Py Pxy] /=.
  by rewrite expn0 modn1; case: x y => [|x] [|y].
rewrite !modn_small ?(addn1, leqnn) //;
  try by rewrite -{1}(expn0 2) ltn_exp2l.
by apply: (@leq_trans y.+1).
Qed.

End WithClasses.
