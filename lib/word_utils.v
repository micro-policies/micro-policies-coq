From mathcomp Require Import
  ssreflect ssrbool ssrfun eqtype ssrnat fintype div ssrint intdiv.
From CoqUtils Require Import ord word.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section WordUtils.

Local Open Scope word_scope.
Local Open Scope ord_scope.

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

Lemma leqw_succ : forall n (x y : word n), x < y -> x < x + 1.
Proof.
move=> n [[x Px]] [[y Py]]; do !rewrite ?Ord.ltNge !/Ord.leq /=.
rewrite -!ltnNge !modz_nat !absz_nat !modn_mod.
case: n Px Py => [|k Px Py Pxy] /=.
  by rewrite expn0 modn1; case: x y => [|x] [|y].
rewrite !modn_small ?(addn1, leqnn) //;
  try by rewrite -{1}(expn0 2) ltn_exp2l.
by apply: (@leq_trans y.+1).
Qed.

Lemma addw_le : forall n (x y : word n),
  x < y -> x + 1 <= y.
Proof.
move=> n [[x Px]] [[y Py]]; do !rewrite ?Ord.ltNge !/Ord.leq /=.
rewrite -!ltnNge /= !modz_nat !absz_nat !modn_mod.
case: n Px Py => [|k Px Py Pxy] /=.
  by rewrite expn0 modn1; case: x y => [|x] [|y].
rewrite !modn_small ?(addn1, leqnn) //;
  try by rewrite -{1}(expn0 2) ltn_exp2l.
by apply: (@leq_trans y.+1).
Qed.

End WordUtils.
