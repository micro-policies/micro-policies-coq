From mathcomp Require Import
  ssreflect ssrbool ssrfun eqtype ssrnat fintype div ssrint intdiv.
From extructures Require Import ord.
From CoqUtils Require Import word.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section WordUtils.

Local Open Scope word_scope.
Local Open Scope ord_scope.

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
