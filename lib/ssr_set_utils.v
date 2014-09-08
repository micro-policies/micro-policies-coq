Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop fintype finset.

Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Theorem common_not_disjoint (T : finType) (x : T) (A B : {set T}) :
  x \in A -> x \in B -> ~~ [disjoint A & B].
Proof.
  move=> IN_A IN_B.
  rewrite -setI_eq0; apply/set0Pn; exists x.
  by rewrite in_setI; apply/andP.
Qed.
Arguments common_not_disjoint [T] x [A B] _ _.

Lemma bigcup_seq_in (S : eqType) (T : finType)
                    (t : T) (a : S) (A : seq S) (F : S -> {set T}) :
  a \in A -> t \in F a -> t \in \bigcup_(x <- A) F x.
Proof. by move=> IN_a IN_t; rewrite (big_rem a) //= inE IN_t. Qed.
Arguments bigcup_seq_in [S T t] a [A F] _ _.

Theorem bigcup_seqP (S : eqType) (T : finType)
                       (t : T) (A : seq S) (F : S -> {set T}) :
  reflect (exists a, a \in A /\ t \in F a) (t \in \bigcup_(x <- A) F x).
Proof.
  have [IN | NIN] := boolP (t \in \bigcup_(x <- A) F x); constructor.
  - elim: A IN => [| a A IH IN]; first by rewrite big_nil inE.
    rewrite big_cons in_setU in IN.
    case/orP: IN => [HERE | THERE].
    + by exists a; rewrite inE eq_refl.
    + case/IH: THERE => [a' [IN_A IN_Fa']].
      by exists a'; rewrite inE IN_A orbT.
  - move=> [a [IN_a IN_t]]; case/negP: NIN.
    elim: A IN_a => [// | a' A IH IN_a].
    rewrite big_cons inE; rewrite inE in IN_a; apply/orP.
    case/orP: IN_a => [/eqP EQ | IN_a]; first subst a'.
    + by left.
    + by right; apply IH.
Qed.
