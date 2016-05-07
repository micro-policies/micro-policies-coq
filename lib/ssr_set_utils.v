From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype ssrnat seq bigop fintype finset.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

(* For extraction -- `enum' is super slow when working with large `finType`s,
   but because it's implemented on top of `enum_mem', we can't just rewrite it
   for all sets. *)
Definition enum_set {T : finType} (s : {set T}) : seq T := enum s.
  (* Can't be eta-reduced -- `enum` is a weird abbreviation *)

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

Theorem subsetDU (T : finType) (A B : {set T}) :
  B \subset A -> A = A :\: B :|: B.
Proof. by move=> /setIidPr SUBSET; rewrite -{1}(setID A B) SUBSET setUC. Qed.

Theorem forall_subset (T : finType) (A B : {set T}) (P : T -> bool) :
  A \subset B -> [forall x in B, P x] -> [forall x in A, P x].
Proof.
  by move=> SUB ALL; apply/forall_inP => x IN;
     apply (elimT forall_inP ALL); apply (elimT subsetP SUB).
Qed.

Theorem forall_impl (T : finType) (A : {set T}) (P Q : T -> bool) :
  (forall x, P x -> Q x) -> [forall x in A, P x] -> [forall x in A, Q x].
Proof.
  by move=> IMPL ALL; apply/forall_inP => x IN;
     apply IMPL; apply (elimT forall_inP ALL).
Qed.
