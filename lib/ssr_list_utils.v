Require Import Coq.Lists.List.
Require Import lib.utils.
Require Import ssreflect ssrfun ssrbool eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Theorem eq_op_is_equiv_dec (T : eqType) (x y : T) :
  x == y = SetoidDec.equiv_dec x y.
Proof. by case: (SetoidDec.equiv_dec _ _) => /= ?; apply/eqP. Qed.

Theorem inP (T : eqType) (x : T) (xs : seq T) : reflect (In x xs) (x \in xs).
Proof.
  case B: (x \in xs); constructor; move: B.
  - elim xs=> [// | /= x' xs' IH IN]; rewrite inE in IN; move/orP in IN.
    case: IN => [/eqP-> | IN].
    + by left.
    + by right; apply IH.
  - elim xs=> [_ [] | /= x' xs' IH NIN].
    rewrite inE in NIN; move/orP in NIN; contradict NIN.
    move: NIN => [-> | IN].
    + by left.
    + right; destruct (x \in xs'); first done.
      by exfalso; apply IH.
Qed.

Theorem uniqP (T : eqType) (xs : seq T) : reflect (NoDup xs) (uniq xs).
Proof.
  case U: (uniq xs); constructor; move: U.
  - elim xs=> [// | /= x xs' IH /andP [NIN U]]; constructor.
    + by move=> /inP ?; contradict NIN; move/negP.
    + by apply IH.
  - elim xs=> [// | /= x xs' IH NU ND].
    inversion ND as [|x' xs'' NIN ND']; subst.
    apply IH; last assumption.
    apply/negP; move/negP in NU; contradict NU; rename NU into U.
    apply/andP; split; last assumption.
    by move/inP in NIN.
Qed.

Definition rem_all {T : eqType} : T -> seq T -> seq T :=
  filter \o predC1.

(* This corollary's proof is so trivial, you'd think we could always use
   `rewrite mem_filter /=` instead.  That's true, but I'd rather have an actual
   lemma so that we're not dependent on implementation details. *)
Corollary in_rem_all (T : eqType) (a b : T) (xs : seq T) :
  a \in rem_all b xs = (a != b) && (a \in xs).
Proof. by rewrite mem_filter. Qed.

Fixpoint ofind T (p : pred T) (s : seq T) : option T :=
  match s with
  | [::] => None
  | x :: s => if p x then Some x else ofind p s
  end.
