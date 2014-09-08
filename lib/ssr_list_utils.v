Require Import Coq.Lists.List.
Require Import lib.list_utils.
Require Import ssreflect ssrfun ssrbool eqtype seq.

Set Bullet Behavior "Strict Subproofs".

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
