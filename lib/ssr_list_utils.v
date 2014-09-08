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

Lemma mem_rem_weaken (T : eqType) (x y : T) (xs : seq T) :
  x \in rem y xs -> x \in xs.
Proof.
  elim: xs => [// | /= x' xs' IH]; rewrite inE.
  case (x' == y).
  - by move=> REM; rewrite REM orbT.
  - rewrite inE; move=> /orP [EQ | IN].
    + by rewrite EQ.
    + by apply IH in IN; rewrite IN orbT.
Qed.
       
Theorem in2_rem (T : eqType) (a b y : T) (xs : seq T) :
  In2 a b (rem y xs) -> In2 a b xs.
Proof.
  elim: xs=> [// | /= x xs' IH].
  case E: (x == y) => IN2; move/eqP: E; [move=> ?; subst | move=> NEQ].
  - by apply In2_there.
  - inversion IN2 as [rem_xs' IN | rem_xs' IN | x' rem_xs' IN2']; subst.
    + by apply In2_here_1;
         move/inP in IN; apply mem_rem_weaken in IN; apply /inP.
    + by apply In2_here_2;
         move/inP in IN; apply mem_rem_weaken in IN; apply /inP.
    + by apply In2_there, IH.
Qed.

Definition rem_all {T : eqType} : T -> seq T -> seq T :=
  filter \o predC1.
