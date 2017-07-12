From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From CoqUtils Require Import hseq ord partmap word.
From MicroPolicies Require Import lib.utils common.types ifc.labels.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section CallFrame.

Variable mt : machine_types.
Variable L : labType.

Record call_frame := CallFrame {
  cf_pc   : atom (mword mt) L;
  cf_regs : {partmap reg mt -> atom (mword mt) L}
}.

Definition tuple_of_call_frame cf :=
  (cf_pc cf, cf_regs cf).

Definition call_frame_of_tuple cf :=
  let: (pc, regs) := cf in
  CallFrame pc regs.

Lemma tuple_of_call_frameK : cancel tuple_of_call_frame call_frame_of_tuple.
Proof. by case. Qed.

Definition call_frame_eqMixin := CanEqMixin tuple_of_call_frameK.
Canonical call_frame_eqType :=
  Eval hnf in EqType call_frame call_frame_eqMixin.

End CallFrame.

Fixpoint reap T p (s : seq T) : seq T :=
  if s is x :: s' then
    if p x then reap p s' else s
  else [::].

Section Indist.

Context {T : eqType} {L : labType}.
Variable t : T -> L.

Local Open Scope label_scope.

Definition indist rs (ra1 ra2 : T) :=
  (t ra1 ⊑ rs) || (t ra2 ⊑ rs) ==> (ra1 == ra2).

CoInductive indist_spec rs ra1 ra2 : Prop :=
| IndistLow of t ra1 ⊑ rs & t ra2 ⊑ rs & ra1 = ra2
| IndistHigh of ~~ (t ra1 ⊑ rs) & ~~ (t ra2 ⊑ rs).

Lemma indistP rs ra1 ra2 :
  reflect (indist_spec rs ra1 ra2) (indist rs ra1 ra2).
Proof.
rewrite /indist; apply/(iffP idP).
  have [hi /eqP <-|lo1] /= := boolP (t ra1 ⊑ rs); first by constructor.
  have [hi /eqP e|lo2 _] /= := boolP (t ra2 ⊑ rs).
    by rewrite e hi in lo1.
  by apply: IndistHigh.
case=> [-> -> -> //=|hi1 hi2].
by rewrite -[X in X ==> _]negbK negb_or hi1 hi2.
Qed.

Lemma indist_refl rl : reflexive (indist rl).
Proof. by move=> ra; rewrite /indist eqxx implybT. Qed.

Lemma indist_sym rl : symmetric (indist rl).
Proof. by move=> ra1 ra2; rewrite /indist orbC eq_sym. Qed.

Lemma indist_trans rl : transitive (indist rl).
Proof.
move=> ra2 ra1 ra3; rewrite /indist => e1 e2.
apply/implyP=> /orP [e|e].
  by move: e1 e2; rewrite e /= => /eqP <-; rewrite e => /eqP ->.
by move: e2 e1; rewrite e orbT /= => /eqP ->; rewrite e orbT /= => /eqP ->.
Qed.

End Indist.

Section IndistSeq.

Variables (T : Type) (R : T -> T -> Prop).

Fixpoint indist_seq (s1 s2 : seq T) :=
  match s1, s2 with
  | x1 :: s1', x2 :: s2' => R x1 x2 /\ indist_seq s1' s2'
  | [::], [::] => True
  | _, _ => False
  end.

Lemma indist_seq_sym :
  (forall x y, R x y -> R y x) ->
  (forall s1 s2, indist_seq s1 s2 -> indist_seq s2 s1).
Proof.
move=> sym.
elim=> [|x1 s1 IH] [|x2 s2] //= [/sym ??].
split=> //; exact: IH.
Qed.

Fixpoint indist_seq_prefix (s1 s2 : seq T) :=
  match s1, s2 with
  | x1 :: s1', x2 :: s2' => R x1 x2 /\ indist_seq_prefix s1' s2'
  | _, _ => True
  end.

Lemma indist_seq_prefix_sym :
  (forall x y, R x y -> R y x) ->
  (forall s1 s2, indist_seq_prefix s1 s2 -> indist_seq_prefix s2 s1).
Proof.
move=> sym.
elim=> [|x1 s1 IH] [|x2 s2] //= [/sym ??].
split=> //; exact: IH.
Qed.

Lemma indist_seq_cat s1 s1' s2 s2' :
  indist_seq s1 s2 ->
  indist_seq s1' s2' ->
  indist_seq (s1 ++ s1') (s2 ++ s2').
Proof.
elim: s1 s2 => [|x1 s1 IH] [|x2 s2] //= [hx hs hs'].
by split; eauto.
Qed.

Lemma indist_seq_cat_prefix s1 s1' s2 s2' :
  indist_seq s1 s2 ->
  indist_seq_prefix s1' s2' ->
  indist_seq_prefix (s1 ++ s1') (s2 ++ s2').
Proof.
elim: s1 s2 => [|x1 s1 IH] [|x2 s2] //= [hx hs hs'].
by split; eauto.
Qed.

Lemma indist_seq_prefix_sub s1 s1' s2 s2' :
  indist_seq_prefix (s1 ++ s1') (s2 ++ s2') ->
  indist_seq_prefix s1 s2.
Proof.
elim: s1 s2 => [|x1 s1 IH] [|x2 s2] //= [hx hs].
by eauto.
Qed.

End IndistSeq.
