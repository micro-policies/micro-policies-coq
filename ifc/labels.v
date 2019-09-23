From mathcomp
Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope label_scope with lab.

Module Label.

Section ClassDef.

Record mixin_of T := Mixin {
  join : T -> T -> T;
  top  : T;
  bot  : T;
  _    : commutative join;
  _    : associative join;
  _    : idempotent join;
  _    : left_id bot join;
  _    : left_zero top join
}.

Record class_of T := Class {base : Choice.class_of T; mixin : mixin_of T}.
Local Coercion base : class_of >->  Choice.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack m :=
  fun b bT & phant_id (Choice.class bT) b => Pack (@Class T b m).

(* Inheritance *)
Definition eqType := @Equality.Pack cT xclass.

Definition choiceType := @Choice.Pack cT xclass.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> Choice.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Notation labType := type.
Notation labMixin := mixin_of.
Notation LabMixin := Mixin.
Notation LabType T m := (@pack T m _ _ id).
Notation "[ 'labType' 'of' T 'for' cT ]" :=  (@clone T cT _ idfun)
  (at level 0, format "[ 'labType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'labType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'labType'  'of'  T ]") : form_scope.
End Exports.

End Label.

Export Label.Exports.

Section Theory.

Local Open Scope label_scope.

Variable L : labType.

Implicit Types (l : L).

Definition join := Label.join (Label.class L).
Definition top := Label.top (Label.class L).
Definition bot := Label.bot (Label.class L).

Local Notation "l1 ⊔ l2" :=
  (join l1 l2) (at level 40, left associativity) : label_scope.
Local Notation "⊤" := top : label_scope.
Local Notation "⊥" := bot : label_scope.

Lemma joinC : commutative join.
Proof. by rewrite /join; case: (L)=> [? [? []]]. Qed.

Lemma joinA : associative join.
Proof. by rewrite /join; case: (L)=> [? [? []]]. Qed.

Lemma joinll : idempotent join.
Proof. by rewrite /join; case: (L)=> [? [? []]]. Qed.

Lemma joinBl : left_id ⊥ join.
Proof. by rewrite /bot /join; case: (L)=> [? [? []]]. Qed.

Lemma joinTl : left_zero ⊤ join.
Proof. by rewrite /top /join; case: (L)=> [? [? []]]. Qed.

Lemma joinlB : right_id ⊥ join.
Proof. by move=> l; rewrite joinC joinBl. Qed.

Lemma joinlT : right_zero ⊤ join.
Proof. by move=> l; rewrite joinC joinTl. Qed.

(* XXX: Should this be a notation? *)
Definition flows l1 l2 := l1 ⊔ l2 == l2.

Local Notation "l1 ⊑ l2" :=
  (flows l1 l2) (at level 50, no associativity) : label_scope.

Lemma flowsll : reflexive flows.
Proof. by move=> l; rewrite /flows joinll eqxx. Qed.

Lemma flows_trans : transitive flows.
Proof.
by move=> ???; rewrite /flows => /eqP e /eqP <-; rewrite joinA e.
Qed.

Lemma flows_antisym : antisymmetric flows.
Proof.
move=> l l'; rewrite /flows => /andP [/eqP e1 /eqP e2].
by rewrite -e2 joinC.
Qed.

Lemma flows_join l l1 l2 : (l1 ⊔ l2 ⊑ l) = (l1 ⊑ l) && (l2 ⊑ l).
Proof.
rewrite /flows; apply/(sameP idP)/(iffP andP).
  by case=> [e1 /eqP e2]; rewrite -joinA e2.
move=> /eqP e; rewrite -{}e 2!joinA joinll; split=> //.
by rewrite 2!joinA [l2 ⊔ _]joinC -3!joinA [l2 ⊔ _]joinA joinll.
Qed.

Lemma botP l : ⊥ ⊑ l.
Proof. by rewrite /flows joinBl. Qed.

Lemma topP l : l ⊑ ⊤.
Proof. by rewrite /flows joinlT. Qed.

End Theory.

Notation "l1 ⊔ l2" :=
  (join l1 l2) (at level 40, left associativity) : label_scope.
Notation "⊤" := (top _) : label_scope.
Notation "⊥" := (bot _) : label_scope.
Notation "l1 ⊑ l2" :=
  (flows l1 l2) (at level 50, no associativity) : label_scope.
