Require Import ssreflect ssrbool ssrfun eqtype.
Require Import ord partmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Pointwise.

Variables (T : ordType) (S1 S2 : Type).

Definition pointwise (P : S1 -> S2 -> Prop)
                     (m1 : {partmap T -> S1})
                     (m2 : {partmap T -> S2}) : Prop :=
  forall k,
    match m1 k, m2 k with
    | None   , None    => True
    | Some v1, Some v2 => P v1 v2
    | _      , _       => False
    end.

(* FIXME: replace by =i *)
Definition same_domain := pointwise (fun _ _ => True).

Lemma refine_get_pointwise_inv : forall P m1 m2 v2 k,
  pointwise P m1 m2 ->
  m2 k = Some v2 ->
  exists v1, m1 k = Some v1 /\ P v1 v2.
Proof.
move=> P m1 m2 v2 k /(_ k) ref sget.
rewrite {}sget in ref; move: ref.
by case: (m1 k) => //; eauto.
Qed.

Lemma pointwise_none : forall P m1 m2 k,
  pointwise P m1 m2 ->
  (m2 k = None <-> m1 k = None).
Proof.
move=> P m1 m2 k /(_ k) ref.
by split=> H; rewrite H in ref; move: ref; case: (getm _ _).
Qed.

Lemma pointwise_same_domain : forall P m1 m2,
  pointwise P m1 m2 ->
  same_domain m1 m2.
Proof.
unfold same_domain, pointwise. intros. specialize (H k).
destruct (getm m1 k) eqn:?; destruct (getm m2 k) eqn:?; tauto.
Qed.

Lemma refine_upd_pointwise2 P m1 m1' m2 m2' k v1 v2 :
  pointwise P m1 m2 ->
  P v1 v2 ->
  updm m1 k v1 = Some m1' ->
  updm m2 k v2 = Some m2' ->
  pointwise P m1' m2'.
Proof.
rewrite /updm; move=> pm1m2; move: (pm1m2 k).
case: (m1 k) => [v1'|] //; case: (m2 k) => [v2'|] //= _ pv1v2 [<-] [<-] k'.
move/(_ k'): pm1m2; rewrite !getm_set.
by case: (_ == _).
Qed.

Lemma refine_upd_pointwise P m1 m2 m2' k v1 v2 :
  pointwise P m1 m2 ->
  P v1 v2 ->
  updm m2 k v2 = Some m2' ->
  exists m1', updm m1 k v1 = Some m1' /\
              pointwise P m1' m2'.
Proof.
rewrite /updm; move=> pm1m2; move: (pm1m2 k).
case: (m2 k) => [v2'|] //; case: (m1 k) => [v1'|] //= _ pv1v2 [<-].
eexists; split; eauto=> k'.
by move/(_ k'): pm1m2; rewrite !getm_set; case: (_ == _).
Qed.

End Pointwise.

Section PartMapExtend.
(* We show that if P km is closed under a key map transformation
   (e.g. extension) then so is any pointwise (P km) *)

Variables K K1 K2 : ordType.
Variables V1 V2 : Type.
Variable P : {partmap K1 -> K2} -> V1 -> V2 -> Prop.
Variable f : {partmap K1 -> K2} -> K1 -> K2 -> Prop. (* condition on key_map (e.g. freshness) *)
Variable g : {partmap K1 -> K2} -> K1 -> K2 -> {partmap K1 -> K2}. (* key_map operation ( e.g. set) *)

Hypothesis p_extend_map : forall km k1 k2 v1 v2,
  f km k1 k2 ->
  P km v1 v2 ->
  P (g km k1 k2) v1 v2.

Lemma refine_extend_map km (m1 : {partmap K -> V1}) m2 k1 k2 :
  f km k1 k2 ->
  pointwise (P km) m1 m2 ->
  pointwise (P (g km k1 k2)) m1 m2.
Proof.
  move => cond ref k. specialize (ref k).
  destruct (getm m1 k); destruct (getm m2 k) => //.
  by auto using p_extend_map.
Qed.

End PartMapExtend.
