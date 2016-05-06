From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

From CoqUtils Require Import ord partmap fset.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Pointwise.

Variables (T : ordType) (S1 S2 S3 : Type).

Definition pointwise (P : S1 -> S2 -> Prop)
                     (m1 : {partmap T -> S1})
                     (m2 : {partmap T -> S2}) : Prop :=
  forall k,
    match m1 k, m2 k with
    | None   , None    => True
    | Some v1, Some v2 => P v1 v2
    | _      , _       => False
    end.

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

Lemma pointwise_same_domain P m1 m2 :
  pointwise P m1 m2 ->
  domm m1 =i domm m2.
Proof.
move=> H k; move: {H} (H k); rewrite !mem_domm.
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
move/(_ k'): pm1m2; rewrite !setmE.
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
by move/(_ k'): pm1m2; rewrite !setmE; case: (_ == _).
Qed.

End Pointwise.

Section SameDomain.

Variables (T : ordType) (S1 S2 S3 : Type).

Lemma same_domain_trans (m : {partmap T -> S1}) (m' : {partmap T -> S2}) (m'' : {partmap T -> S3}) :
  domm m =i domm m' ->
  domm m' =i domm m'' ->
  domm m =i domm m''.
Proof. by move=> h1 h2 k; rewrite -h2. Qed.

Lemma same_domain_comm (m : {partmap T -> S1}) (m' : {partmap T -> S2}) :
  domm m =i domm m' -> domm m' =i domm m.
Proof. by move=> h k; rewrite h. Qed.

End SameDomain.

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

Section General.

Variables (T : ordType) (S : Type).

Implicit Type m : {partmap T -> S}.

Lemma updm_defined m key val val' :
  m key = Some val ->
  exists m',
    updm m key val' = Some m'.
Proof. rewrite /updm. move => -> /=. by eauto. Qed.

Lemma updm_inv m key val' m' :
  updm m key val' = Some m' ->
  exists val,
    m key = Some val.
Proof.
rewrite /updm; case: (m key) => [val _|//].
by eauto.
Qed.

Lemma getm_upd_eq m m' key val :
  updm m key val = Some m' ->
  m' key = Some val.
Proof.
rewrite /updm; case: (m key) => [val' [<-]|//].
by rewrite setmE eqxx.
Qed.

Lemma getm_upd_neq m m' (key key' : T) (val : S) :
  key' <> key ->
  updm m key val = Some m' ->
  m' key' = m key'.
Proof.
rewrite /updm; case: (m key) => [val'|] //= NEQ [<-].
by rewrite setmE (introF eqP NEQ).
Qed.

Lemma getm_upd m m' k v :
  updm m k v = Some m' ->
  forall k', m' k' = if k' == k then Some v else m k'.
Proof.
move=> Hupd k'.
have [-> {k'}|Hneq] := k' =P k.
  by rewrite (getm_upd_eq Hupd).
by rewrite (getm_upd_neq Hneq Hupd).
Qed.

Lemma filter_domains (f : S -> bool) m m' :
  domm m =i domm m' ->
  (forall k, match getm m k, getm m' k with
               | Some v, Some v' => f v = f v'
               | None, None => True
               | _, _ => False
             end) ->
  domm (filterm [fun _ => f] m : {partmap T -> S}) =i
  domm (filterm [fun _ => f] m' : {partmap T -> S}).
Proof.
move => SAME E k; do! rewrite mem_domm filtermE /=.
case GET: (getm m k) (E k) => [v|] {E} E;
case GET': (getm m' k) E => [v'|] E //=.
rewrite E.
by case: (f v').
Qed.

End General.
