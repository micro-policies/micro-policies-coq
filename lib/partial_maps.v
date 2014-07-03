Require Import List. Import ListNotations.
Require Import ssreflect ssrfun ssrbool eqtype.
Require Import Coq.Classes.SetoidDec.
Require Import lib.Coqlib lib.utils.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module PartMaps.

Section maps.

Variables (M : Type -> Type) (K : Type).

Class partial_map := {
  get : forall V, M V -> K -> option V;
  set : forall V, M V -> K -> V -> M V;
  filter : forall V, (V -> bool) -> M V -> M V;
  empty : forall V, M V
}.

Class axioms (pm : partial_map) := mkAxioms {

  get_set_eq : forall V km ak (sk : V) , get (set km ak sk) ak = Some sk;

  get_set_neq : forall V km ak ak' (sk : V),
                  ak' <> ak  ->
                  get (set km ak sk) ak' = get km ak';

  filter_correctness: forall V (f : V -> bool) (m : M V) (k : K),
                        get (filter f m) k = option_filter f (get m k)

  (* TODO: Need some axioms about empty! *)
}.

Section with_classes.

Context {pm : partial_map}
        {a : axioms pm}
        {eqk : EqDec (eq_setoid K)}
        {V : Type}.

Definition upd (m : M V) (k : K) (v : V) : option (M V) :=
  match get m k with
  | Some _ => Some (set m k v)
  | None => None
  end.

Lemma upd_defined m key val val' :
  get m key = Some val ->
  exists m',
    upd m key val' = Some m'.
Proof. rewrite /upd. move => ->. by eauto. Qed.

Lemma upd_inv m key val' m' :
  upd m key val' = Some m' ->
  exists val,
    get m key = Some val.
Proof.
  rewrite /upd.
  case: (get m key) => [val _|//].
  by eauto.
Qed.

Lemma get_upd_eq m m' key val :
  upd m key val = Some m' ->
  get m' key = Some val.
Proof.
  rewrite /upd.
  case: (get m key) => [val' [<-]|//].
  by apply get_set_eq.
Qed.

Lemma get_upd_neq m m' key key' val :
  key' <> key ->
  upd m key val = Some m' ->
  get m' key' = get m key'.
Proof.
  rewrite /upd => NEQ.
  case: (get m key) => [val' [<-]|//].
  by apply get_set_neq.
Qed.

Fixpoint upd_list (m : M V) (ps : list (K * V)) : option (M V) :=
  match ps with
  | [] => Some m
  | (k, v) :: ps' =>
    match upd_list m ps' with
    | Some m' => upd m' k v
    | None => None
    end
  end.

Lemma upd_list_inv m m' ps k v :
  upd_list m ps = Some m' ->
  get m' k = Some v ->
  In (k, v) ps \/ get m k = Some v.
Proof.
  gdep m'.
  induction ps as [|[k' v'] ps IH]; simpl; intros m' UPD GET.
  - simpl. inv UPD. auto.
  - destruct (upd_list m ps) as [m''|] eqn:UPD'; try discriminate.
    destruct (equiv_dec k k') as [E|E]; simpl in E; subst.
    + erewrite get_upd_eq in GET; eauto. inv GET. eauto.
    + erewrite (get_upd_neq E) in GET; [|eauto].
      specialize (IH m'' erefl GET). intuition.
Qed.

Lemma defined_preserved m m' key key' val val' :
  get m key = Some val ->
  upd m key' val' = Some m' ->
  exists val'', get m' key = Some val''.
Proof.
  intros GET UPD.
  destruct (equiv_dec key' key) as [E|E]; simpl in E; subst.
  - erewrite get_upd_eq; eauto.
  - erewrite get_upd_neq; eauto.
Qed.

Lemma upd_list_defined_preserved m m' key val ps :
  get m key = Some val ->
  upd_list m ps = Some m' ->
  exists val', get m' key = Some val'.
Proof.
  intros GET.
  gdep m'.
  induction ps as [|[k v] ps IH]; simpl; intros m' UPD.
  - inv UPD. eauto.
  - destruct (upd_list m ps) as [m'' | ] eqn:UPD'; try discriminate.
    destruct (IH _ erefl) as [v' GET'].
    eapply defined_preserved; eauto.
Qed.

Lemma get_upd_list_in m m' ps k :
  upd_list m ps = Some m' ->
  In k (map (fun p => fst p) ps) ->
  exists v,
    In (k, v) ps /\ get m' k = Some v.
Proof.
  gdep m'.
  induction ps as [|[k' v] ps IH]; simpl; intros m' UPD IN; try solve [intuition].
  destruct (upd_list m ps) as [m''|] eqn:UPD'; try discriminate.
  destruct IN as [EQ | IN].
  - subst k'. eexists. split; eauto.
    erewrite get_upd_eq; eauto.
  - destruct (equiv_dec k' k) as [E|E]; simpl in E; subst.
    + erewrite get_upd_eq; eauto.
    + erewrite get_upd_neq; eauto.
      destruct (IH m'' erefl IN) as (v' & IN' & GET).
      eauto.
Qed.

Lemma get_upd_list_nin m m' ps k :
  upd_list m ps = Some m' ->
  ~ In k (map (fun p => fst p) ps) ->
  get m' k = get m k.
Proof.
  gdep m'.
  induction ps as [|[k' v] ps IH]; simpl; intros m' UPD NIN.
  - now inv UPD.
  - destruct (upd_list m ps) as [m''|] eqn:UPD'; try discriminate.
    apply Decidable.not_or in NIN. destruct NIN as [NEQ NIN].
    rewrite <- (IH _ erefl); eauto.
    eapply get_upd_neq; eauto.
Qed.

Lemma upd_list_defined m ps :
  (forall k, In k (map (fun p => fst p) ps) ->
             exists v, get m k = Some v) ->
  exists m', upd_list m ps = Some m'.
Proof.
  induction ps as [|[k v] ps IH]; simpl; intros DEF; eauto.
  destruct IH as [m' UPD].
  - intros k' IN'. eapply DEF. eauto.
  - rewrite UPD.
    destruct (DEF k (or_introl erefl)) as [v' GET].
    destruct (upd_list_defined_preserved GET UPD) as [v'' GET'].
    eapply upd_defined; eauto.
Qed.

End with_classes.

End maps.

Section PartMapPointwise.

Context {M1 M2 : Type -> Type} {K V1 V2 : Type}
        {pm1 : partial_map M1 K}
        {pm1s : axioms pm1}
        {pm2 : partial_map M2 K}
        {pm2s : axioms pm2}.

Definition pointwise (P : V1 -> V2 -> Prop) (m1 : M1 V1) (m2 : M2 V2) : Prop :=
  forall k : K,
    match get m1 k, get m2 k with
    | None   , None   => True
    | Some v1, Some v2 => P v1 v2
    | _      , _      => False
    end.

Definition same_domain := pointwise (fun _ _ => True).

Lemma refine_get_pointwise_inv : forall P m1 m2 v2 k,
  (pointwise P) m1 m2 ->
  get m2 k = Some v2 ->
  exists v1, get m1 k = Some v1 /\ P v1 v2.
Proof.
  intros P m1 m2 v2 k ref sget.
  unfold pointwise in ref. specialize (ref k).
  rewrite sget in ref. destruct (get m1 k).
  + eexists; split; now trivial.
  + contradiction ref.
Qed.

Lemma pointwise_none : forall P m1 m2 k,
  (pointwise P) m1 m2 ->
  (get m2 k = None <-> get m1 k = None).
Proof.
  intros P m1 m2 k ref.
  pose proof (ref k).
  destruct (get m1 k) eqn:?; destruct (get m2 k) eqn:?; try tauto.
  split; intro X; discriminate X.
Qed.

Lemma pointwise_same_domain : forall P m1 m2,
  (pointwise P) m1 m2 ->
  same_domain m1 m2.
Proof.
  unfold same_domain, pointwise. intros. specialize (H k).
  destruct (get m1 k) eqn:?; destruct (get m2 k) eqn:?; tauto.
Qed.

End PartMapPointwise.

Section PartMapPointwiseUpd.

Context {M1 M2 : Type -> Type} {V1 V2 : Type}
        {K : eqType} (* need key equality to reason about updates *)
        {pm1 : partial_map M1 K}
        {pm1s : axioms pm1}
        {pm2 : partial_map M2 K}
        {pm2s : axioms pm2}.

Variable P : V1 -> V2 -> Prop.

Lemma refine_upd_pointwise1 : forall (m1 : M1 V1) (m2 m2' : M2 V2) k v1 v2,
  (pointwise P) m1 m2 ->
  P v1 v2 ->
  upd m2 k v2 = Some m2' ->
  exists m1', upd m1 k v1 = Some m1'.
Proof.
  intros m1 m2 m2' k v1 v2 ref pv1v2 up. pose proof up as up'.
  destruct (upd_inv up) as [v2' ge].
  destruct (refine_get_pointwise_inv ref ge) as [v1' [ge' _]].
  destruct (upd_defined v1 ge') as [m1' up''].
  exists m1'. exact up''.
Qed.

Lemma refine_upd_pointwise2 : forall (m1 m1' : M1 V1) (m2 m2' : M2 V2) k v1 v2,
  (pointwise P) m1 m2 ->
  P v1 v2 ->
  upd m1 k v1 = Some m1' ->
  upd m2 k v2 = Some m2' ->
  (pointwise P) m1' m2'.
Proof.
  intros m1 m1' m2 m2' k v1 v2 ref pv1v2 u1 u2.
  intro k'. have [<-|/eqP neq_kk'] := altP (k =P k').
  - erewrite get_upd_eq; try eassumption.
    erewrite get_upd_eq; eassumption.
  - erewrite (@get_upd_neq _ _ _ pm2s); [| | apply u2]; try congruence.
    erewrite (@get_upd_neq _ _ _ pm1s); [| | apply u1]; try congruence.
    by apply ref.
Qed.

Lemma refine_upd_pointwise : forall (m1 : M1 V1) (m2 m2' : M2 V2) k v1 v2,
  (pointwise P) m1 m2 ->
  P v1 v2 ->
  upd m2 k v2 = Some m2' ->
  exists m1', upd m1 k v1 = Some m1' /\
              (pointwise P) m1' m2'.
Proof.
  intros m1 m2 m2' k v1 v2 rr rv up.
  destruct (refine_upd_pointwise1 rr rv up) as [m1' up'].
  eauto using refine_upd_pointwise2.
Qed.

End PartMapPointwiseUpd.

Section PartMapExtend.

Context {M1 M2 M : Type -> Type}
        {V1 V2 K1 K2 : Type}
        {K : eqType} (* need key equality to reason about updates *)
        {pm1 : partial_map M1 K}
        {pm1s : axioms pm1}
        {pm2 : partial_map M2 K}
        {pm2s : axioms pm2}
        {pmk : partial_map M K1}
        {pmks : axioms pm2}.

(* We show that if P km is closed under a key map transformation
   (e.g. extension) then so is any pointwise (P km) *)

Variable P : M K2 -> V1 -> V2 -> Prop.
Variable f : M K2 -> K1 -> K2 -> Prop. (* condition on key_map (e.g. freshness) *)
Variable g : M K2 -> K1 -> K2 -> M K2.    (* key_map operation ( e.g. set) *)

Hypothesis p_extend_map : forall km k1 k2 v1 v2,
  f km k1 k2 ->
  P km v1 v2 ->
  P (g km k1 k2) v1 v2.

Lemma refine_extend_map : forall km (m1 : M1 V1) (m2 : M2 V2) k1 k2,
  f km k1 k2 ->
  (pointwise (P km)) m1 m2 ->
  (pointwise (P (g km k1 k2))) m1 m2.
Proof.
  move => km m1 m2 k1 k2 cond ref k. specialize (ref k).
  destruct (get m1 k); destruct (get m2 k) => //.
  by auto using p_extend_map.
Qed.

End PartMapExtend.

Section PartMapDomains.
Variables (M M' M'' : Type -> Type) (K V V' V'' : Type).

Context {pm : partial_map M K}
        {a : axioms pm}

        {pm' : partial_map M' K}
        {a' : axioms pm'}

        {pm'' : partial_map M'' K}
        {a'' : axioms pm''}.

Lemma same_domain_trans (m : M V) (m' : M' V') (m'' : M'' V'') :
  same_domain m m' ->
  same_domain m' m'' ->
  same_domain m m''.
Proof.
  intros SAME1 SAME2.
  intro k.
  assert (SAME1k := SAME1 k); clear SAME1.
  assert (SAME2k := SAME2 k); clear SAME2.
  destruct (get m k), (get m' k), (get m'' k); auto.
Qed.

Lemma same_domain_comm (m : M V) (m' : M' V') :
  same_domain m m' ->
  same_domain m' m.
Proof.
  intros SAME k;
  assert (SAMEk := SAME k);
  destruct (get m' k) eqn:GET;
  destruct (get m k) eqn:GET';
  auto.
Qed.

End PartMapDomains.

Section Filter.

Context {M : Type -> Type} {K V : Type}
        {pm : partial_map M K}
        {a : axioms pm}.

Lemma filter_domains (f : V -> bool) (m : M V) (m' : M V) :
  same_domain(*s*) m m' ->
  (forall k, match get m k, get m' k with
               | Some v, Some v' => f v = f v'
               | None, None => True
               | _, _ => False
             end) ->
  same_domain (filter f m) (filter f m').
Proof.
  move => SAME E k.
  do! rewrite filter_correctness.
  case GET: (get m k) (E k) => [v|] {E} E;
  case GET': (get m' k) E => [v'|] E //=.
  rewrite E.
  by case: (f v').
Qed.

End Filter.

Arguments empty {_ _ _ _}.

End PartMaps.
