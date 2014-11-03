Require Import List. Import ListNotations.
Require Import ssreflect ssrfun ssrbool eqtype.
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
  map_filter : forall V1 V2, (V1 -> option V2) -> M V1 -> M V2;
  remove : forall V, M V -> K -> M V;
  combine : forall V1 V2 V3, (option V1 -> option V2 -> option V3) -> M V1 -> M V2 -> M V3;
  empty : forall V, M V;
  (* The eqType is not strictly necessary, but it does make it more convenient to use those things *)
  is_empty : forall V : eqType, M V -> bool
}.

Class axioms (pm : partial_map) := mkAxioms {

  get_set_eq : forall V km ak (sk : V) , get (set km ak sk) ak = Some sk;

  get_set_neq : forall V km ak ak' (sk : V),
                  ak' <> ak  ->
                  get (set km ak sk) ak' = get km ak';

  map_filter_correctness : forall V1 V2 (f : V1 -> option V2) (m : M V1) (k : K),
                             get (map_filter f m) k = obind f (get m k);

  map_filter_set : forall V1 V2 (f : V1 -> V2) (m : M V1) (k : K) (v1 : V1),
                     map_filter (Some \o f) (set m k v1) =
                     set (map_filter (Some \o f) m) k (f v1);

  get_remove_eq : forall V km (ak : K), get (remove km ak) ak = None :> option V;

  get_remove_neq : forall V km ak ak', ak' <> ak -> get (remove km ak) ak' = get km ak' :> option V;

  get_combine : forall V1 V2 V3 (f : option V1 -> option V2 -> option V3),
                  f None None = None ->
                  forall m1 m2 k, get (combine f m1 m2) k = f (get m1 k) (get m2 k);

  get_empty : forall V k, get (empty V) k = None;

  is_emptyP : forall (V : eqType) (m : M V), ssrbool.reflect (m = empty V) (is_empty m)

}.

Section with_classes.

Context {pm : partial_map}
        {a : axioms pm}
        {V : Type}.

Definition rep (m : M V) (k : K) (f : V -> V) : option (M V) :=
  omap (set m k \o f) (get m k).

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

End with_classes.

End maps.

Section with_eqType.

Context (M : Type -> Type)
        (K : eqType)
        {pm : partial_map M K}
        {a : axioms pm}
        {V : Type}.

Lemma get_rep (m m' : M V) (k : K) f :
  rep m k f = Some m' ->
  forall k', get m' k' = if k' == k then omap f (get m k) else get m k'.
Proof.
  rewrite /rep.
  case: (get m k) => [v [<-]|] //= k'.
  have [{k'} ->|NE] := (k' =P k); first by rewrite get_set_eq.
  by rewrite (get_set_neq _ _ NE).
Qed.

Lemma get_upd (m m' : M V) k v :
  upd m k v = Some m' ->
  forall k', get m' k' = if k' == k then Some v else get m k'.
Proof.
  move=> Hupd k'.
  have [-> {k'}|Hneq] := k' =P k.
    by rewrite (get_upd_eq Hupd).
  by rewrite (get_upd_neq Hneq Hupd).
Qed.

End with_eqType.

Section upd_list.

Context (M : Type -> Type)
        (K : eqType)
        {pm : partial_map M K}
        {a : axioms pm}
        {V : Type}.

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
    have [EQ | /eqP NEQ] := altP (k =P k'); subst.
    + erewrite get_upd_eq in GET; eauto. inv GET. eauto.
    + erewrite (get_upd_neq NEQ) in GET; [|eauto].
      specialize (IH m'' erefl GET). intuition.
Qed.

Lemma defined_preserved m m' key key' (val val' : V) :
  get m key = Some val ->
  upd m key' val' = Some m' ->
  exists val'', get m' key = Some val''.
Proof.
  intros GET UPD.
  have [E | /eqP E] := altP (key =P key'); subst.
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
  In k (List.map (fun p => fst p) ps) ->
  exists v,
    In (k, v) ps /\ get m' k = Some v.
Proof.
  gdep m'.
  induction ps as [|[k' v] ps IH]; simpl; intros m' UPD IN; try solve [intuition].
  destruct (upd_list m ps) as [m''|] eqn:UPD'; try discriminate.
  destruct IN as [EQ | IN].
  - subst k'. eexists. split; eauto.
    erewrite get_upd_eq; eauto.
  - have [E | /eqP E] := altP (k =P k'); subst.
    + erewrite get_upd_eq; eauto.
    + erewrite get_upd_neq; eauto.
      destruct (IH m'' erefl IN) as (v' & IN' & GET).
      eauto.
Qed.

Lemma get_upd_list_nin m m' ps k :
  upd_list m ps = Some m' ->
  ~ In k (List.map (fun p => fst p) ps) ->
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
  (forall k, In k (List.map (fun p => fst p) ps) ->
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

End upd_list.

Section map.

Context {M : Type -> Type} {K : Type}
        {pm : partial_map M K} {a : axioms pm}
        {V1 V2 : Type} (f : V1 -> V2).

Definition map (m : M V1) : M V2 :=
  map_filter (Some \o f) m.

Lemma map_correctness m k : get (map m) k = omap f (get m k).
Proof.
  by rewrite /map map_filter_correctness /obind //=.
Qed.

Lemma map_upd (m : M V1) m' (k : K) v :
  upd m k v = Some m' ->
  upd (map m) k (f v) = Some (map m').
Proof.
  rewrite /upd map_correctness /map.
  case: (get m k) => [v'|] //= [<-] {m'}.
  by apply/esym/f_equal/map_filter_set.
Qed.

End map.

Section filter.

Context {M : Type -> Type} {K : Type}
        {pm : partial_map M K} {a : axioms pm}
        {V : Type} (f : V -> bool).

Definition filter (m : M V) : M V :=
  map_filter (fun x => if f x then Some x else None) m.

Lemma filter_correctness m k : get (filter m) k = option_filter f (get m k).
Proof.
  by rewrite /filter map_filter_correctness /obind /omap //=.
Qed.

End filter.

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
