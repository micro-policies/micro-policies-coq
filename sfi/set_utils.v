Require Import List Bool ZArith Sorted.
Require Import lib.Coqlib lib.utils lib.ordered sfi.list_utils.
Require Import Coq.Classes.SetoidDec.
Import ListNotations.
Local Open Scope bool_scope.

Generalizable Variables A.

(***** Sets of orderable things *****)

(*** Functions ***)

Section functions.

Context `{ord : Ordered A}.

(* *Strictly* ordered, so no duplicates. *)
Fixpoint is_set (xs : list A) : bool :=
  match xs with
    | []        => true
    | x1 :: xs' => match xs' with
                     | [] => true
                     | x2 :: xs'' => (x1 <? x2) && is_set xs'
                   end
  end.

Fixpoint insert_unique (y : A) (xs : list A) : list A :=
  match xs with
    | []       => [y]
    | x :: xs' => match x <=> y with
                    | Lt => x :: insert_unique y xs'
                    | Eq => x :: xs'
                    | Gt => y :: x :: xs'
                  end
  end.

Fixpoint to_set (xs : list A) : list A :=
  match xs with
    | []       => []
    | x :: xs' => insert_unique x (to_set xs')
  end.

Fixpoint set_elem (e : A) (xs : list A) : bool :=
  match xs with
    | []       => false
    | x :: xs' => match e <=> x with
                   | Lt => false
                   | Eq => true
                   | Gt => set_elem e xs'
                  end
  end.

Fixpoint set_delete (e : A) (xs : list A) : list A :=
  match xs with
    | []       => []
    | x :: xs' => match e <=> x with
                   | Lt => x :: xs'
                   | Eq => xs'
                   | Gt => x :: set_delete e xs'
                  end
  end.

Fixpoint set_union (xs ys : list A) : list A :=
  (* Bleh, lexicographic termination. *)
  (fix aux ys :=
     match xs , ys with
       | []       , ys'      => ys'
       | xs'      , []       => xs'
       | x :: xs' , y :: ys' => match x <=> y with
                                  | Lt => x :: set_union xs' (y :: ys')
                                  | Eq => x :: set_union xs' ys'
                                  | Gt => y :: aux ys'
                                end
     end) ys.

Fixpoint set_intersection (xs ys : list A) : list A :=
  (fix aux ys :=
     match xs , ys with
       | []       , _        => []
       | _        , []       => []
       | x :: xs' , y :: ys' => match x <=> y with
                                  | Lt => set_intersection xs' (y :: ys')
                                  | Eq => x :: set_intersection xs' ys'
                                  | Gt => aux ys'
                                end
     end) ys.

Fixpoint set_difference (xs ys : list A) : list A :=
  (fix aux ys :=
     match xs , ys with
       | []       , _        => []
       | xs'      , []       => xs'
       | x :: xs' , y :: ys' => match x <=> y with
                                  | Lt => x :: set_difference xs' (y :: ys')
                                  | Eq => set_difference xs' ys'
                                  | Gt => aux ys'
                                end
     end) ys.

Definition disjoint (xs ys : list A) : bool :=
  match set_intersection xs ys, xs, ys with
    | [] , [] , [] => false
    | [] , _  , _  => true
    | _  , _  , _  => false
  end.

End functions.

(*** Theorems ***)

(* The `by_set_extensionality` tactic uses the `set_specs` rewriting base.  We
   have to abstract it over `set_extensionality` to define it here; we twice,
   later, define the specialized version in terms of `set_extensionality`.  We
   have to do this twice so we can get it both inside and outside the
   section. *)
Ltac impl__by_set_extensionality set_extensionality_thm :=
  intros; apply set_extensionality_thm; auto; intros;
  autorewrite with set_specs; auto;
  try tauto.

Section theorems.

Context `{ord : Ordered A}.

Theorem is_set_tail : forall x xs,
  is_set (x :: xs) = true -> is_set xs = true.
Proof.
  simpl. destruct xs.
  - reflexivity.
  - rewrite andb_true_iff; destruct 1; assumption.
Qed.
(*Global*) Hint Resolve @is_set_tail.

Theorem is_set_tail_iff : forall x1 x2 xs,
  is_set (x1 :: x2 :: xs) = true <-> (x1 <? x2) && is_set (x2 :: xs) = true.
Proof. simpl; reflexivity. Qed.

Theorem is_set_iff_locally_sorted : forall xs,
  is_set xs = true <-> LocallySorted lt xs.
Proof.
  induction xs as [|x1 xs]; [|destruct xs as [|x2 xs]];
    split; try solve [simpl; auto].
  - intros H; apply andb_true_iff in H; destruct H as [Hlt His_set].
    constructor.
    + apply IHxs, His_set.
    + apply ltb_lt; assumption.
  - inversion_clear 1 as [ | | x1' x2' xs' Hsorted Hlt ].
    apply andb_true_iff; split.
    + apply ltb_lt; assumption.
    + apply IHxs, Hsorted.
Qed.

Corollary is_set_iff_sorted : forall xs,
  is_set xs = true <-> Sorted lt xs.
Proof.
  split; intro H;
  [ apply Sorted_LocallySorted_iff, is_set_iff_locally_sorted, H
  | apply is_set_iff_locally_sorted, Sorted_LocallySorted_iff, H ].
Qed.

Corollary is_set_iff_strongly_sorted : forall xs,
  is_set xs = true <-> StronglySorted lt xs.
Proof.
  split; intro H.
  - apply Sorted_StronglySorted.
    + red; apply lt_trans.
    + apply is_set_iff_sorted, H.
  - apply is_set_iff_sorted, StronglySorted_Sorted, H.
Qed.

Lemma delete_preserves_set : forall a xs,
  is_set xs = true ->
  is_set (delete a xs) = true.
Proof.
  intros; rewrite is_set_iff_strongly_sorted in *; auto.
Qed.
(*Global*) Hint Resolve @delete_preserves_set.

Theorem filter_preserves_set : forall p xs,
  is_set xs = true ->
  is_set (filter p xs) = true.
Proof.
  intros; rewrite is_set_iff_strongly_sorted in *; auto.
Qed.
(*Global*) Hint Resolve @filter_preserves_set.  

Theorem is_set_no_dups : forall xs,
  is_set xs = true -> NoDup xs.
Proof.
  induction xs as [|x1 xs]; intros His_set; constructor; eauto.
  simpl in *; destruct xs as [|x2 xs]; auto; simpl.
  apply andb_true_iff in His_set; destruct His_set as [Hlt His_set].
  destruct 1 as [Heq | HIn].
  - subst. contradict Hlt; apply not_true_iff_false, ltb_irrefl.
  - assert (HSorted' : StronglySorted lt (x2 :: xs)) by
      apply is_set_iff_strongly_sorted, His_set.
    inversion_clear HSorted' as [|x2' xs' HSorted Hall_lt].
    rewrite Forall_forall in Hall_lt.
    apply Hall_lt in HIn.
    apply ltb_lt in Hlt.
    eapply lt_asym; eassumption.
Qed.
(*Global*) Hint Resolve @is_set_no_dups.  

Lemma insert_unique_adds : forall y xs,
  In y (insert_unique y xs).
Proof.
  induction xs as [|x xs]; simpl; try destruct (x <=> y) eqn:?;
    auto using compare_eq.
Qed.
(*Global*) Hint Resolve @insert_unique_adds.

Lemma insert_unique_preserves : forall e y xs,
  In e xs -> In e (insert_unique y xs).
Proof.
  induction xs as [|x xs]; simpl; destruct 1; destruct (x <=> y); simpl; auto.
Qed.
(*Global*) Hint Resolve @insert_unique_preserves.

Lemma insert_unique_origin : forall e y xs,
  In e (insert_unique y xs) -> y = e \/ In e xs.
Proof.
  induction xs as [|x xs]; simpl; try destruct (x <=> y) eqn:cmp; auto.
  destruct 1 as [Heq | HIn]; auto.
  destruct (IHxs HIn); auto.
Qed.
(*Global*) Hint Resolve @insert_unique_origin.

Lemma insert_unique_spec : forall e y xs,
  In e (insert_unique y xs) <-> y = e \/ In e xs.
Proof. split; [|inversion 1; subst]; auto. Qed.
(*Global*) Hint Resolve @insert_unique_spec.

Lemma insert_unique_preserves_set_true : forall y xs,
  is_set xs = true -> is_set (insert_unique y xs) = true.
Proof.
  intros until 0; induction xs as [|x1 xs]; [reflexivity|].
  simpl; destruct xs as [|x2 xs].
  - destruct (x1 <=> y) eqn:cmp; simpl;
    try (unfold ltb; first [rewrite cmp | rewrite compare_asym, cmp]);
    reflexivity.
  - rewrite andb_true_iff; intros [Hlt His_set].
    destruct (x1 <=> y) eqn:cmp; simpl in *.
    + andb_true_split; assumption.
    + destruct (x2 <=> y) eqn:cmp2; andb_true_split; auto.
      apply ltb_lt; auto.
    + andb_true_split; auto.
      apply ltb_lt, gt__lt; auto.
Qed.
(*Global*) Hint Resolve @insert_unique_preserves_set_true.

Theorem to_set_set : forall xs, is_set (to_set xs) = true.
Proof. induction xs; simpl; auto. Qed.
(*Global*) Hint Resolve @to_set_set.

Theorem to_set_unchanged_sets : forall xs,
  is_set xs = true ->
  to_set xs = xs.
Proof.
  induction xs as [|x1 [|x2 xs]]; auto; simpl in *; intros SET.
  apply andb_true_iff in SET; destruct SET as [LT SET].
  rewrite IHxs; [|exact SET].
  simpl; unfold ltb in *.
  rewrite compare_asym; destruct (x1 <=> x2); simpl in *;
    first [reflexivity | congruence].
Qed.
(*Global*) Hint Resolve @to_set_unchanged_sets.
  
Theorem is_set_from_to_set : forall xs,
  is_set xs = true <-> exists xs', xs = to_set xs'.
Proof.
  split.
  - exists xs. symmetry; auto.
  - intros [xs' EQ]; subst.
    rewrite to_set_set; simpl; trivial.
Qed.

Theorem to_set_elts : forall y xs, In y xs <-> In y (to_set xs).
Proof.
  induction xs as [|x xs]; [reflexivity|].
  simpl; split.
  - intros [Heq | HIn]; subst; auto.
    apply insert_unique_preserves, IHxs, HIn.
  - intros HIn; destruct (insert_unique_origin _ _ _ HIn); [left|right]; auto.
    apply IHxs; assumption.
Qed.

Theorem to_set_involutive : forall xs, to_set (to_set xs) = to_set xs.
Proof. induction xs; simpl; auto. Qed.
(*Global*) Hint Resolve @to_set_involutive.

Lemma is_set_head : forall x0 xs y0 ys,
  (forall a, In a (x0 :: xs) <-> In a (y0 :: ys)) ->
  is_set (x0 :: xs) = true -> is_set (y0 :: ys) = true ->
  x0 = y0.
Proof.
  intros until 0; intros SAME SET_xs SET_ys;
    apply is_set_iff_strongly_sorted in SET_xs;
    apply is_set_iff_strongly_sorted in SET_ys.
  idtac;
    inversion SET_xs as [|x0' xs' SORTED_xs ALL_xs];
    inversion SET_ys as [|y0' ys' SORTED_ys ALL_ys];
    subst.
  rewrite Forall_forall in *.
  destruct (x0 == y0) as [EQ | NEQ]; auto.
  simpl in SAME.
  specialize ALL_xs with y0; specialize ALL_ys with x0.
  lapply ALL_xs; [lapply ALL_ys; [intros; eelim lt_asym; eassumption|]|];
    [specialize SAME with x0 | specialize SAME with y0];
    destruct SAME as [SUBSET_xs_ys SUBSET_ys_xs];
    [lapply SUBSET_xs_ys | lapply SUBSET_ys_xs];
    auto; (destruct 1; [scongruence|]); auto.
Qed.
(*Global*) Hint Resolve @is_set_head.

Ltac extensional_nil_cons_contradict :=
  match goal with
    | [SAME : forall a, In a ?xs <-> In a ?ys |- _] =>
      first [specialize_with_head SAME xs | specialize_with_head SAME ys];
      destruct SAME;
      not_subset_cons_nil
  end.      

Theorem set_extensionality : forall xs ys,
  (forall a, In a xs <-> In a ys) ->
  is_set xs = true -> is_set ys = true ->
  xs = ys.
Proof.
  induction xs as [|x xs]; intros ys SAME SET_xs SET_ys.
  - destruct ys as [|y ys]; [auto | extensional_nil_cons_contradict].
  - destruct ys as [|y ys]; [extensional_nil_cons_contradict|].
    assert (EQ : x = y) by eauto 2; subst y.
    f_equal; apply IHxs; eauto.
    intros z; specialize SAME with z; simpl in SAME.
    assert (NEQ : forall ws, is_set (x :: ws) = true -> In z ws -> x <> z) by
      (intros; apply in2_nodup_neq with (x :: ws); eauto).
    split; [specialize NEQ with xs | specialize NEQ with ys]; tauto.
Qed.
(*Global*) Hint Resolve @set_extensionality.
Ltac by_set_extensionality := impl__by_set_extensionality set_extensionality.

Theorem set_elem_cases : forall e xs,
  is_set xs = true -> if set_elem e xs then In e xs else ~ In e xs.
Proof.
  induction xs as [|x1 xs]; intros SET; simpl; auto.
  destruct (e <=> x1) eqn:CMP.
  - apply compare_eq in CMP; subst; auto.
  - intros [-> | IN].
    + eelim lt_irrefl; exact CMP.
    + apply is_set_iff_strongly_sorted in SET;
        inversion SET as [|x1' xs' SS ALL]; subst; rewrite Forall_forall in ALL.
      specialize (ALL _ IN); elim (lt_irrefl e); eauto 2 with ordered.
  - assert (x1 <> e) by (intros ->; eelim gt_irrefl; exact CMP).
    destruct (set_elem e xs), xs; try tauto;
      simpl in SET; rewrite andb_true_iff in SET; destruct SET; tauto.
Qed.

Corollary set_elem_true : forall e xs,
  is_set xs = true -> (set_elem e xs = true <-> In e xs).
Proof.
  intros e xs SET; apply set_elem_cases with (e := e) in SET.
  destruct (set_elem e); intuition.
Qed.

Corollary set_elem_false : forall e xs,
  is_set xs = true -> (set_elem e xs = false <-> ~ In e xs).
Proof.
  intros e xs SET; apply set_elem_cases with (e := e) in SET.
  destruct (set_elem e); intuition.
Qed.

Corollary set_elem_is_elem : forall e xs,
  is_set xs = true -> (set_elem e xs = proj_sumbool (elem e xs)).
Proof.
  intros e xs SET; apply set_elem_cases with (e := e) in SET.
  destruct (set_elem e xs), (elem e xs); solve [reflexivity | contradiction].
Qed.

Theorem set_delete_is_delete : forall e xs,
  is_set xs = true -> set_delete e xs = delete e xs.
Proof.
  induction xs as [|x xs]; intros SET; [reflexivity|].
  simpl; destruct (e <=> x) eqn:CMP.
  - apply compare_eq in CMP; subst.
    destruct (equiv_dec x x); [|congruence].
    symmetry; apply delete_not_in.
    apply is_set_no_dups in SET; inversion SET; assumption.
  - destruct (equiv_dec e x); [ssubst; elim (lt_irrefl x); exact CMP|].
    f_equal; symmetry; apply delete_not_in.
    apply is_set_iff_strongly_sorted in SET; inversion SET; subst;
      rewrite Forall_forall in *.
    intros IN; elim (lt_irrefl x); eauto 3 with ordered.
  - destruct (equiv_dec e x); [ssubst; elim (gt_irrefl x); exact CMP|].
    f_equal; apply IHxs; eauto.
Qed.

Corollary set_delete_spec : forall a e xs,
  is_set xs = true ->
  (In a (set_delete e xs) <-> a <> e /\ In a xs).
Proof. intros; rewrite set_delete_is_delete by auto; apply delete_in_iff. Qed.
Hint Rewrite @set_delete_spec : set_specs.

Theorem set_delete_preserves_set : forall e xs,
  is_set xs = true -> is_set (set_delete e xs) = true.
Proof.
  induction xs as [|x xs]; intros SET; [reflexivity | simpl].
  destruct (e <=> x) eqn:CMP; eauto 2.
  simpl; rewrite IHxs by eauto 2.
  destruct (set_delete e xs) as [|d ds] eqn:DEL;
    [reflexivity | rewrite andb_true_r].
  assert (In d xs). {
    assert (IN : In d (set_delete e xs)) by (rewrite DEL; auto).
    rewrite set_delete_spec in IN by eauto 2; tauto.
  }
  apply is_set_iff_strongly_sorted in SET; inversion SET; subst;
    rewrite Forall_forall in *; apply ltb_lt; auto.
Qed.
(*Global*) Hint Resolve @set_delete_preserves_set.

(* I could add corollaries that repeat the theorems about `delete`, but we don't
   use `set_delete` enough to be worth it; we can just rewrite with
   `set_delete_is_delete` when we want to use them. *)

Theorem set_union_spec : forall a xs ys,
  In a (set_union xs ys) <-> In a xs \/ In a ys.
Proof.
  induction xs as [|x xs].
  - intros []; simpl; tauto.
  - induction ys as [|y ys]; simpl; [tauto|].
    destruct (x <=> y) eqn:CMP; simpl;
    (split; [ intros [EQ | IN]; [|try apply IHxs in IN]; tauto
            | try apply compare_eq in CMP; subst;
              intros [[EQ | IN_xs] | [EQ | IN_ys]]; subst; simpl in *;
              solve [tauto | right; apply IHxs; auto 4] ]).
Qed.
(*Global*) Hint Rewrite @set_union_spec : set_specs.

Theorem set_union_preserves_set : forall xs ys,
  is_set xs = true -> is_set ys = true ->
  is_set (set_union xs ys) = true.
Proof.
  induction xs as [|x xs]; intros ys SET_xs SET_ys; induction ys as [|y ys];
    try assumption.
  simpl; destruct (x <=> y) eqn:CMP; simpl.
  - apply compare_eq in CMP; subst.
    rewrite IHxs by eauto.
    destruct (set_union xs ys) as [|e U] eqn:UNION; [reflexivity|].
    assert (IN : In e xs \/ In e ys) by
      (rewrite <- set_union_spec, UNION; left; reflexivity).
    rewrite is_set_iff_strongly_sorted in SET_xs,SET_ys;
      inversion SET_xs; inversion SET_ys; subst;
      rewrite Forall_forall in *.
    rewrite andb_true_r, ltb_lt; destruct IN; auto.
  - fold (x < y) in CMP.
    rewrite IHxs by eauto.
    destruct (set_union xs (y :: ys)) as [|e U] eqn:UNION; [reflexivity|].
    assert (IN : In e xs \/ In e (y :: ys)) by
      (rewrite <- set_union_spec, UNION; left; reflexivity).
    rewrite is_set_iff_strongly_sorted in SET_xs,SET_ys;
      inversion SET_xs; inversion SET_ys; subst;
      rewrite Forall_forall in *.
    rewrite andb_true_r, ltb_lt; destruct IN as [|[|]]; eauto 3 with ordered.
  - fold (x > y) in CMP; apply lt_iff_gt in CMP; destruct ys as [|y' ys].
    + rewrite SET_xs, andb_true_r, ltb_lt; exact CMP.
    + simpl in *; apply andb_true_iff in SET_ys;
        destruct SET_ys as [LT_ys SET_ys].
      rewrite IHys by exact SET_ys.
      destruct (x <=> y') eqn:CMP'; rewrite andb_true_r;
        solve [exact LT_ys | apply ltb_lt; exact CMP].
Qed.
(*Global*) Hint Resolve @set_union_preserves_set.

Theorem set_union_subset_id : forall xs ys,
  is_set xs = true -> is_set ys = true ->
  (forall a, In a xs -> In a ys) ->
  set_union xs ys = ys.
Proof.
  intros xs ys SET_xs SET_ys SUBSET; apply set_extensionality; eauto 2.
  intros a; specialize SUBSET with a; rewrite set_union_spec.
  tauto.
Qed.
(*Global*) Hint Resolve @set_union_subset_id.

Theorem set_union_self_id : forall xs,
  set_union xs xs = xs.
Proof.
  induction xs; simpl.
  - reflexivity.
  - rewrite compare_refl. rewrite <- IHxs at 3. reflexivity.
Qed.
(*Global*) Hint Resolve @set_union_self_id.
  
Theorem set_union_nil_l : forall xs,
  set_union [] xs = xs.
Proof. destruct xs; reflexivity. Qed.
(*Global*) Hint Resolve @set_union_nil_l.

Theorem set_union_nil_r : forall xs,
  set_union xs [] = xs.
Proof. destruct xs; reflexivity. Qed.
(*Global*) Hint Resolve @set_union_nil_r.

Theorem set_union_comm : forall xs ys,
  is_set xs = true -> is_set ys = true ->
  set_union xs ys = set_union ys xs.
Proof. by_set_extensionality. Qed.
(*Global*) Hint Resolve @set_union_comm.

Theorem set_union_assoc : forall xs ys zs,
  is_set xs = true -> is_set ys = true -> is_set zs = true ->
  set_union xs (set_union ys zs) =
  set_union (set_union xs ys) zs.
Proof. by_set_extensionality. Qed.
(*Global*) Hint Resolve @set_union_assoc.

Theorem set_intersection_spec : forall a xs ys,
  is_set xs = true -> is_set ys = true ->
  (In a (set_intersection xs ys) <-> In a xs /\ In a ys).
Proof.
  induction xs as [|x xs].
  - intros []; simpl; tauto.
  - induction ys as [|y ys]; [simpl; tauto | intros SET_xs SET_ys; simpl].
    destruct (x <=> y) eqn:CMP; simpl;
      [ apply compare_eq in CMP; subst
      | fold (x < y) in CMP
      | fold (x > y) in CMP ];
      first [rewrite IHxs by eauto | rewrite IHys by eauto]; simpl;
      (split; [tauto|]);
      intros [[EQ_x | IN_xs] [EQ_y | IN_ys]]; subst;
      first [ eelim lt_irrefl; exact CMP
            | eelim gt_irrefl; exact CMP
            | auto].
    + apply is_set_iff_strongly_sorted in SET_ys.
      inversion SET_ys; subst; rewrite Forall_forall in *.
      elim (lt_irrefl a); eauto with ordered.
    + apply is_set_iff_strongly_sorted in SET_xs.
      inversion SET_xs; subst; rewrite Forall_forall in *.
      elim (lt_irrefl a); eauto with ordered.
Qed.
(*Global*) Hint Rewrite @set_intersection_spec : set_specs.

Theorem set_intersection_preserves_set : forall xs ys,
  is_set xs = true -> is_set ys = true ->
  is_set (set_intersection xs ys) = true.
Proof.
  induction xs as [|x xs]; intros ys SET_xs SET_ys; induction ys as [|y ys];
    try assumption.
  simpl; destruct (x <=> y) eqn:CMP; simpl.
  - apply compare_eq in CMP; subst.
    rewrite IHxs by eauto.
    destruct (set_intersection xs ys) as [|e I] eqn:INTERSECTION;
      [reflexivity|].
    assert (IN : In e xs /\ In e ys) by
      (rewrite <- set_intersection_spec, INTERSECTION; eauto 3).
    rewrite is_set_iff_strongly_sorted in SET_xs;
      inversion SET_xs; subst;
      rewrite Forall_forall in *.
    rewrite andb_true_r, ltb_lt; destruct IN; auto.
  - apply IHxs; eauto.
  - apply IHys; eauto.
Qed.
(*Global*) Hint Resolve @set_intersection_preserves_set.

Theorem set_intersection_subset_id : forall xs ys,
  is_set xs = true -> is_set ys = true ->
  (forall a, In a xs -> In a ys) ->
  set_intersection xs ys = xs.
Proof.
  induction xs as [|x xs]; [destruct ys; reflexivity|];
    intros ys SET_xs SET_ys SUBSET; simpl.
  induction ys as [|y ys]; [specialize SUBSET with x; elim SUBSET; auto|].
  destruct (x <=> y) eqn:CMP.
  - apply compare_eq in CMP; subst.
    f_equal; apply IHxs; eauto 2.
    simpl in SUBSET.
    intros a IN_xs; specialize SUBSET with a.
    assert (y <> a) by
      (intros <-; apply is_set_no_dups in SET_xs;
       inversion SET_xs; contradiction).
    tauto.
  - fold (x < y) in CMP.
    assert (y <> x) by (intros ->; eelim lt_irrefl; exact CMP).
    apply is_set_iff_strongly_sorted in SET_ys;
      inversion SET_ys; subst; rewrite Forall_forall in *.
    assert (In x ys) by (specialize SUBSET with x; simpl in SUBSET; tauto).
    elim (lt_irrefl x); eauto 3 with ordered.
  - fold (x > y) in CMP; apply lt_iff_gt in CMP.
    apply IHys; eauto 2.
    intros a [EQ | IN]; subst;
      (assert (y <> a); [|specialize SUBSET with a; simpl in SUBSET; tauto]).
    + intros ->; eelim lt_irrefl; exact CMP.
    + intros ->.
      apply is_set_iff_strongly_sorted in SET_xs;
        inversion SET_xs; subst; rewrite Forall_forall in *.
      elim (lt_irrefl x); eauto 3 with ordered.
Qed.
(*Global*) Hint Resolve @set_intersection_subset_id.

Theorem set_intersection_self_id : forall xs,
  set_intersection xs xs = xs.
Proof.
  induction xs; simpl.
  - reflexivity.
  - rewrite compare_refl, IHxs; reflexivity.
Qed.
(*Global*) Hint Resolve @set_intersection_self_id.
  
Theorem set_intersection_nil_l : forall xs,
  set_intersection [] xs = [].
Proof. destruct xs; reflexivity. Qed.
(*Global*) Hint Resolve @set_intersection_nil_l.

Theorem set_intersection_nil_r : forall xs,
  set_intersection xs [] = [].
Proof. destruct xs; reflexivity. Qed.
(*Global*) Hint Resolve @set_intersection_nil_r.

Theorem set_intersection_comm : forall xs ys,
  is_set xs = true -> is_set ys = true ->
  set_intersection xs ys = set_intersection ys xs.
Proof. by_set_extensionality. Qed.
(*Global*) Hint Resolve @set_intersection_comm.

Theorem set_intersection_assoc : forall xs ys zs,
  is_set xs = true -> is_set ys = true -> is_set zs = true ->
  set_intersection xs (set_intersection ys zs) =
  set_intersection (set_intersection xs ys) zs.
Proof. by_set_extensionality. Qed.
(*Global*) Hint Resolve @set_intersection_assoc.

(* This comes first because it doesn't need the full force of the spec. *)
Theorem set_difference_preserves_set : forall xs ys,
  is_set xs = true ->
  is_set (set_difference xs ys) = true.
Proof.
  induction xs as [|x xs]; [intros []; auto | intros ys SET_xs; simpl].
  induction ys as [|y ys]; [auto | simpl].
  destruct (x <=> y).
  - apply IHxs; eauto.
  - simpl. rewrite IHxs; eauto 2.
    destruct (set_difference xs (y :: ys)) as [|e D] eqn:DIFFERENCE;
      [reflexivity | rewrite andb_true_r].
    assert (LEMMA : forall x0 xs,  is_set (x0 :: xs) = true ->
                    forall ys e D, set_difference xs ys = e :: D ->
                      x0 <? e = true). {
      clear.
      induction xs as [|x xs]; intros SET_xs;
        [destruct ys; discriminate | simpl].
      induction ys as [|y ys]; intros e D DIFFERENCE.
      - inversion DIFFERENCE; subst.
        rewrite is_set_tail_iff, andb_true_iff in SET_xs;
          destruct SET_xs; assumption.
      - destruct (x <=> y) eqn:CMP.
        + apply IHxs with ys D; eauto 2.
          simpl in SET_xs; rewrite andb_true_iff in SET_xs.
          simpl; destruct xs; [reflexivity|].
          rewrite andb_true_iff in *; repeat invh and; split;
            [eauto 2 with ordered|assumption].
        + inversion DIFFERENCE; subst; clear DIFFERENCE.
          rewrite is_set_tail_iff, andb_true_iff in SET_xs;
            destruct SET_xs; assumption.
        + apply IHys in DIFFERENCE; eauto 2.
    }
    eapply LEMMA; eassumption.
  - apply IHys.
Qed.
(*Global*) Hint Resolve @set_difference_preserves_set.

Theorem set_difference_spec : forall e xs ys,
  is_set xs = true -> is_set ys = true ->
  (In e (set_difference xs ys) <-> In e xs /\ ~ In e ys).
Proof.
  induction xs as [|x xs]; [intros []; tauto|].
  induction ys as [|y ys]; [tauto | intros SET_xs SET_ys; simpl].
  destruct (x <=> y) eqn:CMP.
  - apply compare_eq in CMP; subst.
    split; [intros IN | intros SPEC].
    + apply IHxs in IN; eauto 2. split; [tauto|].
      intros [-> | IN']; [|tauto].
      apply is_set_no_dups in SET_xs; inversion SET_xs; tauto.
    + apply IHxs; eauto 2; tauto.
  - split; [intros [-> | IN] | intros [[-> | IN] NOT_EQ_IN]].
    + split; auto.
      intros [-> | IN]; [elim (lt_irrefl e); exact CMP|].
      apply is_set_iff_strongly_sorted in SET_ys; inversion SET_ys; subst;
        rewrite Forall_forall in *.
      elim (lt_irrefl e); eauto 3 with ordered.
    + apply IHxs in IN; solve [eauto 2 | simpl in IN; tauto].
    + auto.
    + right. apply IHxs; solve [eauto 2 | simpl; tauto].
  - rewrite IHys by eauto 2. simpl; split; [|tauto].
    intros [[-> | IN] NOT_IN].
    + assert (y <> e) by (intros ->; eelim gt_irrefl; exact CMP); tauto.
    + split; [tauto | intros [-> | IN']; [|contradiction]].
      apply lt_iff_gt in CMP.
      apply is_set_iff_strongly_sorted in SET_xs; inversion SET_xs; subst;
        rewrite Forall_forall in *.
      elim (lt_irrefl e); eauto 3 with ordered.
Qed.
(*Global*) Hint Rewrite @set_difference_spec : set_specs.

Theorem set_difference_origin : forall e xs ys,
  In e (set_difference xs ys) -> In e xs.
Proof.
  induction xs as [|x xs]; simpl; auto; induction ys as [|y ys]; simpl; auto.
  destruct (x <=> y) eqn:CMP; intros IN.
  - apply compare_eq in CMP; subst.
    right; eapply IHxs; exact IN.
  - simpl in IN; destruct IN as [EQ | IN]; [left; exact EQ | right].
    eapply IHxs; exact IN.
  - apply IHys; exact IN.
Qed.
(*Global*) Hint Resolve @set_difference_origin.

Theorem set_difference_removes : forall e xs ys,
  is_set xs = true -> is_set ys = true ->
  In e (set_difference xs ys) -> ~ In e ys.
Proof. intros. apply set_difference_spec with xs; assumption. Qed.
(*Global*) Hint Resolve @set_difference_removes.

Theorem set_difference_subset_annihilating : forall xs ys,
  is_set xs = true -> is_set ys = true ->
  (forall a, In a xs -> In a ys) ->
  set_difference xs ys = [].
Proof.
  by_set_extensionality.
  simpl; match goal with a : A, H : A -> _ |- _ => specialize (H a) end; tauto.
Qed.
(*Global*) Hint Resolve @set_difference_subset_annihilating.

Theorem set_difference_self_annihilating : forall xs,
  set_difference xs xs = [].
Proof.
  induction xs as [|x xs]; simpl; [reflexivity|].
  rewrite compare_refl; assumption.
Qed.
(*Global*) Hint Resolve @set_difference_self_annihilating.
  
Theorem set_difference_nil_l : forall xs,
  set_difference [] xs = [].
Proof. destruct xs; reflexivity. Qed.
(*Global*) Hint Resolve @set_difference_nil_l.

Theorem set_difference_nil_r : forall xs,
  set_difference xs [] = xs.
Proof. destruct xs; reflexivity. Qed.
(*Global*) Hint Resolve @set_intersection_nil_r.

Theorem set_union_intersection_distrib : forall xs ys zs,
  is_set xs = true -> is_set ys = true -> is_set zs = true ->
  set_union (set_intersection xs ys) zs =
  set_intersection (set_union xs zs) (set_union ys zs).
Proof. by_set_extensionality. Qed.
(*Global*) Hint Resolve @set_union_intersection_distrib.

Theorem set_intersection_union_distrib : forall xs ys zs,
  is_set xs = true -> is_set ys = true -> is_set zs = true ->
  set_intersection (set_union xs ys) zs =
  set_union (set_intersection xs zs) (set_intersection ys zs).
Proof. by_set_extensionality. Qed.
(*Global*) Hint Resolve @set_intersection_union_distrib.

Theorem set_union_difference_distrib : forall xs ys zs,
  is_set xs = true -> is_set ys = true -> is_set zs = true ->
  set_union (set_difference xs ys) zs =
  set_difference (set_union xs zs) (set_difference ys zs).
Proof.
  by_set_extensionality.
  match goal with e : A |- _ =>
  generalize (bool_dec (set_elem e zs) true); intros ELEM;
  assert ({In e zs} + {~ In e zs}) by
    (destruct ELEM;
       [ left; apply set_elem_true; assumption
       | right; apply set_elem_false; [|apply not_true_iff_false]; assumption ])
  end;
  tauto.
Qed.
(*Global*) Hint Resolve @set_union_difference_distrib.

Theorem set_difference_union_distrib : forall xs ys zs,
  is_set xs = true -> is_set ys = true -> is_set zs = true ->
  set_difference (set_union xs ys) zs =
  set_union (set_difference xs zs) (set_difference ys zs).
Proof. by_set_extensionality. Qed.
(*Global*) Hint Resolve @set_difference_union_distrib.

Theorem set_difference_union_collapse : forall xs ys zs,
  is_set xs = true -> is_set ys = true -> is_set zs = true ->
  set_difference (set_union xs zs) (set_union ys zs) =
  set_difference (set_difference xs ys) zs.
Proof. by_set_extensionality. Qed.
(*Global*) Hint Resolve @set_difference_union_collapse.

Theorem set_intersection_difference_distrib : forall xs ys zs,
  is_set xs = true -> is_set ys = true -> is_set zs = true ->
  set_intersection (set_difference xs ys) zs =
  set_difference (set_intersection xs zs) (set_intersection ys zs).
Proof. by_set_extensionality. Qed.
(*Global*) Hint Resolve @set_intersection_difference_distrib.

Theorem set_difference_intersection_distrib : forall xs ys zs,
  is_set xs = true -> is_set ys = true -> is_set zs = true ->
  set_difference (set_intersection xs ys) zs =
  set_intersection (set_difference xs zs) (set_difference ys zs).
Proof. by_set_extensionality. Qed.
(*Global*) Hint Resolve @set_difference_intersection_distrib.

Theorem disjoint_irrefl : forall xs,
  disjoint xs xs = false.
Proof.
  now intros; unfold disjoint; rewrite set_intersection_self_id; destruct xs.
Qed.
(*Global*) Hint Resolve @disjoint_irrefl.

Theorem disjoint_comm : forall xs ys,
  is_set xs = true -> is_set ys = true ->
  disjoint xs ys = disjoint ys xs.
Proof.
  now intros; unfold disjoint; rewrite set_intersection_comm; destruct xs,ys.
Qed.
(*Global*) Hint Resolve @disjoint_comm.

Theorem disjoint_subset : forall xs ys zs,
  is_set xs = true ->
  is_set ys = true ->
  is_set zs = true ->
  nonempty xs = true ->
  (forall e, In e xs -> In e ys) ->
  disjoint ys zs = true ->
  disjoint xs zs = true.
Proof.
  intros xs ys zs GOOD1 GOOD2 GOOD3 NONEMPTY SUBSET DISJOINT;
    unfold disjoint in *; simpl in *.
  assert (SUBSET' : forall e, In e (set_intersection xs zs) ->
                              In e (set_intersection ys zs)) by
    (intros e; specialize SUBSET with e;
     repeat rewrite set_intersection_spec; solve [eauto 2 | tauto]).
  destruct (set_intersection ys zs).
  - destruct (set_intersection xs zs).
    + destruct xs; [inversion NONEMPTY | reflexivity].
    + not_subset_cons_nil.
  - inversion DISJOINT.
Qed.
(*Global*) Hint Resolve @disjoint_subset.

Theorem iterate_set : forall f x n,
  (forall y, y < f y) ->
  is_set (iterate f x n) = true.
Proof.
  intros; gdep x; induction n; intros; simpl.
  - reflexivity.
  - simpl; rewrite IHn.
    destruct n; simpl.
    + reflexivity.
    + rewrite andb_true_r, ltb_lt; auto.
Qed.
(*Global*) Hint Resolve @iterate_set.

End theorems.

(* And we repeat this tactic outside the section. *)
Ltac by_set_extensionality := impl__by_set_extensionality set_extensionality.

(* Can be updated automatically by an Emacs script; see `global-hint.el' *)
(* Start globalized hint section *)
Hint Resolve @is_set_tail.
Hint Resolve @delete_preserves_set.
Hint Resolve @filter_preserves_set.
Hint Resolve @is_set_no_dups.
Hint Resolve @insert_unique_adds.
Hint Resolve @insert_unique_preserves.
Hint Resolve @insert_unique_origin.
Hint Resolve @insert_unique_spec.
Hint Resolve @insert_unique_preserves_set_true.
Hint Resolve @to_set_set.
Hint Resolve @to_set_unchanged_sets.
Hint Resolve @to_set_involutive.
Hint Resolve @is_set_head.
Hint Resolve @set_extensionality.
Hint Resolve @set_delete_preserves_set.
Hint Rewrite @set_union_spec : set_specs.
Hint Resolve @set_union_preserves_set.
Hint Resolve @set_union_subset_id.
Hint Resolve @set_union_self_id.
Hint Resolve @set_union_nil_l.
Hint Resolve @set_union_nil_r.
Hint Resolve @set_union_comm.
Hint Resolve @set_union_assoc.
Hint Rewrite @set_intersection_spec : set_specs.
Hint Resolve @set_intersection_preserves_set.
Hint Resolve @set_intersection_subset_id.
Hint Resolve @set_intersection_self_id.
Hint Resolve @set_intersection_nil_l.
Hint Resolve @set_intersection_nil_r.
Hint Resolve @set_intersection_comm.
Hint Resolve @set_intersection_assoc.
Hint Resolve @set_difference_preserves_set.
Hint Rewrite @set_difference_spec : set_specs.
Hint Resolve @set_difference_origin.
Hint Resolve @set_difference_removes.
Hint Resolve @set_difference_subset_annihilating.
Hint Resolve @set_difference_self_annihilating.
Hint Resolve @set_difference_nil_l.
Hint Resolve @set_intersection_nil_r.
Hint Resolve @set_union_intersection_distrib.
Hint Resolve @set_intersection_union_distrib.
Hint Resolve @set_union_difference_distrib.
Hint Resolve @set_difference_union_distrib.
Hint Resolve @set_difference_union_collapse.
Hint Resolve @set_intersection_difference_distrib.
Hint Resolve @set_difference_intersection_distrib.
Hint Resolve @disjoint_irrefl.
Hint Resolve @disjoint_comm.
Hint Resolve @disjoint_subset.
Hint Resolve @iterate_set.
(* End globalized hint section *)
