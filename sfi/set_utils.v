Require Import List Bool ZArith Sorted Coqlib lib.utils list_utils ordered.
Require Import Coq.Classes.SetoidDec.
Import ListNotations.
Local Open Scope bool_scope.

Generalizable Variables A.

(***** Sets of orderable things *****)

(*** Functions ***)

Section functions.

Context `{ORD : Ordered A}.

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

Definition set_intersection (xs ys : list A) : list A :=
  filter (fun x => proj_sumbool (elem x ys)) xs.

Fixpoint set_difference (xs ys : list A) : list A :=
  match ys with
    | [] => xs
    | y :: ys' => set_difference (delete y xs) ys'
  end.

(* Definition range (l h : A) : list A :=
  up_from l (A.to_nat (h - l + 1)). *)

End functions.

(*** Theorems ***)

Section theorems.

Context `{ORD : Ordered A}.

Theorem is_set_tail : forall x xs,
  is_set (x :: xs) = true -> is_set xs = true.
Proof.
  simpl. destruct xs.
  - reflexivity.
  - rewrite andb_true_iff; destruct 1; assumption.
Qed.
(*Global*) Hint Resolve @is_set_tail.

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

Lemma to_set_head : forall x0 xs y0 ys,
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
(*Global*) Hint Resolve @to_set_head.

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

Theorem set_intersection_preserves_set : forall xs ys,
  is_set xs = true ->
  is_set (set_intersection xs ys) = true.
Proof. unfold set_intersection; auto. Qed.
(*Global*) Hint Resolve @set_intersection_preserves_set.

Theorem set_intersection_spec : forall a xs ys,
  In a (set_intersection xs ys) <-> In a xs /\ In a ys.
Proof.
  unfold set_intersection; intros; rewrite filter_In in *.
  destruct (elem a ys); simpl; split; try tauto.
  intros [_ NO]; inversion NO.
Qed.
(*Global*) Hint Resolve @set_intersection_spec.

Theorem set_intersection_subset_id : forall xs ys,
  (forall a, In a xs -> In a ys) ->
  set_intersection xs ys = xs.
Proof.
  induction xs as [|x xs]; simpl; auto; intros ys SUBSET.
  destruct (elem x ys) as [IN | OUT]; simpl.
  - f_equal; auto.
  - elim OUT; auto.
Qed.
(*Global*) Hint Resolve @set_intersection_subset_id.

Corollary set_intersection_self_id : forall xs,
  set_intersection xs xs = xs.
Proof. auto. Qed.
(*Global*) Hint Resolve @set_intersection_self_id.
  
Theorem set_intersection_nil_l : forall xs,
  set_intersection [] xs = [].
Proof. reflexivity. Qed.
(*Global*) Hint Resolve @set_intersection_nil_l.

Theorem set_intersection_nil_r : forall xs,
  set_intersection xs [] = [].
Proof. induction xs; auto. Qed.
(*Global*) Hint Resolve @set_intersection_nil_r.

Theorem set_intersection_comm : forall xs ys,
  is_set xs = true -> is_set ys = true ->
  set_intersection xs ys = set_intersection ys xs.
Proof.
  intros; apply set_extensionality; auto; intros;
  repeat rewrite set_intersection_spec; tauto.
Qed.
(*Global*) Hint Resolve @set_intersection_comm.

Theorem set_intersection_assoc : forall xs ys zs,
  is_set xs = true -> is_set ys = true -> is_set zs = true ->
  set_intersection xs (set_intersection ys zs) =
  set_intersection (set_intersection xs ys) zs.
Proof.
  intros; apply set_extensionality; auto; intros;
  repeat rewrite set_intersection_spec; tauto.
Qed.
(*Global*) Hint Resolve @set_intersection_assoc.

Theorem set_difference_origin : forall e xs ys,
  In e (set_difference xs ys) -> In e xs.
Proof.
  intros until 0; gdep xs; induction ys as [|y ys];
    intros until 0; intros HIn; simpl; auto.
  apply IHys in HIn.
  induction xs as [|x xs]; auto; simpl in *.
  destruct (y == x); try destruct HIn; auto.
Qed.
(*Global*) Hint Resolve @set_difference_origin.

Theorem set_difference_removes : forall e xs ys,
  In e (set_difference xs ys) -> ~ In e ys.
Proof.
  intros until 0; gdep xs; induction ys as [|y ys]; intros until 0; auto.
  simpl; intros HIn_diff [Heq | HIn].
  - subst. apply set_difference_origin in HIn_diff.
    eapply delete_in; apply HIn_diff.
  - eapply IHys; eassumption.
Qed.
(*Global*) Hint Resolve @set_difference_removes.

Theorem set_difference_spec : forall e xs ys,
  In e (set_difference xs ys) <-> In e xs /\ ~ In e ys.
Proof.
  split; [eauto|].
  gdep xs; induction ys as [|y ys]; intros xs [HIn HNIn]; simpl; auto.
  apply IHys; split.
  - induction xs as [|x xs]; simpl; auto.
    destruct (y == x).
    + subst; apply IHxs; destruct HIn.
      * subst; simpl in HNIn.
        apply Decidable.not_or in HNIn; destruct HNIn.
        congruence.
      * assumption.
    + destruct HIn; [left | right]; auto.
  - simpl in HNIn; apply Decidable.not_or in HNIn; destruct HNIn; assumption.
Qed.

Theorem set_difference_preserves_set : forall xs ys,
  is_set xs = true ->
  is_set (set_difference xs ys) = true.
Proof.
  intros xs ys SET; gdep xs; induction ys as [|y xs]; intros; simpl; auto.
Qed.
(*Global*) Hint Resolve @set_difference_preserves_set.

Theorem set_difference_subset_annihilating : forall xs ys,
  (forall a, In a xs -> In a ys) ->
  set_difference xs ys = [].
Proof.
  intros xs ys SUBSET; gdep xs; induction ys as [|y ys]; intros; simpl; auto.
  - destruct xs; [auto | not_subset_cons_nil].
  - apply IHys; intros a NOT_IN.
    assert (NEQ : y <> a) by (intros EQ; subst; eapply delete_in; eassumption).
    specialize SUBSET with a; simpl in *.
    apply delete_in_iff in NOT_IN; tauto.
Qed.
(*Global*) Hint Resolve @set_difference_subset_annihilating.

Corollary set_difference_self_annihilating : forall xs,
  set_difference xs xs = [].
Proof. auto. Qed.
(*Global*) Hint Resolve @set_difference_self_annihilating.
  
Theorem set_difference_nil_l : forall xs,
  set_difference [] xs = [].
Proof. intros; apply set_difference_subset_annihilating; inversion 1. Qed.
(*Global*) Hint Resolve @set_difference_nil_l.

Theorem set_difference_nil_r : forall xs,
  set_difference xs [] = xs.
Proof. reflexivity. Qed.
(*Global*) Hint Resolve @set_intersection_nil_r.

Lemma set_difference_delete_comm : forall a xs ys,
  set_difference (delete a xs) ys =
  delete a (set_difference xs ys).
Proof.
  intros; gdep xs; gdep a; induction ys as [|y ys]; intros; auto.
  simpl; rewrite <- IHys, delete_comm; reflexivity.
Qed.
(*Global*) Hint Resolve @set_difference_delete_comm.

Theorem set_difference_intersection_distrib : forall xs ys zs,
  is_set xs = true -> is_set ys = true -> is_set zs = true ->
  set_difference (set_intersection xs ys) zs =
  set_intersection (set_difference xs zs) (set_difference ys zs).
Proof.
  intros; apply set_extensionality; auto; intros.
  repeat (rewrite set_difference_spec || rewrite set_intersection_spec); tauto.
Qed.
(*Global*) Hint Resolve @set_difference_intersection_distrib.

Theorem set_intersection_difference_distrib : forall xs ys zs,
  is_set xs = true -> is_set ys = true -> is_set zs = true ->
  set_intersection (set_difference xs ys) zs =
  set_difference (set_intersection xs zs) (set_intersection ys zs).
Proof.
  intros; apply set_extensionality; auto; intros.
  repeat (rewrite set_difference_spec || rewrite set_intersection_spec); tauto.
Qed.
(*Global*) Hint Resolve @set_intersection_difference_distrib.

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

(*Theorem range_set : forall l h, is_set (range l h) = true.
Proof. unfold range; auto. Qed.*)
(*(*Global*) Hint Resolve @range_set.*)

(*Lemma up_from_elts : forall x n e,
  In e (up_from x n) <-> x <= e < x + Z_of_nat n.
Proof.
  intros; gdep x; induction n; intros.
  - simpl; split; [inversion 1 | omega].
  - simpl; rewrite Zpos_P_of_succ_nat; split.
    + intros [Heq | Hin]; subst; try apply IHn in Hin; omega.
    + destruct 1, (Z.eq_dec x e); [left; assumption | right; apply IHn; omega].
Qed.*)

(*Theorem range_elts : forall l h e,
  In e (range l h) <-> l <= e <= h.
Proof.
  intros; unfold range; rewrite up_from_elts.
  destruct (Z_le_dec 0 (h - l + 1)) as [pos | neg].
  - rewrite Z2Nat.id; [omega | assumption].
  - assert (Z.to_nat (h - l + 1) = 0%nat). {
      destruct (h - l + 1).
      - omega.
      - contradict neg; cbv; discriminate.
      - apply Z2Nat.inj_neg.
    }
    omega.
Qed.*)

(*Corollary range_empty : forall l h,
  range l h = [] <-> l > h.
Proof.
  intros; rewrite nil_iff_not_in; split.
  - intros NOT_IN; apply Znot_le_gt; intros LE.
    apply NOT_IN with l, range_elts. omega.
  - intros GT e IN. apply range_elts in IN. omega.
Qed.*)

End theorems.

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
Hint Resolve @to_set_head.
Hint Resolve @set_extensionality.
Hint Resolve @set_intersection_preserves_set.
Hint Resolve @set_intersection_spec.
Hint Resolve @set_intersection_subset_id.
Hint Resolve @set_intersection_self_id.
Hint Resolve @set_intersection_nil_l.
Hint Resolve @set_intersection_nil_r.
Hint Resolve @set_intersection_comm.
Hint Resolve @set_intersection_assoc.
Hint Resolve @set_difference_origin.
Hint Resolve @set_difference_removes.
Hint Resolve @set_difference_preserves_set.
Hint Resolve @set_difference_subset_annihilating.
Hint Resolve @set_difference_self_annihilating.
Hint Resolve @set_difference_nil_l.
Hint Resolve @set_intersection_nil_r.
Hint Resolve @set_difference_delete_comm.
Hint Resolve @set_difference_intersection_distrib.
Hint Resolve @set_intersection_difference_distrib.
Hint Resolve @iterate_set.
(* End globalized hint section *)
