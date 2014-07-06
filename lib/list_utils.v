Require Import List Bool Sorted lib.Coqlib lib.utils.
Require Import Coq.Classes.SetoidDec.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope Z_scope.

(***** Lists *****)

(*** Type class instances ***)

Generalizable Variables A.

Instance list_eqdec `{eqdec : ! EqDec (eq_setoid A)} :
  EqDec (eq_setoid (list A)).
Proof. red; apply list_eq_dec; assumption. Defined.

(*** Functions ***)

Section functions.

Context `{eqdec : ! EqDec (eq_setoid A)}.

Definition elem : forall (a : A) (xs : list A), {In a xs} + {~ In a xs} :=
  in_dec eqdec.
Arguments elem /.

Definition delete : A -> list A -> list A := remove equiv_dec.
Arguments delete /.

Definition nonempty (xs : list A) : bool :=
  match xs with
    | []     => false
    | _ :: _ => true
  end.

Fixpoint cat_somes (xs : list (option A)) : list A :=
  match xs with
    | []           => []
    | Some x :: xs => x :: cat_somes xs
    | None   :: xs => cat_somes xs
  end.

Import DoNotation.
Fixpoint map_options {B} (f : A -> option B) (xs : list A) : option (list B) :=
  match xs with
    | []       => Some []
    | x :: xs' => do! y  <- f x;
                  do! ys <- map_options f xs';
                  Some (y :: ys)
  end.

Definition the (xs : list A) : option A :=
  match xs with
    | []       => None
    | x :: xs' => if forallb (equiv_dec x) xs' then Some x else None
  end.

Fixpoint iterate (f : A -> A) (x : A) (n : nat) : list A :=
  match n with
    | O    => []
    | S n' => x :: iterate f (f x) n'
  end.

Fixpoint tails (xs : list A) : list (list A) :=
  xs :: match xs with
          | []       => []
          | _ :: xs' => tails xs'
        end.

Definition concat : list (list A) -> list A :=
  fold_right (@app _) [].

Fixpoint tail_pairs (xs : list A) : list (A * list A) :=
  match xs with
    | []       => []
    | x :: xs' => (x,xs') :: tail_pairs xs'
  end.

Fixpoint splits (xs : list A) : list (list A * A * list A) :=
  match xs with
    | []       => []
    | x :: xs' => ([],x,xs') :: map (fun split => let '(pre,mid,post) := split
                                                  in (x::pre,mid,post))
                                    (splits xs')
  end.

Definition all_pairs_b (p : A -> A -> bool) (xs : list A) : bool :=
  forallb (fun split => let '(pre,mid,post) := split
                        in forallb (p mid) pre && forallb (p mid) post)
          (splits xs).

Definition all_tail_pairs_b (p : A -> A -> bool) (xs : list A) : bool :=
  forallb (fun y_ys => forallb (p (fst y_ys)) (snd y_ys))
          (tail_pairs xs).

Definition subset (xs ys : list A) : bool :=
  forallb (fun x => existsb (fun y => if x == y then true else false) ys)
          xs.

End functions.

(*** Properties ***)

Inductive Dup {A : Type} (a : A) : list A -> Prop :=
| Dup_here  : forall xs,   In  a xs -> Dup a (a :: xs)
| Dup_there : forall x xs, Dup a xs -> Dup a (x :: xs).
Hint Constructors Dup.

Inductive In2 {A : Type} (a b : A) : list A -> Prop :=
| In2_here_1 : forall xs,   In  b xs   -> In2 a b (a :: xs)
| In2_here_2 : forall xs,   In  a xs   -> In2 a b (b :: xs)
| In2_there  : forall x xs, In2 a b xs -> In2 a b (x :: xs).
Hint Constructors In2.

(*** Theorems ***)

Hint Unfold In.
Hint Constructors NoDup.
Hint Constructors LocallySorted Sorted StronglySorted.

Theorem app_cons_assoc : forall {A} (a : A) xs ys,
  xs ++ a :: ys = (xs ++ [a]) ++ ys.
Proof. induction xs; simpl; intros; try rewrite IHxs; auto. Qed.
Hint Resolve app_cons_assoc.

Theorem in_anywhere : forall {A} (a : A) pre post,
  In a (pre ++ a :: post).
Proof. induction pre; simpl; auto. Qed.
Hint Resolve in_anywhere.

Theorem in_last : forall {A} (a : A) xs,
  In a (xs ++ [a]).
Proof. induction xs; simpl; auto. Qed.
Hint Resolve in_last.

Theorem in_spec : forall {A} (a : A) xs,
  In a xs <-> exists pre post, xs = pre ++ a :: post.
Proof. split; [|intros [pre [post EQ]]; subst]; auto using in_split. Qed.

Theorem forallb_map : forall {A B} (p : B -> bool) (f : A -> B) xs,
  forallb p (map f xs) = forallb (p ∘ f) xs.
Proof.
  induction xs; simpl; try rewrite IHxs; reflexivity.
Qed.
Hint Resolve forallb_map.

Theorem forallb_ext : forall {A} (p q : A -> bool) xs,
  (forall a, p a = q a) ->
  forallb p xs = forallb q xs.
Proof.
  induction xs; intros EQ; simpl; try rewrite IHxs, EQ; auto.
Qed.
Hint Resolve forallb_ext.

Theorem forallb_impl : forall {A} (p q : A -> bool) xs,
  (forall a, p a = true -> q a = true) ->
  forallb p xs = true -> forallb q xs = true.
Proof.
  intros; repeat rewrite forallb_forall in *; auto.
Qed.
Hint Resolve forallb_impl.

Theorem forallb_ext_in : forall {A} (p q : A -> bool) xs,
  (forall a, In a xs -> p a = q a) ->
  forallb p xs = forallb q xs.
Proof.
  induction xs; intros EQ; simpl; try rewrite IHxs, EQ; auto.
Qed.
Hint Resolve forallb_ext_in.

Theorem forallb_impl_in : forall {A} (p q : A -> bool) xs,
  (forall a, In a xs -> p a = true -> q a = true) ->
  forallb p xs = true -> forallb q xs = true.
Proof.
  intros; repeat rewrite forallb_forall in *; auto.
Qed.
Hint Resolve forallb_impl_in.

Theorem forallb_subset : forall {A} (p : A -> bool) xs ys,
  (forall c, In c ys -> In c xs) ->
  forallb p xs = true ->
  forallb p ys = true.
Proof.
  intros; repeat rewrite forallb_forall in *; auto.
Qed.
Hint Resolve forallb_subset.

Theorem existsb_equiv_decb_in : forall `{eqdec : ! EqDec (eq_setoid A)}
                                       (a : A) xs,
  In a xs -> existsb (equiv_decb a) xs = true.
Proof.
  intros; apply existsb_exists; exists a; rewrite eqb_true_iff; auto.
Qed.
Hint Resolve @existsb_equiv_decb_in.

Theorem in_existsb_equiv_decb : forall `{eqdec : ! EqDec (eq_setoid A)}
                                       (a : A) xs,
  existsb (equiv_decb a) xs = true -> In a xs.
Proof.
  intros until 0; intros EX; rewrite existsb_exists in EX.
  destruct EX; invh and;
  match goal with H : _ ==b _ = true |- _ => rewrite eqb_true_iff in H end;
  congruence.
Qed.
Hint Resolve @in_existsb_equiv_decb.

Corollary existsb_iff_equiv_decb_in : forall `{eqdec : ! EqDec (eq_setoid A)}
                                             (a : A) xs,
  In a xs <-> existsb (equiv_decb a) xs = true.
Proof. split; eauto. Qed.

Theorem NoDup_map : forall {A B} (f : A -> B) (xs : list A),
  (forall x y, f x = f y -> x = y) ->
  NoDup xs -> NoDup (map f xs).
Proof.
  induction xs as [|x xs]; intros until 0; intros INJ ND; simpl; constructor.
  - inversion_clear ND as [|x' xs' Hnin ND'].
    intro Hin; apply Hnin.
    apply in_map_iff in Hin; destruct Hin as [y [Heq Hin]].
    apply INJ in Heq; subst; exact Hin.
  - inversion_clear ND; apply IHxs; assumption.
Qed.
Hint Resolve NoDup_map.

Theorem nil_iff_not_in : forall {A} (xs : list A),
  xs = [] <-> (forall a, ~ In a xs).
Proof.
  split; intro;
    [ subst; auto
    | destruct xs; [auto | exfalso; unfold not in *; eauto ] ].
Qed.

Theorem in_init : forall {A} (x : A) xs,
  In x (init xs) -> In x xs.
Proof.
  induction xs as [|? [|? ?]]; inversion_clear 1; simpl in *; auto.
Qed.
Hint Resolve in_init.

Theorem NoDup_init : forall {A} (xs : list A),
  NoDup xs -> NoDup (init xs).
Proof.
  induction xs as [|? [|? ?]]; inversion_clear 1; constructor; auto.
Qed.
Hint Resolve NoDup_init.

Theorem LocallySorted_strengthen : forall {A} (R R' : A -> A -> Prop) xs,
  (forall a b, R a b -> R' a b) ->
  LocallySorted R xs -> LocallySorted R' xs.
Proof.
  induction xs as [|x xs]; intros SUBREL SORTED; auto.
  inversion SORTED; auto; subst.
  constructor.
  - apply IHxs; assumption.
  - apply SUBREL; assumption.
Qed.
Hint Resolve LocallySorted_strengthen.

Theorem StronglySorted_NoDup : forall {A} (R : A -> A -> Prop) xs,
  (forall a, ~ R a a) ->
  StronglySorted R xs -> NoDup xs.
Proof.
  induction xs as [|x xs]; intros IRREFL SORTED; auto.
  inversion SORTED as [|x' xs' SORTED' ALL]; auto; subst.
  constructor; auto.
  rewrite Forall_forall in ALL.
  intros IN; specialize (ALL x IN).
  apply IRREFL in ALL; exact ALL.
Qed.
Hint Resolve StronglySorted_NoDup.

Theorem find_existsb : forall {A} (p : A -> bool) xs,
  is_some (find p xs) = existsb p xs.
Proof.
  induction xs as [|x xs]; simpl; [|destruct (p x)]; auto.
Qed.
Hint Resolve find_existsb.

Theorem find_in : forall {A} (p : A -> bool) xs x,
  find p xs = Some x -> In x xs /\ p x = true.
Proof.
  induction xs as [|x xs]; [inversion 1|simpl; intros y].
  destruct (p x) eqn:?.
  - inversion 1; subst; tauto.
  - specialize IHxs with y; tauto.
Qed.
Hint Resolve find_in.

Theorem filter_preserves_Forall : forall {A} (P : A -> Prop) p xs,
  Forall P xs ->
  Forall P (filter p xs).
Proof.
  intros; rewrite Forall_forall in *; intros; rewrite filter_In in *;
    invh and; auto.
Qed.
Hint Resolve filter_preserves_Forall.

Corollary filter_preserves_forallb : forall {A} (p1 p2 : A -> bool) xs,
  forallb p1 xs = true ->
  forallb p1 (filter p2 xs) = true.
Proof. intros; rewrite forallb_forall, <- Forall_forall in *; auto. Qed.
Hint Resolve filter_preserves_forallb.

Corollary filter_preserves_strongly_sorted : forall {A} (R : A -> A -> Prop)
                                                    p xs,
  StronglySorted R xs ->
  StronglySorted R (filter p xs).
Proof.
  induction 1 as [|x xs SORTED IH ALL]; simpl; auto.
  destruct (p x); auto.
Qed.
Hint Resolve filter_preserves_strongly_sorted.

Lemma delete_comm : forall `{eqdec : ! EqDec (eq_setoid A)} (a b : A) xs,
  delete a (delete b xs) = delete b (delete a xs).
Proof.
  induction xs as [|x xs]; simpl in *; auto;
  destruct (b == x), (a == x); ssubst; try reflexivity;
    simpl; try (destruct (x == x); scongruence).
  destruct (a == x), (b == x); scongruence.
Qed.
Hint Resolve @delete_comm.

Theorem delete_in : forall `{eqdec : ! EqDec (eq_setoid A)} (a : A) xs,
  ~ In a (delete a xs).
Proof. auto using remove_In. Qed.
Hint Resolve @delete_in.

Theorem delete_not_in : forall `{eqdec : ! EqDec (eq_setoid A)} (a : A) xs,
  ~ In a xs -> delete a xs = xs.
Proof.
  induction xs as [|x xs]; intros NOT_IN; auto; simpl in *.
  apply Decidable.not_or in NOT_IN; destruct NOT_IN as [NEQ NOT_IN].
  destruct (a == x); [congruence|].
  f_equal; auto.
Qed.
Hint Resolve @delete_not_in.

Theorem delete_in_iff : forall `{eqdec : ! EqDec (eq_setoid A)} (a b : A) xs,
  In a (delete b xs) <-> a <> b /\ In a xs.
Proof.
  induction xs as [|x xs]; simpl; try tauto.
  destruct (b == x); ssubst; split; simpl; solve [intuition; subst; auto].
Qed.

Theorem delete_preserves_Forall : forall `{eqdec : ! EqDec (eq_setoid A)}
                                         (P : A -> Prop) a xs,
  Forall P xs ->
  Forall P (delete a xs).
Proof.
  induction 1 as [|x xs Px ALL IH]; simpl; auto.
  destruct (a == x); auto.
Qed.
Hint Resolve @delete_preserves_Forall.

Corollary delete_preserves_forallb : forall `{eqdec : ! EqDec (eq_setoid A)}
                                            (p : A -> bool) a xs,
  forallb p xs = true ->
  forallb p (delete a xs) = true.
Proof.
  intros; rewrite forallb_forall, <- Forall_forall in *; auto.
Qed.
Hint Resolve @delete_preserves_forallb.
  
Corollary delete_preserves_strongly_sorted :
  forall `{eqdec : ! EqDec (eq_setoid A)} (R : A -> A -> Prop) a xs,
    StronglySorted R xs ->
    StronglySorted R (delete a xs).
Proof.
  induction 1 as [|x xs SORTED IH ALL]; simpl; auto.
  destruct (a == x); auto.
Qed.
Hint Resolve @delete_preserves_strongly_sorted.

Theorem nonempty_spec : forall {A} (xs : list A),
  nonempty xs = true <-> xs <> [].
Proof.
  destruct xs; simpl; split; solve [tauto | congruence].
Qed.

Theorem nonempty_iff_in : forall {A} (xs : list A),
  nonempty xs = true <-> (exists a, In a xs).
Proof.
  split.
  - destruct xs; [simpl in *; congruence | eauto].
  - intros [a IN]; destruct xs; [inversion IN | reflexivity].
Qed.

Theorem empty_iff_not_in : forall {A} (xs : list A),
  nonempty xs = false <-> (forall a, ~ In a xs).
Proof.
  destruct xs; simpl; split; try solve [intuition].
  intros IN; exfalso. eapply IN; left; reflexivity.
Qed.

Theorem in_cat_somes : forall {A} (xs : list (option A)) x,
  In (Some x) xs <-> In x (cat_somes xs).
Proof.
  induction xs as [|y ys]; split; simpl; auto.
  - intros [EQ | IN].
    + subst; auto.
    + apply IHys in IN. destruct y; auto.
  - intros IN. destruct y as [y|].
    + inversion IN; [left; f_equal | right; apply IHys]; assumption.
    + right. apply IHys, IN.
Qed.

Theorem NoDup_cat_somes : forall {A} (xs : list (option A)),
  NoDup xs -> NoDup (cat_somes xs).
Proof.
  induction xs as [|ox xs]; intros ND; simpl; eauto.
  inversion_clear ND as [|ox' xs' NOT_IN ND']; rename ND' into ND.
  destruct ox as [x|]; try constructor; auto.
  intro IN; apply NOT_IN, in_cat_somes, IN.
Qed.
Hint Resolve NoDup_cat_somes.

Theorem map_options_somes : forall {A B} (f : A -> option B) xs,
  is_some (map_options f xs) = true <->
  (forall x, In x xs -> is_some (f x) = true).
Proof.
  induction xs as [|x xs]; simpl;
    [tauto | unfold bind; split; [intros SOME x' IN | intros ALL]].
  - destruct IN as [<- | IN]; (destruct (f x); [auto | discriminate]).
    apply IHxs in IN; auto.
    destruct (map_options f xs); [reflexivity | discriminate].
  - destruct (f x) eqn:fx.
    + destruct (map_options f xs); [simpl | apply IHxs]; auto.
    + lapply (ALL x); [rewrite fx; discriminate | auto].
Qed.

Theorem map_options_none : forall {A B} (f : A -> option B) xs,
  map_options f xs = None <-> (exists x, In x xs /\ f x = None).
Proof.
  induction xs as [|x xs]; simpl;
    [split; [discriminate | intros []; tauto] | unfold bind; split].
  - intros SOME. destruct (f x) eqn:fx.
    + destruct (map_options f xs); [discriminate | apply IHxs in SOME].
      destruct SOME as [x' [IN fx']]; eauto.
    + eauto.
  - intros [x' [[-> | IN] fx']].
    + rewrite fx'; reflexivity.
    + destruct IHxs as [_ IHxs].
      specialize (IHxs (ex_intro _ x' (conj IN fx'))); rewrite IHxs.
      destruct (f x); reflexivity.
Qed.

Theorem map_options_in : forall {A B} (f : A -> option B) xs ys,
  map_options f xs = Some ys ->
  forall y, In y ys <-> (exists x, f x = Some y /\ In x xs).
Proof.
  induction xs as [|x xs]; simpl; unfold bind; intros until 0; intros SOME y.
  - inversion_clear SOME; simpl; split; [|intros []]; tauto.
  - destruct (f x) as [y'|] eqn:fx; [|congruence].
    destruct (map_options f xs) as [ys'|]; [|congruence].
    inversion SOME; subst; clear SOME; simpl.
    split.
    + intros [<- | IN]; [eauto|].
      apply IHxs in IN; [destruct IN as [x' IHxs'] | reflexivity].
      exists x'; tauto.
    + intros [x' [fx' [-> | IN']]].
      * left; congruence.
      * right; apply IHxs; eauto.
Qed.

Theorem map_options_bind : forall {A B C}
                                  (f : A -> option B) (g : B -> option C) xs,
  bind (map_options g) (map_options f xs) = map_options (bind g ∘ f) xs.
Proof.
  intros A B C f g xs.
  induction xs as [|x xs]; simpl in *; [reflexivity|].
  destruct (f x) as [fx|]; simpl; [|reflexivity].
  rewrite <-IHxs.
  destruct (map_options f xs); simpl; [reflexivity|].
  destruct (g fx); reflexivity.
Qed.  

Theorem the_in : forall `{eqdec : ! EqDec (eq_setoid A)} (xs : list A) x,
  the xs = Some x -> In x xs.
Proof.
  destruct xs as [|x' xs']; [discriminate | simpl; intros x SOME].
  destruct (forallb _ _) eqn:ALL;
    [inversion SOME; subst x'; clear SOME | discriminate].
  auto.
Qed.
Hint Resolve the_in.

Theorem the_spec : forall `{eqdec : ! EqDec (eq_setoid A)} (xs : list A) x,
  the xs = Some x <-> nonempty xs = true /\ forall x', In x' xs -> x' == x.
Proof.
  destruct xs as [|x' xs']; simpl; [split; [|intros []]; discriminate|].
  split.
  - destruct (forallb _ _) eqn:ALL; [|discriminate].
    intros EQ; inversion EQ; subst; clear EQ.
    split; auto.
    rewrite forallb_forall in ALL.
    intros x' [<- | IN]; [reflexivity|].
    apply ALL in IN. destruct (x == x'); [ssubst; reflexivity | discriminate].
  - intros [_ ALL].
    assert (ALL' : forall y, In y xs' -> proj_sumbool (x == y) = true) by
      (intros y IN; specialize (ALL y (or_intror IN));
       ssubst; destruct (_ == _); [reflexivity | congruence]).
    rewrite <-forallb_forall in ALL'.
    specialize (ALL x' (or_introl eq_refl)); ssubst.
    rewrite ALL'; reflexivity.
Qed.

Theorem dup_in : forall {A} (a : A) xs,
  Dup a xs -> In a xs.
Proof. induction 1; auto. Qed.
Hint Resolve dup_in.

Theorem dup_in_tail : forall {A} (a : A) x xs,
  Dup a (x :: xs) -> In a xs.
Proof.
  intros until xs; intros DUP; gdep x; induction xs as [|x' xs]; intros.
  - inversion_clear DUP;
    match goal with
      [H : _(*In/Dup*) _ [] |- _] => inversion H
    end.
  - inversion DUP; subst; auto.
Qed.
Hint Resolve dup_in_tail.

Theorem dup_spec : forall {A} (a : A) xs,
  Dup a xs <-> exists ys zs, xs = ys ++ zs /\ In a ys /\ In a zs.
Proof.
  split.
  - induction 1 as [xs IN | h xs DUP].
    + exists [a],xs; auto.
    + destruct IHDUP as [ys [zs [EQ [IN_ys IN_zs]]]].
      exists (h :: ys),zs; simpl; subst; repeat split; try right; auto.
  - intros [ys [zs [EQ [IN_ys IN_zs]]]]; subst; gdep zs;
    induction ys as [|y ys]; intros.
    + inversion IN_ys.
    + simpl; inversion IN_ys; subst.
      * constructor; apply in_app_iff; right; auto.
      * constructor; apply IHys; assumption.
Qed.
Hint Resolve dup_in.

Theorem in2_comm : forall {A} (a b : A) xs,
  In2 a b xs -> In2 b a xs.
Proof. induction 1; auto. Qed.
Hint Resolve in2_comm.

Theorem in2_in : forall {A} (a b : A) xs,
  In2 a b xs -> In a xs /\ In b xs.
Proof. induction 1; try destruct IHIn2; auto. Qed.
Hint Resolve in2_in.

Theorem in2_in_1 : forall {A} (a b : A) xs,
  In2 a b xs -> In a xs.
Proof fun {A} a b xs in2 => proj1 (in2_in a b xs in2).
Hint Resolve in2_in_1.

Theorem in2_in_2 : forall {A} (a b : A) xs,
  In2 a b xs -> In b xs.
Proof fun {A} a b xs in2 => proj2 (in2_in a b xs in2).
Hint Resolve in2_in_2.

Theorem in_neq_in2 : forall {A} (a b : A) xs,
  a <> b ->
  In a xs -> In b xs ->
  In2 a b xs.
Proof.
  induction xs as [|x xs]; intros neq IN_a IN_b; [solve [inversion IN_a]|].
  inversion IN_a; inversion IN_b; subst; solve [congruence | auto].
Qed.
Hint Resolve in_neq_in2.

Theorem in2_dup_iff : forall {A} (a : A) xs,
  In2 a a xs <-> Dup a xs.
Proof. split; induction 1; auto. Qed.

Theorem in2_nodup_neq : forall {A} (a b : A) xs,
  NoDup xs -> In2 a b xs -> a <> b.
Proof.
  induction xs as [|x xs]; intros NO_DUP' IN2'.
  - inversion IN2'.
  - inversion NO_DUP' as [|x' xs' NOT_IN NO_DUP]; subst;
    inversion IN2' as [xs'' IN | xs'' IN | x'' xs'' IN2]; subst;
    solve [ auto | intros EQ; apply NOT_IN; subst; auto ].
Qed.
Hint Resolve in2_nodup_neq.

Theorem in2_subset : forall {A} (a b : A) xs ys,
  (forall c, In c xs -> In c ys) ->
  NoDup xs ->
  In2 a b xs ->
  In2 a b ys.
Proof.
  intros until 0; intros SUBSET NO_DUP IN2;
    induction xs as [|x xs];
    inversion IN2 as [ys' IN | ys' IN | y' ys' IN2']; subst;
    inversion NO_DUP as [|x' xs' NOT_IN NO_DUP']; subst;
    apply in_neq_in2; eauto. (* Or `eauto 7', but this is MUCH slower. *)
Qed.
Hint Resolve in2_subset.

Theorem in2_map : forall {A B} (f : A -> B) a b xs,
  In2 a b xs -> In2 (f a) (f b) (map f xs).
Proof. induction 1; simpl in *; auto using in_map. Qed.
Hint Resolve in2_map.

Theorem in2_map_iff : forall {A B} (f : A -> B) a b xs,
  In2 a b (map f xs) <-> (exists a' b', f a' = a /\ f b' = b /\ In2 a' b' xs).
Proof.
  split.
  - induction xs as [|x xs]; intros IN2; [solve [inversion IN2] | simpl in *].
    inversion IN2 as [xs' IN | xs' IN | x' xs' IN2']; subst;
      first [ apply in_map_iff in IN; destruct IN as [? [? ?]]
            | apply IHxs in IN2'; destruct IN2' as [? [? [? [? ?]]]] ];
      eauto 10.
  - intros [a' [b' [EQ_a [EQ_b IN2]]]]; subst; induction IN2; auto.
Qed.

Theorem in2_split : forall {A} (a b : A) xs,
  In2 a b xs <-> exists pre mid post, xs = pre ++ a :: mid ++ b :: post \/
                                      xs = pre ++ b :: mid ++ a :: post.
Proof.
  split.
  - induction 1 as [xs IN | xs IN | x xs IN2];
      try ( apply in_split in IN; destruct IN as [? [? ?]]; subst;
            exists []; repeat eexists; solve [ left;  reflexivity
                                             | right; reflexivity ] ).
    destruct IHIN2 as [pre [mid [post [? | ?]]]]; subst;
      exists (x :: pre), mid, post; eauto.
  - induction xs as [|x xs]; intros [pre [mid [post [EQ | EQ]]]];
      solve [ destruct pre; inversion EQ
            | destruct pre; simpl in *;
              inversion EQ; subst; constructor;
              first [apply IHxs; eauto | auto] ].
Qed.

Theorem in2_app : forall {A} (a b : A) xs ys,
  In a xs -> In b ys -> In2 a b (xs ++ ys).
Proof.
  induction xs.
  - inversion 1.
  - simpl; destruct 1; subst; intros; auto.
    constructor; apply in_app_iff; auto.
Qed.
Hint Resolve in2_app.

Lemma in2_delete : forall `{eqdec : ! EqDec (eq_setoid A)} (a b y : A) xs,
  In2 a b (delete y xs) -> In2 a b xs.
Proof.
  induction xs as [|x xs]; [inversion 1 | simpl; intros IN2].
  destruct (y == x); unsetoid; subst; auto.
  inversion IN2 as [del' IN | del' IN | x' del' IN2' ]; subst;
    solve [ auto | constructor; apply delete_in_iff in IN; tauto ].
Qed.
Hint Resolve in2_delete.

Lemma tails_app  : forall {A} (xs ys : list A),
  tails (xs ++ ys) = init (map (fun t => t ++ ys) (tails xs)) ++ tails ys.
Proof.
  induction xs as [|x xs]; [reflexivity|].
  intros ys.
  simpl; rewrite IHxs.
  destruct xs; reflexivity.
Qed.
Hint Resolve tails_app.

Theorem tails_spec : forall {A} (xs : list A) t,
  In t (tails xs) <-> exists pre, pre ++ t = xs.
Proof.
  induction xs as [|x xs]; simpl.
  - split.
    + destruct t, 1; solve [exists []; eauto | discriminate | contradiction].
    + intros [pre Heq]; destruct (app_eq_nil _ _ Heq); auto.
  - split.
    + intros [Heq | Hin].
      * exists []; auto.
      * apply IHxs in Hin. destruct Hin as [pre Hin].
        exists (x :: pre); simpl; f_equal; exact Hin.
    + intros [[|h pre] Heq].
      * left; auto.
      * inversion Heq; subst.
        right; apply IHxs; eauto.
Qed.

Lemma tails_shrinking : forall {A} (xs : list A),
  LocallySorted (fun t t' => exists h, t = h :: t') (tails xs).
Proof.
  induction xs as [|x1 [|x2 xs]]; simpl; eauto.
Qed.
Hint Resolve tails_shrinking.

Lemma tails_shrinking_strong : forall {A} (xs : list A),
  StronglySorted (fun t t' => exists h hs, t = h :: hs ++ t') (tails xs).
Proof.
  intros; apply Sorted_StronglySorted.
  - red. intros ys zs ws [hy [hys EQ_ys]] [hz [hzs EQ_zs]]; subst.
    repeat eexists; f_equal; repeat rewrite app_comm_cons, app_assoc; f_equal.
  - apply Sorted_LocallySorted_iff.
    eapply LocallySorted_strengthen; [|apply tails_shrinking].
    intros ys zs [h EQ]; subst. exists h,[]; reflexivity.
Qed.
Hint Resolve tails_shrinking_strong.

Theorem tails_unique : forall {A} (xs : list A),
  NoDup (tails xs).
Proof.
  intros; eapply StronglySorted_NoDup; [clear xs|apply tails_shrinking_strong].
  intros xs [h [hs EQ]].
  cut (length xs = length (h :: hs ++ xs)).
  - simpl; rewrite app_length, <- plus_Sn_m; omega.
  - f_equal; assumption.
Qed.  
Hint Resolve tails_unique.

Theorem concat_app : forall {A} (xss yss : list (list A)),
  concat (xss ++ yss) = concat xss ++ concat yss.
Proof.
  induction xss; simpl; [reflexivity|].
  intros; rewrite IHxss; apply app_assoc.
Qed.
Hint Resolve concat_app.

Theorem concat_map_concat : forall {A} (xss : list (list (list A))),
  concat (map concat xss) = concat (concat xss).
Proof.
  induction xss as [|xs xss]; try reflexivity.
  simpl; rewrite IHxss; auto.
Qed.
Hint Resolve concat_map_concat.

Theorem concat_map_return : forall {A} (xs : list A),
  concat (map (fun x => [x]) xs) = concat [xs].
Proof.
  induction xs; simpl; [|rewrite IHxs]; reflexivity.
Qed.
Hint Resolve concat_map_return.

Theorem concat_return_id : forall {A} (xs : list A),
  concat [xs] = xs.
Proof.
  simpl; auto using app_nil_r.
Qed.
Hint Resolve concat_return_id.

Theorem concat_map_map : forall {A B} (f : A -> B) xss,
  concat (map (map f) xss) = map f (concat xss).
Proof.
  induction xss; simpl; [|rewrite IHxss, map_app]; reflexivity.
Qed.
Hint Resolve concat_map_map.
  
Theorem concat_in : forall {A} (xss : list (list A)) x,
  In x (concat xss) <-> (exists xs, In xs xss /\ In x xs).
Proof.
  induction xss; simpl.
  - split; intros; try invh ex; tauto.
  - intros. rewrite in_app_iff. rewrite IHxss.
    split; intros;
      [ invh or; [|invh ex; invh and]
      | invh ex; invh and; invh or ];
      eauto.
Qed.

Theorem iterate_nonempty : forall {A} (f : A -> A) x n,
  nonempty (iterate f x n) = true <-> n <> O.
Proof. destruct n; simpl; split; congruence. Qed.

(* TODO We could spec out `iterate' more. *)

Theorem tail_pairs_spec_1 : forall {A} (xs : list A),
  map (fun p => fst p :: snd p) (tail_pairs xs) = init (tails xs).
Proof.
  induction xs as [|x xs]; simpl; [reflexivity|].
  rewrite IHxs.
  destruct xs; reflexivity.
Qed.
Hint Resolve tail_pairs_spec_1.

Lemma tails_init_all_cons : forall {A} (xs : list A),
  forallb is_some (map (fun t => match t with
                                   | h :: t' => Some (h,t')
                                   | []      => None
                                 end)
                       (init (tails xs)))
  = true.
Proof.
  induction xs.
  - reflexivity.
  - rewrite <- IHxs.
    destruct xs; reflexivity.
Qed.
Hint Resolve tails_init_all_cons.

Theorem tail_pairs_spec_2 : forall {A} (xs : list A),
  tail_pairs xs = cat_somes (map (fun t => match t with
                                             | h :: t' => Some (h,t')
                                             | []      => None
                                           end)
                                 (init (tails xs))).
Proof.
  induction xs as [|x xs]; simpl; [reflexivity|].
  rewrite IHxs.
  destruct xs; reflexivity.
Qed.
Hint Resolve tail_pairs_spec_2.

Theorem tail_pairs_unique : forall {A} (xs : list A),
  NoDup (tail_pairs xs).
Proof.
  intros; rewrite tail_pairs_spec_2.
  apply NoDup_cat_somes, NoDup_map; auto.
  clear xs; intros [|x xs] [|y ys]; inversion 1; reflexivity.
Qed.
Hint Resolve tails_unique.

Theorem tail_pairs_order : forall {A} (xs : list A),
  map fst (tail_pairs xs) = xs.
Proof.
  induction xs; simpl; f_equal; auto.
Qed.
Hint Resolve tail_pairs_order.

Lemma splits_original : forall {A} (xs : list A) pre mid post,
  In (pre,mid,post) (splits xs) ->
  pre ++ mid :: post = xs.
Proof.
  induction xs as [|x xs]; intros until 0.
  - inversion 1.
  - intros [here | there].
    + inversion here; subst. reflexivity.
    + apply in_map_iff in there;
      destruct there as [[[pre' mid'] post'] [Heq HIn]];
      inversion Heq; subst.
      simpl; f_equal. apply IHxs, HIn.
Qed.
Hint Resolve splits_original.

Lemma splits_all : forall {A} (xs : list A) pre mid post,
  pre ++ mid :: post = xs ->
  In (pre,mid,post) (splits xs).
Proof.
  intros until pre; gdep xs; induction pre as [|y pre]; intros until 0;
    simpl; intros Heq.
  - subst; left; reflexivity.
  - destruct xs as [|x xs]; inversion Heq;
      match goal with [H : y = x|- _] => rename H into Heq_xy end;
      match goal with [H : ?ys = xs |- _] =>
        rename H into Heq_xs; assert (HIn : ys = xs) by exact Heq_xs
      end.
    clear Heq; apply IHpre in HIn; subst y; rewrite Heq_xs in *.
    right.
    set (fn := fun split => let '(pre',mid',post') := split
                            in (x::pre',mid',post')).
    assert (Heq_fn : (x :: pre, mid, post) = fn (pre,mid,post)) by reflexivity.
    rewrite Heq_fn. apply in_map. assumption.
Qed.
Hint Resolve splits_all.

Theorem splits_spec : forall {A} (xs : list A) pre mid post,
  In (pre,mid,post) (splits xs) <-> pre ++ mid :: post = xs.
Proof. split; auto. Qed.

Theorem splits_unique : forall {A} (xs : list A),
  NoDup (splits xs).
Proof.
  induction xs as [|x xs]; simpl; constructor.
  - intro HIn; apply in_map_iff in HIn;
      destruct HIn as [[[pre mid] post] [Heq HIn]].
    inversion Heq.
  - apply NoDup_map; [|exact IHxs].
    intros [[pre1 mid1] post1] [[pre2 mid2] post2] Heq.
    inversion_clear Heq; reflexivity.
Qed.
Hint Resolve splits_unique.

Theorem splits_order : forall {A} (xs : list A),
  map (fun split => snd (fst split)) (splits xs) = xs.
Proof.
  induction xs.
  - reflexivity.
  - simpl; f_equal.
    eapply eq_trans; [|apply IHxs].
    rewrite map_map; apply map_ext.
    destruct 0 as [[? ?] ?]; reflexivity.
Qed.
Hint Resolve splits_order.

Theorem splits_tail_pairs : forall {A} (xs : list A),
  map (fun split => (snd (fst split), snd split)) (splits xs) =
  tail_pairs xs.
Proof.
  induction xs; simpl; try reflexivity.
  f_equal. rewrite <- IHxs.
  rewrite map_map,
          map_ext with (g := (fun split => (snd (fst split), snd split)));
    auto.
  destruct 0 as [[? ?] ?]; simpl; reflexivity.
Qed.
Hint Resolve splits_tail_pairs.

Theorem splits_mid_in : forall {A} (xs : list A) pre mid post,
  In (pre,mid,post) (splits xs) -> In mid xs.
Proof.
  intros; rewrite <- splits_order.
  apply in_map_iff; exists (pre,mid,post); auto.
Qed.
Hint Resolve splits_mid_in.

Theorem in_splits_mid : forall {A} (xs : list A) x,
  In x xs -> exists pre post, In (pre,x,post) (splits xs).
Proof.
  intros until 0; intros IN; rewrite <- splits_order in IN.
  apply in_map_iff in IN; destruct IN as [[[pre mid] post] [EQ IN]];
    simpl in *; subst.
  exists pre, post; exact IN.
Qed.
Hint Resolve in_splits_mid.

Theorem splits_pre_mid : forall {A} (xs : list A) x pre mid post,
  In (pre,mid,post) (splits xs) ->
  In x pre ->
  exists pre' post', In (pre',x,post') (splits xs).
Proof.
  induction xs as [|y ys]; intros until 0; intros IN_split IN_pre; simpl in *;
    [solve [inversion IN_split]|].
  destruct IN_split as [EQ | IN_split].
  - inversion EQ; subst; inversion IN_pre.
  - apply in_map_iff in IN_split.
    destruct IN_split as [[[pre' mid'] post'] [EQ IN_split]].
    inversion EQ; subst; clear EQ.
    inversion IN_pre.
    + subst. do 2 eexists; left; reflexivity.
    + apply IHys with (x:=x) in IN_split; try assumption.
      destruct IN_split as [pre'' [post'' IN'']].
      do 2 eexists.
      right. apply in_map_iff. exists (pre'',x,post''); auto.
Qed.
Hint Resolve splits_pre_mid.

Theorem all_pairs__all_tail_pairs : forall {A} (p : A -> A -> bool) xs,
  all_pairs_b      p xs = true ->
  all_tail_pairs_b p xs = true.
Proof.
  intros until 0.
  unfold all_pairs_b, all_tail_pairs_b.
  rewrite <- splits_tail_pairs, forallb_map; simpl.
  induction (splits xs) as [|[[pre mid] post] sxs]; [reflexivity|].
  simpl; repeat rewrite andb_true_iff; intros [[? ?] ?]; auto.
Qed.
Hint Resolve all_pairs__all_tail_pairs.

Theorem all_pairs_in2_comm : forall {A} (p : A -> A -> bool) xs,
  (forall a b, In2 a b xs -> p a b = p b a) ->
  all_pairs_b p xs = all_tail_pairs_b p xs.
Proof.
  intros until 0; intros COMM.
  unfold all_pairs_b, all_tail_pairs_b.
  rewrite <- splits_tail_pairs, forallb_map; simpl.
  match goal with
    [|- forallb ?the_fn_all (splits xs) = forallb ?the_fn_tail (splits xs) ] =>
    set (fn_all := the_fn_all); set (fn_tail := the_fn_tail)
  end.
  induction xs as [|x xs]; [reflexivity|].
  cbv delta [fn_tail]; simpl; fold fn_tail.
  destruct (forallb (p x) xs) eqn:all_xs; [|reflexivity].
  f_equal.
  repeat rewrite forallb_map; simpl.
  match goal with
    [|- forallb ?the_fn_all' (splits xs) = forallb ?the_fn_tail' (splits xs) ] =>
    set (fn_all' := the_fn_all'); set (fn_tail' := the_fn_tail')
  end.
  assert (EQT : forallb fn_tail (splits xs) = forallb fn_tail' (splits xs)). {
    apply forallb_ext.
    subst fn_tail fn_tail'; destruct 0 as [[pre mid] post]; reflexivity.
  }
  assert (EQA : forallb fn_all (splits xs) = forallb fn_all' (splits xs)). {
    apply forallb_ext_in.
    subst fn_all fn_all'; destruct 0 as [[pre mid] post]; intros IN; simpl.
    rewrite <- andb_true_l at 1; rewrite <- andb_assoc; f_equal.
    symmetry; rewrite COMM; eauto.
    rewrite forallb_forall in all_xs; eauto.
  }
  rewrite <- EQT, <- EQA; auto.
Qed.
Hint Resolve all_pairs_in2_comm.

Corollary all_pairs_comm : forall {A} (p : A -> A -> bool) xs,
  (forall a b, p a b = p b a) ->
  all_pairs_b p xs = all_tail_pairs_b p xs.
Proof. auto. Qed.
Hint Resolve all_pairs_comm.

Theorem all_pairs_spec : forall {A} (p : A -> A -> bool) xs,
  all_pairs_b p xs = true <->
  (forall x y, In2 x y xs -> p x y = true).
Proof.
  intros; unfold all_pairs_b; rewrite forallb_forall; split.
  - intros ALL a b IN2.
    assert (EQ : exists pre mid post, pre ++ a :: mid ++ b :: post = xs \/
                                      pre ++ b :: mid ++ a :: post = xs) by
        (apply in2_split in IN2; destruct IN2 as [? [? [? [? | ?]]]]; eauto);
      destruct EQ as [pre [mid [post EQs]]].
    destruct EQs as [EQ | EQ];
      [ assert (IN_a : In (pre, a, mid ++ b :: post) (splits xs)) by
          auto
      | assert (IN_a : In (pre ++ b :: mid, a, post) (splits xs)) by
          (subst; rewrite app_comm_cons, app_assoc; auto) ];
      apply ALL in IN_a; apply andb_true_iff in IN_a; destruct IN_a;
      rewrite forallb_forall in *; auto.
  - intros SPEC [[pre mid] post] IN.
    apply andb_true_iff; repeat rewrite forallb_forall.
    apply splits_spec in IN; subst.
    split; intros a IN'; apply SPEC; eauto.
    rewrite app_cons_assoc; auto.
Qed.

Theorem all_pairs_subset : forall {A} (p : A -> A -> bool) xs ys,
  (forall c, In c ys -> In c xs) ->
  NoDup ys ->
  all_pairs_b p xs = true ->
  all_pairs_b p ys = true.
Proof.
  intros until 0; intros SUBSET NO_DUP ALL;
    (* Replacing this with `repeat rewrite all_pairs_spec in *' doesn't work *)
    rewrite all_pairs_spec in ALL; rewrite all_pairs_spec;
    intros; eauto.
Qed.
Hint Resolve all_pairs_subset.                                       

Theorem all_pairs_distinct_nodup : forall {A} (p : A -> A -> bool) xs,
  (forall a, p a a = false) ->
  all_pairs_b p xs = true   ->
  NoDup xs.
Proof.
  intros A p xs IRREFL ALL; rewrite all_pairs_spec in ALL.
  induction xs as [|x xs]; constructor; auto.
  intros IN; specialize IRREFL with x; apply not_true_iff_false in IRREFL;
    auto.
Qed.
Hint Resolve all_pairs_distinct_nodup.

Theorem delete_preserves_all_pairs : forall `{eqdec : ! EqDec (eq_setoid A)}
                                            (p : A -> A -> bool) a xs,
  all_pairs_b p xs = true ->
  all_pairs_b p (delete a xs) = true.
Proof.
  intros until 0; intros ALL;
    rewrite all_pairs_spec in ALL; rewrite all_pairs_spec.
  intros b c IN2; apply ALL.
  destruct (b == c) as [EQ | NEQ]; ssubst.
  - clear ALL; induction xs as [|x xs]; simpl in *.
    + inversion IN2.
    + destruct (a == x); auto.
      rewrite in2_dup_iff in IN2; repeat rewrite in2_dup_iff in IHxs;
        rewrite in2_dup_iff.
      inversion IN2; subst; auto.
      constructor. rewrite @delete_in_iff in *; tauto.
  - apply in2_in in IN2; destruct IN2 as [IN_b IN_c];
      apply delete_in_iff in IN_b; destruct IN_b as [NEQ_b IN_b];
      apply delete_in_iff in IN_c; destruct IN_c as [NEQ_c IN_c].
    eauto.
Qed.
Hint Resolve @delete_preserves_all_pairs.

Theorem filter_preserves_all_pairs : forall {A} (p1 : A -> A -> bool) p2 xs,
  all_pairs_b p1 xs = true ->
  all_pairs_b p1 (filter p2 xs) = true.
Proof.
  intros A p1 p2 xs ALL;
    rewrite all_pairs_spec in ALL; rewrite all_pairs_spec.
  intros b c IN2; apply ALL.
  assert (p2_b : p2 b = true) by (eapply filter_In; eauto).
  assert (p2_c : p2 c = true) by (eapply filter_In; eauto).
  clear ALL; induction xs as [|x xs].
  - inversion IN2.
  - simpl in *.
    destruct (p2 x) eqn:p2_x.
    + inversion IN2; subst;
        solve [auto | constructor; eapply filter_In; eassumption].
    + auto.
Qed.        
Hint Resolve filter_preserves_all_pairs.

Theorem all_tail_pairs_tail : forall {A} (p : A -> A -> bool) x xs,
  all_tail_pairs_b p (x :: xs) = forallb (p x) xs && all_tail_pairs_b p xs.
Proof. reflexivity. Qed.
Hint Resolve all_tail_pairs_tail.

Theorem delete_preserves_all_tail_pairs :
  forall `{eqdec : ! EqDec (eq_setoid A)} (p : A -> A -> bool) a xs,
    all_tail_pairs_b p xs = true ->
    all_tail_pairs_b p (delete a xs) = true.
Proof.
  intros until 0; intros ALL; unfold all_tail_pairs_b in *.
  induction xs as [|x xs]; [reflexivity|]; simpl in *.
  apply andb_true_iff in ALL; destruct ALL as [HERE THERE].
  destruct (a == x) as [EQ | NEQ]; auto; simpl.
  andb_true_split; auto.
Qed.
Hint Resolve @delete_preserves_all_tail_pairs.

Theorem filter_preserves_all_tail_pairs : forall {A} p1 p2 (xs : list A),
  all_tail_pairs_b p1 xs = true ->
  all_tail_pairs_b p1 (filter p2 xs) = true.
Proof.
  intros A p1 p2 xs ALL; unfold all_tail_pairs_b in *.
  induction xs as [|x xs]; [reflexivity|]; simpl in *.
  apply andb_true_iff in ALL; destruct ALL as [HERE THERE].
  destruct (p2 x); simpl; try andb_true_split; auto.
Qed.
Hint Resolve filter_preserves_all_tail_pairs.

Theorem subset_spec : forall `{eqdec : ! EqDec (eq_setoid A)} (xs ys : list A),
  subset xs ys = true <-> (forall a, In a xs -> In a ys).
Proof.
  intros; unfold subset; rewrite forallb_forall.
  split.
  - intros ALL a IN_xs. apply ALL, existsb_exists in IN_xs.
    destruct IN_xs as [x [IN_ys EQ_DEC]]; destruct (a == x); congruence.
  - intros SUBSET x IN_xs. apply existsb_exists.
    exists x; split; [auto | destruct (x == x); congruence].
Qed.

(*** Ltac ***)

Ltac not_subset_cons_nil :=
  try match goal with
    | [SUBSET : forall a, In a (?h :: _) -> In a [] |- _] =>
      specialize SUBSET with h
  end;
  match goal with
    | [SUBSET : In ?h (?h :: _) -> In ?h [] |- _] =>
      lapply SUBSET; [inversion 1 | auto]
  end.

Ltac specialize_with_head SAME xs :=
  match xs with ?h :: _ => specialize SAME with h end.
