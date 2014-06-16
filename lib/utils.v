Require Import Coq.Classes.SetoidDec.
Require Import ZArith. (* omega *)
Require Import List.
Require Import Bool.
Require Import lib.Coqlib.

Close Scope Z_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Useful tactics *)
Ltac gdep x := generalize dependent x.

Ltac split3 := split; [| split].
Ltac split4 := split; [| split3].

(* inv by name of the Inductive relation *)
Ltac invh f :=
    match goal with
      [ id: f |- _ ] => inv id
    | [ id: f _ |- _ ] => inv id
    | [ id: f _ _ |- _ ] => inv id
    | [ id: f _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ ] => inv id
    end.

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

(* ---------------------------------------------------------------- *)
(* Tactics for replacing definitional equality with provable equality *)
Module EqualityTactics.
(* NC: Using a module here to show where these equality related defs
start and end.  It appears that [Ltac] defs don't escape from sections
... *)

Ltac try_exploit l :=
  try (exploit l;
       try solve [eauto];
       let H := fresh "H" in intros H;
       repeat match goal with
                | [H : (exists _, _) |- _ ] => destruct H
                | [H : _ /\ _ |- _ ] => destruct H
              end;
       subst).

(* NC: need to change the order of the premises, versus [modusponens],
so I can get at the implication [P -> Q] first; the proof of [P] may
generate arbitrarily many subgoals. *)
Lemma cut': forall (P Q: Prop), (P -> Q) -> P -> Q.
Proof. auto. Qed.

(* Like [exploit], but using [cut']. *)
Ltac ecut' x :=
    refine (cut' _ _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))
 || refine (cut' _ _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))
 || refine (cut' _ _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _))
 || refine (cut' _ _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _))
 || refine (cut' _ _ _ (x _ _ _ _ _ _ _ _ _ _ _ _))
 || refine (cut' _ _ _ (x _ _ _ _ _ _ _ _ _ _ _))
 || refine (cut' _ _ _ (x _ _ _ _ _ _ _ _ _ _))
 || refine (cut' _ _ _ (x _ _ _ _ _ _ _ _ _))
 || refine (cut' _ _ _ (x _ _ _ _ _ _ _ _))
 || refine (cut' _ _ _ (x _ _ _ _ _ _ _))
 || refine (cut' _ _ _ (x _ _ _ _ _ _))
 || refine (cut' _ _ _ (x _ _ _ _ _))
 || refine (cut' _ _ _ (x _ _ _ _))
 || refine (cut' _ _ _ (x _ _ _))
 || refine (cut' _ _ _ (x _ _))
 || refine (cut' _ _ _ (x _))
 || refine (cut' _ _ _ (x)).

(* Like [exact H], but allow indexes to be definitionally different if
   they are provably equal.

   For example, a goal

     H : T a1 ... an
     ---------------
     T b1 ... bn

   is reduced to proving

     a1 = b1, ..., an = bn

   by [exact_f_equal H].
*)
Ltac exact_f_equal h :=
  let h_eq := fresh "h_eq" in
  let t := type of h in
  match goal with
  | [ |- ?g ] =>
    cut (g = t); [ intro h_eq; rewrite h_eq; exact h | f_equal; auto ]
  end.

(* A generalization of [exact_f_equal] to implications.

   This is like [applys_eq] from LibTactics.v, except you do not need
   to specify which vars you want equalities for.  See Software
   Foundations for a description of [applys_eq]:
   http://www.cis.upenn.edu/~bcpierce/sf/UseTactics.html#lab869

*)
Ltac apply_f_equal h :=
  let h_specialized := fresh "h_specialized" in
  let t := intro h_specialized; exact_f_equal h_specialized in
  (ecut' h; [t|..]).

(* Solve sub goals with [tac], using [f_equal] to make progress when
   possible
*)
Ltac rec_f_equal tac :=
  tac || (progress f_equal; rec_f_equal tac).

Section Test.

Open Scope nat.

Lemma test_exact_f_equal: forall (n1 n2: nat) (P: nat -> nat -> Prop),
  P (n1+1) (n1+n2) -> P (1+n1) (n2+n1).
Proof.
  intros ? ? ? HP. exact_f_equal HP; omega.
Qed.

Lemma test_rec_f_equal:
  forall (n1 n2: nat) (P: list (list nat) -> nat -> Prop),
  P (((n1+1)::nil)::nil) (n1+n2) -> P (((1+n1)::nil)::nil) (n2+n1).
Proof.
  intros ? ? ? HP. exact_f_equal HP; rec_f_equal omega.
Qed.

End Test.

End EqualityTactics.
Export EqualityTactics.

(* Borrowed from CPDT *)
(* Instantiate a quantifier in a hypothesis [H] with value [v], or,
if [v] doesn't have the right type, with a new unification variable.
Also prove the lefthand sides of any implications that this exposes,
simplifying [H] to leave out those implications. *)

Ltac guess v H :=
 repeat match type of H with
          | forall x : ?T, _ =>
            match type of T with
              | Prop =>
                (let H' := fresh "H'" in
                  assert (H' : T); [
                    solve [ eauto 6 ]
                    | specialize (H H'); clear H' ])
                || fail 1
              | _ =>
                specialize (H v)
                || let x := fresh "x" in
                  evar (x : T);
                  let x' := eval unfold x in x in
                    clear x; specialize (H x')
            end
        end.


Ltac eq_H_intros :=
  repeat
    (match goal with
      | [  |- _ = _ -> _ ] =>
        intros ?Heq
    end).

Ltac eq_H_getrid :=
  repeat
    (match goal with
       | [  |- _ = _ -> _ ] =>
         intros _
     end).

Ltac decEq :=
  match goal with
  | [ |- _ = _ ] => f_equal
  | [ |- (?X ?A <> ?X ?B) ] =>
      cut (A <> B); [intro; congruence | try discriminate]
  end.

Ltac allinv :=
  repeat
    match goal with
      | [ H: Some _ = Some _ |- _ ] => inv H
      | [ H: Some _ = None |- _ ] => inv H
      | [ H: None = Some _ |- _ ] => inv H
      | _ => idtac
    end.

Ltac allinv' :=
  allinv ;
    (match goal with
       | [ H1:  ?f _ _ = _ ,
           H2:  ?f _ _ = _ |- _ ] => rewrite H1 in H2 ; inv H2
     end).

Ltac andb_true_split :=
  try match goal with
    | [|- Is_true _]  => apply Is_true_eq_left
    | [|- true  =  _] => symmetry
    | [|- false <> _] => symmetry; apply not_false_iff_true
    | [|- _ <> false] => apply not_false_iff_true
  end;
  match goal with
    | [|- ?b1 && ?b = true] => apply andb_true_iff; split; try andb_true_split
  end.

(* For when you want to subst/congruence, but you have terms relying on
   "EqDec (eq_setoid A)" lying around. *)
Ltac unsetoid    := repeat match goal with
                      | H : context[complement equiv ?x ?y] |- _ =>
                        replace (complement equiv x y) with (~ equiv x y) in *
                          by auto
                      | |- context[complement equiv ?x ?y] =>
                        replace (complement equiv x y) with (~ equiv x y) in *
                          by auto
                    end;
                    unfold equiv, eq_setoid in *.
Ltac ssubst      := unsetoid; subst.
Ltac scongruence := unsetoid; congruence.

(* NC: Ltac is not exported from [Section]. This is for simplifying
the existential in [predicted_outcome]. *)
Ltac simpl_exists_tag :=
  match goal with
  | [ H: exists _, ?x = (_,_) |- _ ] => destruct H; subst x; simpl
  end.


(* And basic lemmas *)
Lemma rev_nil_nil (A: Type) : forall (l: list A),
  rev l = nil ->
  l = nil.
Proof.
  induction l; intros ; auto.
  simpl in *.
  exploit app_eq_nil ; eauto.
  intros [Hcont1 Hcont2].
  inv Hcont2.
Qed.

(* Function composition *)
Definition compose {A B C : Type} (f : B -> C) (g : A -> B) : A -> C :=
  fun x => f (g x).
Infix "∘" := compose (at level 30).
Arguments compose {A B C} f g / x.

(* Useful functions on lists *)

(* What I wanted to write for group_by (taken from ghc stdlib)
Fixpoint span A (p : A -> bool) (xs : list A) : list A * list A :=
  match xs with
  | nil => (nil,nil)
  | x :: xs' =>
      if p x then
        let (ys,zs) := span p xs' in (x::ys,zs)
      else
        (nil,xs)
  end.

Fixpoint group_by A (e : A -> A -> bool) (xs : list A) : list (list A) :=
  match xs with
  | nil => nil
  | x::xs' => let (ys,zs) := span (e x) xs' in (x::ys) :: group_by e zs
  end.
Error: Cannot guess decreasing argument of fix. *)

(* What I ended up writing for group_by *)
Require Import Omega.
Require Import Recdef.

Definition span' X (p : X -> bool) : forall (xs : list X),
    {x : list X * list X | le (length (snd x)) (length xs)}.
  refine(
    fix span xs :=
      match xs
      return {x : list X * list X | le (length (snd x)) (length xs)}
      with
        | nil => exist _ (nil,nil) _
        | x :: xs' =>
            if p x then
              exist _ (x :: fst (proj1_sig (span xs')),
                       snd (proj1_sig (span xs'))) _
            else
              exist _ (nil,x::xs') _
      end).
  simpl. omega.
  simpl in *. destruct (span xs'). simpl. omega.
  simpl. omega.
Defined.

Function group_by (A : Type) (e : A -> A -> bool)
                  (xs : list A) {measure length xs}
  : list (list A) :=
  match xs with
  | nil => nil
  | x::xs' => (x :: fst (proj1_sig (span' (e x) xs')))
              :: group_by e (snd (proj1_sig (span' (e x) xs')))
  end.
intros. destruct (span' (e x) xs'). simpl. omega.
Defined.

(*
Eval compute in group_by beq_nat (1 :: 2 :: 2 :: 3 :: 3 :: 3 :: nil).
*)

Fixpoint zip_with_keep_rests (A B C : Type) (f : A -> B -> C)
    (xs : list A) (ys : list B) : (list C * (list A * list B)) :=
  match xs, ys with
  | x::xs', y::ys' =>
      let (zs, rest) := zip_with_keep_rests f xs' ys' in
        (f x y :: zs, rest)
  | nil, _ => (nil, (nil, ys))
  | _, nil => (nil, (xs, nil))
  end.

(*
Eval compute in zip_with_keep_rests plus (1 :: 2 :: 3 :: nil)
                                         (1 :: 1 :: nil).

Eval compute in zip_with_keep_rests plus (1 :: 1 :: nil)
                                         (1 :: 2 :: 3 :: nil).
*)

Definition zip_with (A B C : Type) (f : A -> B -> C)
    (xs : list A) (ys : list B) : list C :=
  fst (zip_with_keep_rests f xs ys).

Fixpoint consecutive_with (A B : Type) (f : A -> A -> B) (xs : list A)
    : list B :=
  match xs with
  | nil => nil
  | x1 :: xs' =>
    match xs' with
    | nil => nil
    | x2 :: xs'' => f x1 x2 :: consecutive_with f xs'
    end
  end.

Definition consecutive (A : Type) := consecutive_with (@pair A A).

(*
Eval compute in consecutive (1 :: 2 :: 3 :: 4 :: 5 :: nil).
*)

Fixpoint last_with (A B : Type) (f : A -> B) (l : list A) (d : B) : B :=
  match l with
  | nil => d
  | a :: nil => f a
  | a :: l => last_with f l d
  end.

Definition last_opt (A : Type) xs := last_with (@Some A) xs None.

(*
Eval compute in last_opt (1 :: 2 :: 3 :: nil).
Eval compute in last_opt (@nil nat).
*)

Fixpoint snoc (A : Type) (xs : list A) (y : A) : list A :=
  match xs with
  | nil => y :: nil
  | x :: xs' => x :: (snoc xs' y)
  end.

Fixpoint init (X : Type) (xs : list X) : list X :=
  match xs with
  | nil => nil
  | x1 :: xs' =>
    match xs' with
    | nil => nil
    | x2 :: xs'' => x1 :: (init xs')
    end
  end.

(*
Eval compute in init (1 :: 2 :: 3 :: nil).
Eval compute in init (1 :: nil).
Eval compute in init (@nil nat).
*)
(** * Finite and infinite traces *)

CoInductive trace (A : Type) : Type :=
  | TNil : trace A
  | TCons : A -> trace A -> trace A.

Implicit Arguments TNil [A].

Fixpoint list_to_trace (A : Type) (xs : list A) : trace A :=
  match xs with
  | nil => TNil
  | x :: xs' => TCons x (list_to_trace xs')
  end.

CoFixpoint map_trace (A B: Type) (f: A -> B) (t: trace A) : trace B :=
  match t with
    | TNil => TNil
    | TCons a ta => TCons (f a) (map_trace f ta)
  end.

Definition frob A (t : trace A) : trace A :=
  match t with
    | TCons h t' => TCons h t'
    | TNil => TNil
  end.

Theorem frob_eq : forall A (t : trace A), t = frob t.
  destruct t; reflexivity.
Qed.

Lemma nth_error_nil : forall A pc,
  nth_error nil pc = @None A .
Proof.
  induction pc; auto.
Qed.

Definition index_list_Z A i (xs: list A) : option A :=
  if Z.ltb i 0 then
    None
  else
    nth_error xs (Z.to_nat i).

Lemma index_list_Z_nil : forall A i,
  index_list_Z i nil = @None A .
Proof.
  intros. unfold index_list_Z. destruct (i <? 0)%Z. auto. apply nth_error_nil.
Qed.

Lemma index_list_Z_nat (A: Type) :
  forall l i (v:A),
    index_list_Z i l = Some v ->
    nth_error l (Z.to_nat i) = Some v.
Proof.
  intros. unfold index_list_Z in *. destruct (i <? 0)%Z. congruence. auto.
Qed.

Lemma nth_error_cons (T: Type): forall n a (l:list T),
 nth_error l n = nth_error (a :: l) (n+1)%nat.
Proof.
  intros.
  replace ((n+1)%nat) with (S n) by omega.
  gdep n. induction n; intros.
  destruct l ; simpl; auto.
  destruct l. auto.
  simpl. eauto.
Qed.

Lemma index_list_Z_cons (T: Type): forall i (l1: list T) a,
  (i >= 0)%Z ->
  index_list_Z i l1 = index_list_Z (i+1) (a::l1).
Proof.
  induction i; intros.
  auto.
  unfold index_list_Z. simpl.
  replace (Pos.to_nat (p + 1)) with ((Pos.to_nat p)+1)%nat by (zify; omega).
  eapply nth_error_cons with (l:= l1) (a:= a) ; eauto.
  zify; omega.
Qed.

Lemma index_list_Z_app:
  forall (T : Type)  (l1 l2: list T) (i : Z),
  i = Z.of_nat (length l1) -> index_list_Z i (l1 ++ l2) = index_list_Z 0 l2.
Proof.
  induction l1; intros.
  simpl in *. subst. auto.
  simpl (length (a::l1)) in H.  zify.
  simpl.
  replace i with (i - 1 + 1)%Z by omega.
  erewrite <- index_list_Z_cons by try omega.
  eapply IHl1. omega.
Qed.

Lemma index_list_Z_eq (T: Type) : forall (l1 l2: list T),
  (forall i, index_list_Z i l1 = index_list_Z i l2) ->
  l1 = l2.
Proof.
  induction l1; intros.
  destruct l2 ; auto.
  assert (HCont:= H 0%Z). inv HCont.
  destruct l2.
  assert (HCont:= H 0%Z). inv HCont.
  assert (a = t).
  assert (Helper:= H 0%Z). inv Helper. auto.
  inv H0.
  erewrite IHl1 ; eauto.
  intros. destruct i.
  erewrite index_list_Z_cons with (a:= t); eauto; try omega.
  erewrite H ; eauto.
  erewrite index_list_Z_cons with (a:= t); eauto; try (zify ; omega).
  erewrite H ; eauto. symmetry. eapply index_list_Z_cons; eauto. zify; omega.
  destruct l1, l2 ; auto.
Qed.

Lemma nth_error_Some (T:Type): forall n (l:list T) v,
   nth_error l n = Some v -> n < length l. (* APT: converse isn't true, due to quantification of v! *)
Proof.
  induction n. 
  - intros. destruct l; inv H.  simpl; omega. 
  - intros. destruct l; inv H.  simpl. pose proof (IHn _ _ H1).  omega. 
Qed.

Lemma index_list_Z_Some (T:Type): forall i (l:list T) v,  (* APT: ditto *)
   index_list_Z i l = Some v -> (0 <= i < Z.of_nat (length l))%Z.
Proof.
  unfold index_list_Z. intros. 
  destruct (i <? 0)%Z eqn:?. inv H. 
  pose proof (nth_error_Some H). clear H.
  rewrite Z.ltb_nlt in Heqb.
  zify. rewrite Z2Nat.id in H0; omega. 
Qed.

Fixpoint update_list A (n : nat) (y : A) (xs : list A) : option (list A) :=
  match xs, n with
  | nil, _ => None
  | _ :: xs', 0 => Some (y :: xs')
  | a :: xs', S n' =>
    match update_list n' y xs' with
      | None => None
      | Some l => Some (a::l)
    end
  end.

Lemma update_some_not_nil : forall A (v:A) l a l',
  update_list a v l = Some l' ->
  l' = nil ->
  False.
Proof.
  destruct l; intros.
  destruct a ; simpl in * ; congruence.
  destruct a0 ; simpl in *. congruence.
  destruct update_list.  inv H.
  congruence.
  congruence.
Qed.

Definition update_list_Z A i y (xs: list A) : option (list A) :=
  if Z.ltb i 0 then
    None
  else
    update_list (Z.to_nat i) y xs.


Lemma update_Z_some_not_nil : forall A (v:A) l i l',
  update_list_Z i v l = Some l' ->
  l' = nil ->
  False.
Proof.
  intros. unfold update_list_Z in *.  destruct (i <? 0)%Z. congruence.
  eapply update_some_not_nil; eauto.
Qed.


Lemma update_list_Z_nat (A: Type) (v:A) l i l':
  update_list_Z i v l = Some l' ->
  update_list (Z.to_nat i) v l = Some l'.
Proof.
  intros. unfold update_list_Z in *. destruct (i <? 0)%Z. congruence.
  auto.
Qed.

Lemma update_list_spec (T: Type) : forall (v: T) l a l',
  update_list a v l = Some l' ->
  nth_error l' a = Some v.
Proof.
  induction l ; intros.
  destruct a ; simpl in *; inv H.
  destruct a0 ; simpl in *; inv H; auto.
  case_eq (update_list a0 v l) ; intros ; rewrite H in * ; inv H1.
  auto.
Qed.

Lemma update_list_Z_spec (T: Type) : forall (v: T) l a l',
  update_list_Z a v l = Some l' ->
  index_list_Z a l' = Some v.
Proof.
  unfold update_list_Z, index_list_Z. intros.
  destruct (a <? 0)%Z.  congruence.
  eapply update_list_spec; eauto.
Qed.

Lemma update_list_spec2 (T:Type) : forall (v:T) l n n' l',
  update_list n v l = Some l' ->
  n <> n' ->
  nth_error l n' = nth_error l' n'.
Proof.
  induction l; intros.
  destruct n; simpl in *; inv H.
  destruct n.
    destruct n'.
      exfalso; omega.
      destruct l'; inv H.
      simpl. auto.
    destruct n'.
      destruct l'; inv H.
        destruct (update_list n v l); inv H2.
        destruct (update_list n v l); inv H2.
        auto.
      destruct l'; inv H.
        destruct (update_list n v l); inv H2.
        simpl.
        destruct  (update_list n v l) eqn:?; inv H2.
        eapply IHl; eauto.
Qed.

Lemma update_list_Z_spec2 (T:Type) : forall (v:T) l a a' l',
  update_list_Z a v l = Some l' ->
  a' <> a ->
  index_list_Z a' l = index_list_Z a' l'.
Proof.
  unfold update_list_Z, index_list_Z. intros.
  destruct (a <? 0)%Z eqn:?. congruence.
  destruct (a' <? 0)%Z eqn:?. auto.
  eapply update_list_spec2; eauto.
  apply Z.ltb_ge in Heqb.
  apply Z.ltb_ge in Heqb0.
  intro. apply H0. apply Z2Nat.inj; eauto.
Qed.

Lemma update_list_Some (T: Type) (v: T) l n :
  n < length l <-> exists l', update_list n v l = Some l'.
Proof.
revert n v; induction l; intros n v; constructor; simpl; try omega.
+ destruct n; simpl; intros [l]; discriminate.
+ destruct n; intros lt_n; simpl.
    now exists (v :: l).
  apply lt_S_n in lt_n.
  destruct (IHl n v) as [IH _]; destruct (IH lt_n) as [l' upd_l'].
  now exists (a :: l'); rewrite upd_l'.
+ destruct n; simpl; try omega.
  intros [l' upd_l]; apply lt_n_S, (IHl n v).
  destruct (update_list n v l) as [l''|]; try discriminate.
now exists l''.
Qed.

Lemma valid_update T i (l : list T) x : index_list_Z i l = Some x ->
  forall x', exists l', update_list_Z i x' l = Some l'.
Proof.
  intros.
  unfold index_list_Z, update_list_Z in *.
  destruct (i <? 0)%Z; try congruence.
  - remember (Z.to_nat i) as n; clear Heqn.
    generalize dependent n.
    generalize dependent l.
    induction l; intros.
    + rewrite nth_error_nil in H. discriminate.
    + destruct n; simpl in *.
      * simpl; eauto.
      * simpl in *.
        edestruct IHl as [l' Hl']; eauto.
        rewrite Hl'. eauto.
Qed.

Definition swap T n (l : list T) : option (list T) :=
  match l with
    | nil => None
    | y :: l' =>
      match nth_error (y :: l') n with
        | Some x => update_list n y (x :: l')
        | None => None
      end
  end.

Lemma filter_cons_inv_strong :
  forall X (l1 : list X) x2 l2
         (f : X -> bool),
    x2 :: l2 = filter f l1 ->
    exists l11 l12,
      l1 = l11 ++ l12 /\
      filter f l11 = x2 :: nil /\
      filter f l12 = l2.
Proof.
  intros X l1.
  induction l1 as [|x1 l1 IH]; simpl; try congruence.
  intros.
  destruct (f x1) eqn:E.
  - exists (x1 :: nil).
    exists l1.
    simpl.
    rewrite E.
    inv H.
    eauto.
  - exploit IH; eauto.
    clear IH.
    intros [l11 [l12 [H1 [H2 H3]]]].
    subst.
    exists (x1 :: l11).
    exists l12.
    simpl.
    rewrite E. eauto.
Qed.

Lemma filter_cons_inv :
  forall A (f : A -> bool) a l1 l2,
    a :: l1 = filter f l2 ->
    exists l2', l1 = filter f l2'.
Proof.
  induction l2 as [|a' l2 IH]; simpl. congruence.
  destruct (f a'); intros H; auto.
  inv H. eauto.
Qed.

Lemma filter_app :
  forall X (l1 l2 : list X) (f : X -> bool),
    filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
Proof.
  induction l1 as [|x l1 IH]; simpl; intros. trivial.
  rewrite IH. destruct (f x); auto.
Qed.

Lemma update_list_Z_Some (T:Type): forall (v:T) l (i:Z),
  (0 <= i < Z.of_nat (length l))%Z <->
  exists l', update_list_Z i v l = Some l'.
Proof.
intros. unfold update_list_Z.
destruct (i <? 0)%Z eqn:?.
- apply Z.ltb_lt in Heqb; constructor; try omega.
  intros []; discriminate.
- constructor.
    intros [pos_i lt_i].
    rewrite <-(Z2Nat.id _ pos_i) in lt_i.
    apply Nat2Z.inj_lt in lt_i.
    now eapply update_list_Some; eauto.
    intros H; apply update_list_Some in H.
  apply Z.ltb_ge in Heqb.
  split; try easy.
  rewrite <-(Z2Nat.id _ Heqb).
  now apply Nat2Z.inj_lt.
Qed.

Lemma length_update_list : forall T a (vl:T) m m',
  update_list a vl m = Some m' ->
  length m' = length m.
Proof.
  induction a; intros.
  - destruct m; simpl in *.
    + inv H.
    + inversion H; subst; reflexivity.
  - destruct m; simpl in *.
    + inv H.
    + destruct (update_list a vl m) eqn:?.
      * exploit IHa; eauto.
        inversion H; subst.
        intros eq; rewrite <- eq; reflexivity.
      * inv H.
Qed.

Lemma length_update_list_Z A i v (l l' : list A) : update_list_Z i v l = Some l' ->
  length l' = length l.
Proof.
unfold update_list_Z.
destruct (i <? 0)%Z; try discriminate.
intros H; apply (length_update_list H).
Qed.

Lemma app_same_length_eq (T: Type): forall (l1 l2 l3 l4: list T),
  l1++l2 = l3++l4 ->
  length l1 = length l3 ->
  l1 = l3.
Proof.
  induction l1; intros; simpl in *.
  destruct l3; auto. inv H0.
  destruct l3. inv H0. simpl in *.
  inv H. erewrite IHl1 ; eauto.
Qed.

Lemma app_same_length_eq_rest (T: Type): forall (l1 l2 l3 l4: list T),
  l1++l2 = l3++l4 ->
  length l1 = length l3 ->
  l2 = l4.
Proof.
  intros.
  exploit app_same_length_eq; eauto.
  intro Heq ; inv Heq.
  gdep l3. induction l3 ; intros; auto.
  simpl in *.
  inv H. eauto.
Qed.

Definition is_some {T} (o : option T) :=
  match o with
    | Some _ => true
    | None => false
  end.

Definition remove_none {T} (l : list (option T)) :=
  filter (@is_some _) l.

Inductive with_silent {T:Type} := | E (e:T) | Silent.
Notation "T +τ" := (@with_silent T) (at level 1).

Inductive match_actions {T1 T2} (match_events : T1 -> T2 -> Prop) : T1+τ -> T2+τ -> Prop :=
| match_actions_silent : match_actions match_events Silent Silent
| match_actions_event : forall e1 e2,
  match_events e1 e2 -> match_actions match_events (E e1) (E e2).

(** Reflexive transitive closure. *)
Definition op_cons (E: Type) (oe: E+τ) (l: list E) :=
  match oe with
      | E e => e::l
      | Silent => l
  end.


Inductive star (S E: Type) (Rstep: S -> E+τ -> S -> Prop): S -> list E -> S -> Prop :=
  | star_refl: forall s,
      star Rstep s nil s
  | star_step: forall s1 s2 s3 e t t',
      Rstep s1 e s2 -> star Rstep s2 t s3 ->
      t' = (op_cons e t) ->
      star Rstep s1 t' s3.
Hint Constructors star.

Lemma op_cons_app : forall E (e: E+τ) t t', (op_cons e t)++t' = op_cons e (t++t').
Proof. intros. destruct e; reflexivity. Qed.

Lemma star_right : forall S E (Rstep: S -> E+τ -> S -> Prop) s1 s2 t,
                     star Rstep s1 t s2 ->
                     forall s3 e t',
                       Rstep s2 e s3 ->
                       t' = (t++(op_cons e nil)) ->
                       star Rstep s1 t' s3.
Proof.
  induction 1; intros.
  eapply star_step; eauto.
  exploit IHstar; eauto. intros.
  inv H3. rewrite op_cons_app; eauto.
Qed.

Inductive plus (S E: Type) (Rstep: S -> E+τ -> S -> Prop): S -> list E -> S -> Prop :=
  | plus_step: forall s t s' e,
      Rstep s e s' ->
      t = (op_cons e nil) ->
      plus Rstep s t s'
  | plus_trans: forall s1 s2 s3 e t t',
      Rstep s1 e s2 -> plus Rstep s2 t s3 ->
      t' = (op_cons e t) ->
      plus Rstep s1 t' s3.

Hint Constructors star.
Hint Constructors plus.

Lemma plus_right : forall E S (Rstep: S -> E+τ -> S -> Prop) s1 s2 t,
                     plus Rstep s1 t s2 ->
                     forall s3 e t',
                       t' = (t++(op_cons e nil)) ->
                       Rstep s2 e s3 -> plus Rstep s1 t' s3.
Proof.
  induction 1; intros.
  inv H1.
  rewrite op_cons_app. simpl.
  eapply plus_trans; eauto.
  exploit IHplus; eauto.
  inv H2. rewrite op_cons_app.  eauto.
Qed.

Lemma step_star_plus :
  forall (S E: Type)
         (Rstep: S -> E+τ -> S -> Prop) s1 t s2
         (STAR : star Rstep s1 t s2)
         (NEQ : s1 <> s2),
    plus Rstep s1 t s2.
Proof.
  intros. inv STAR. congruence.
  clear NEQ.
  gdep e. gdep s1.
  induction H0; subst; eauto.
Qed.
Hint Resolve step_star_plus.

Lemma star_trans: forall S E (Rstep: S -> E+τ -> S -> Prop) s0 t s1,
  star Rstep s0 t s1 ->
  forall t' s2,
  star Rstep s1 t' s2 ->
  star Rstep s0 (t++t') s2.
Proof.
  induction 1.
  - auto.
  - inversion 1.
    + rewrite app_nil_r.
      subst; econstructor; eauto.
    + subst; econstructor; eauto.
      rewrite op_cons_app; reflexivity.
Qed.

Fixpoint replicate T (a: T) n : list T :=
  match n with
    | O => nil
    | S n => a::(replicate a n)
  end.

Lemma nth_error_In :
  forall T n (l : list T) (x : T),
    nth_error l n = Some x ->
    In x l.
Proof.
  intros.
  gdep l.
  induction n as [|n IH]; intros l H; destruct l as [|x' l]; simpl in *;
  try solve [inv H].
  - inv H. auto.
  - auto.
Qed.
Hint Resolve nth_error_In.

Lemma update_list_In :
  forall T n x y (l l' : list T)
         (UPD: update_list n x l = Some l')
         (IN: In y l'),
    y = x \/ In y l.
Proof.
  induction n as [|n IH]; intros; destruct l as [|x' l]; simpl in *;
  try solve [inv UPD].
  - inv UPD. destruct IN; eauto.
  - destruct (update_list n x l) as [l''|] eqn:UPD'; inv UPD.
    destruct IN; auto.
    exploit IH; eauto.
    intros []; eauto.
Qed.

Lemma swap_In :
  forall T n (l l' : list T) x
         (SWAP : swap n l = Some l')
         (IN : In x l'),
    In x l.
Proof.
  unfold swap.
  intros.
  destruct l as [|y l]; try congruence.
  destruct n as [|n]; simpl in *.
  - inv SWAP. eauto.
  - destruct (nth_error l n) as [x'|] eqn:IDX; try congruence.
    destruct (update_list n y l) as [l''|] eqn:UPD; try congruence.
    inv SWAP.
    destruct IN as [H | H]; subst; eauto.
    clear - UPD H.
    exploit update_list_In; eauto.
    intros []; auto.
Qed.

Lemma index_list_app :
  forall T n (l1 l2 : list T) x,
    nth_error l1 n = Some x ->
    nth_error (l1 ++ l2) n = Some x.
Proof.
  induction n as [|n IH]; intros [|x' l1] l2 x H; simpl in *;
  try solve [inv H]; auto.
Qed.

Lemma update_list_app :
  forall T n x (l1 l1' l2 : list T)
         (UPD : update_list n x l1 = Some l1'),
    update_list n x (l1 ++ l2) = Some (l1' ++ l2).
Proof.
  induction n; intros;
  destruct l1 as [|x' l1]; simpl in *; allinv; auto.
  destruct (update_list n x l1) as [l1''|] eqn:UPD'; allinv.
  erewrite IHn; eauto.
  simpl.
  reflexivity.
Qed.

Lemma swap_app :
  forall T n (l1 l1' l2 : list T)
         (SWAP : swap n l1 = Some l1'),
    swap n (l1 ++ l2) = Some (l1' ++ l2).
Proof.
  unfold swap.
  intros.
  destruct l1 as [|y l1]; simpl; try congruence.
  destruct (nth_error (y :: l1) n) as [x|] eqn:SWAP'; allinv.
  eapply index_list_app in SWAP'.
  simpl in SWAP'.
  rewrite SWAP'.
  eapply update_list_app in SWAP.
  simpl in *.
  eauto.
Qed.

Lemma swap_forall :
  forall T (P : T -> Prop) n l l'
         (SWAP : swap n l = Some l')
         (FORALL : forall x, In x l -> P x),
    forall x, In x l' -> P x.
Proof.
  unfold swap.
  intros.
  destruct l as [|y l]; try congruence.
  destruct (nth_error (y :: l) n) as [x'|] eqn:IDX; try congruence.
  destruct n as [|n]; simpl in *; allinv; simpl in *; eauto.
  match goal with
    | H : (match ?UP with _ => _ end) = _ |- _ =>
      destruct UP as [l''|] eqn:?; simpl in *; try congruence
  end.
  allinv.
  destruct H.
  - subst. eauto.
  - exploit update_list_In; eauto.
    intros [? | ?]; subst; eauto.
Qed.

Fixpoint drop {X:Type} (n:nat) (xs:list X) : list X :=
match n with
| O => xs
| S n' => match xs with
          | nil => nil
          | (x::xs') => drop n' xs'
          end
end.

Definition dropZ {X:Type} (z:Z) (xs:list X) : list X :=
  if (z <? 0)%Z then
    xs
  else drop (Z.to_nat z) xs.


Lemma length_drop : forall {X:Type} n (xs:list X),
           length (drop n xs) = ((length xs) -  n)%nat.
Proof.
  intros X n. induction n; intros xs.
    simpl. omega.
    destruct xs. simpl.
       auto.
       simpl. auto.
Qed.

Lemma drop_cons : forall {X:Type} p (l : list X),
    (p < length l)%nat ->
    exists x,
      drop p l = x :: drop (S p) l.
Proof.
  induction p; intros [|x l] H; simpl in *; try omega; eauto.
  apply IHp.
  omega.
Qed.

Import ListNotations.

Lemma dropZ_all: forall {X:Type} (xs:list X),
  (dropZ (Z.of_nat (length xs)) xs = []).
Proof.
  intros.
  destruct (dropZ (Z.of_nat (length xs)) xs) eqn:E. auto.
  exfalso.
  unfold dropZ in E.  destruct (Z.of_nat (length xs) <? 0)%Z eqn:M.
    apply Z.ltb_lt in M.  omega.
    rewrite Nat2Z.id in E.
    assert (length (drop (length xs) xs) = length (x::l)). rewrite E; auto.
    rewrite length_drop in H. simpl in H. replace (length xs - length xs)%nat with O in H by omega. inv H.
Qed.

Inductive match_options {A B} (R : A -> B -> Prop) : option A -> option B -> Prop :=
| mo_none : match_options R None None
| mo_some : forall a b, R a b -> match_options R (Some a) (Some b).

Lemma Forall2_length :
  forall A B (R : A -> B -> Prop) l1 l2,
    Forall2 R l1 l2 -> length l1 = length l2.
Proof.
  induction 1; eauto; simpl; congruence.
Qed.

Fixpoint take {T} (n : nat) (l : list T) : list T :=
  match n with
    | O => []
    | S n' =>
      match l with
        | [] => []
        | x :: l' => x :: take n' l'
      end
  end.

Lemma nth_error_app' X : forall (l1 l2 : list X) (x : X),
                            nth_error (l1 ++ x :: l2) (length l1) = Some x.
Proof.
  induction l1 as [|x' l1 IH]; intros; simpl in *; subst; eauto.
Qed.

Definition bind (A B:Type) (f:A->option B) (a:option A) : option B :=
    match a with
      | None => None
      | Some a => f a
    end.

Lemma bind_inv A B (f : A -> option B) (a : option A) (b : B) :
  bind f a = Some b -> exists a', a = Some a' /\ f a' = Some b.
Proof.
  destruct a as [a'|]; simpl; solve [eauto | discriminate].
Qed.

(* This notation breaks parsing of the "do" tactical, so it should be
packaged in a module. *)
Module DoNotation.

Notation "'do!' X <- A ; B" :=
  (bind (fun X => B) A)
  (at level 200, X ident, A at level 100, B at level 200).

Notation "'do!' X : T <- A ; B" :=
  (bind (fun X : T => B) A)
  (at level 200, X ident, A at level 100, B at level 200).

End DoNotation.

Definition error {A} : option A := None.

Fixpoint ble_nat (m n:nat) : bool :=
  match m,n with
    | O,_ => true
    | _,O => false
    | S m',S n' => ble_nat m' n'
  end.

Module PartMaps.

Section maps.

Variables M K V : Type.

Class partial_map := {
  get : M -> K -> option V;
  upd : M -> K -> V -> option M
}.

Class axioms (pm : partial_map) := mkAxioms {

  upd_defined : forall m key val val',
                  get m key = Some val ->
                  exists m',
                    upd m key val' = Some m';

  upd_inv : forall m key val' m',
              upd m key val' = Some m' ->
              exists val,
                get m key = Some val;

  get_upd_eq : forall m m' key val,
                 upd m key val = Some m' ->
                 get m' key = Some val;

  get_upd_neq : forall m m' key key' val,
                  key' <> key ->
                  upd m key val = Some m' ->
                  get m' key' = get m key'

}.

Section with_classes.

Context {pm : partial_map}
        {a : axioms pm}
        {eqk : EqDec (eq_setoid K)}.

Fixpoint upd_list (m : M) (ps : list (K * V)) : option M :=
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
    destruct (k == k') as [E|E]; simpl in E; subst.
    + erewrite get_upd_eq in GET; eauto. inv GET. eauto.
    + erewrite (get_upd_neq E) in GET; [|eauto].
      specialize (IH m'' eq_refl GET). intuition.
Qed.

Lemma defined_preserved m m' key key' val val' :
  get m key = Some val ->
  upd m key' val' = Some m' ->
  exists val'', get m' key = Some val''.
Proof.
  intros GET UPD.
  destruct (key' == key) as [E|E]; simpl in E; subst.
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
    destruct (IH _ eq_refl) as [v' GET'].
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
  - destruct (k' == k) as [E|E]; simpl in E; subst.
    + erewrite get_upd_eq; eauto.
    + erewrite get_upd_neq; eauto.
      destruct (IH m'' eq_refl IN) as (v' & IN' & GET).
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
    rewrite <- (IH _ eq_refl); eauto.
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
    destruct (DEF k (or_introl eq_refl)) as [v' GET].
    destruct (upd_list_defined_preserved GET UPD) as [v'' GET'].
    eapply upd_defined; eauto.
Qed.

End with_classes.

End maps.

Section PartMapPointwise.

Context {M1 M2 K V1 V2 : Type}
        {pm1 : partial_map M1 K V1}
        {pm2 : partial_map M2 K V2}.

Definition pointwise (P : V1 -> V2 -> Prop) (m1 : M1) (m2 : M2) : Prop :=
  forall k : K,
    match get m1 k, get m2 k with
    | None   , None   => True
    | Some v1, Some v2 => P v1 v2
    | _      , _      => False
    end.

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

Definition same_domain := pointwise (fun _ _ => True).

End PartMapPointwise.

Section PartMapDomains.
Variable M M' M'' K V V' V'' : Type.

Context {pm : partial_map M K V}
        {a : axioms pm}

        {pm' : partial_map M' K V'}
        {a' : axioms pm'}

        {pm'' : partial_map M'' K V''}
        {a'' : axioms pm''}.

Lemma same_domain_trans (m : M) (m' : M') (m'' : M'') :
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

Lemma same_domain_comm (m : M) (m' : M') :
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

End PartMaps.

Module TotalMaps.

Section total_maps.

Variable M A B : Type.

Class total_map := {
  get : M -> A -> B;
  upd : M -> A -> B -> M
}.

Record axioms (tm : total_map) := mkAxioms {

  get_upd_eq : forall m key val, get (upd m key val) key = val;

  get_upd_neq : forall m key key' val,
                  key' <> key ->
                  get (upd m key val) key' = get m key'

}.

End total_maps.

End TotalMaps.

(*
Require Import Relations.

Notation "R *" := (clos_refl_trans_1n R)
  (at level 8, left associativity):relation_scope.
*)

Fixpoint assoc_list_lookup {T1 T2 : Type} (xys : list (T1*T2))
    (select : T1 -> bool) : option T2 :=
  match xys with
  | [] => None
  | (x,y) :: xys' => if select x then Some y
                      else assoc_list_lookup xys' select
  end.

Section EqDec.

Context {A : Type}
        {E : EqDec (eq_setoid A)}.

Lemma eqb_refl (x : A) : (x ==b x) = true.
Proof.
  unfold equiv_decb.
  destruct (equiv_dec x x); congruence.
Qed.

Lemma eqb_true_iff (x y : A) : (x ==b y) = true <-> x = y.
Proof.
  unfold equiv_decb.
  destruct (equiv_dec x y); simpl in *; split; congruence.
Qed.

Lemma eqb_false_iff (x y : A) : (x ==b y) = false <-> x <> y.
Proof.
  unfold equiv_decb.
  destruct (equiv_dec x y); simpl in *; split; congruence.
Qed.

End EqDec.

Require Import Recdef.
Require Import Omega.

Section In2.

Variable A : Type.

Variable x y : A.
(*
Function In2 (zs : list A) {measure length zs} : Prop :=
  match zs with
  | z1 :: z2 :: zs' => (z1 = x /\ z2 = y) \/ (In2 (z2 :: zs'))
  | _ => False
  end.
Proof. intros. simpl. omega. Defined.
*)
Fixpoint In2 (l : list A) {struct l} : Prop :=
  match l with
      | nil => False
      | a :: l' => 
        match l' with
          | nil => False
          | b :: l'' => (a = x /\ b = y) \/ (In2 l')
        end
  end.


Lemma in2_strengthen :
  forall zs ys,
    In2 zs ->
    In2 (ys ++ zs).
Proof.
  intros zs ys IN2.
  destruct zs. inversion IN2.
  induction ys. auto.
  destruct ys. simpl. right. assumption.
  simpl. right. auto.
Qed.

Lemma in2_strengthen' :
  forall zs ys,
    In2 zs ->
    In2 (zs ++ ys).
Proof.
  induction zs as [|z1 [|z2 zs]]; try solve [inversion 1].
  intros ys [[-> ->] | IN2]; [left | right]; auto.
Qed.

Lemma in2_trivial : forall xs ys,
  In2 (xs ++ x :: y :: ys).
Proof.
  intros xs ys. induction xs; intros. simpl; auto.
  simpl. 
  destruct (xs ++ x :: y :: ys). inversion IHxs.
  right; assumption.
Qed.

Lemma in2_reverse : forall xs i j,
  In2 (xs ++ [i;j]) ->
  In2 (xs ++ [i]) \/ i = x /\ j = y.
Proof. 
  intros xs i j IN2.
  induction xs.
  - right. simpl in IN2; destruct IN2 as [[EQ1 EQ2] | CONTRA]; [auto | inversion CONTRA]. 
  - destruct xs. simpl in IN2. 
    { destruct IN2 as [[EQ1 EQ2] | [[EQ1 EQ2] | CONTRA]]; subst.
      *  left. simpl; auto.
      * right; auto.
      * destruct CONTRA. }
    { destruct IN2 as [[EQ1 EQ2] | IN2]; subst.
      * left; simpl; auto.
      * destruct (IHxs IN2) as [IN2' | [EQ1 EQ2]].
        + left. simpl. right. auto.
        + right; auto.
    }
Qed.
    
End In2. 

Section exec.

(* Several notions of execution. Essentially variations on the
   reflexive-transitive closure of a relation. *)

Variable A : Type.
Variable R : A -> A -> Prop.

(* Here's an inductive predicate we could use to state the kernel
   correctness theorem in a non-deterministic setting: *)
Inductive nexec (P Q : A -> Prop) (x : A) : Prop :=
| ne_stop : ~ P x -> Q x -> nexec P Q x
| ne_step : forall x', R x x' -> P x ->
                       (forall x', R x x' -> nexec P Q x') ->
                       nexec P Q x.

Inductive restricted_exec (P : A -> Prop) : A -> A -> Prop :=
| re_refl (x : A) : P x -> restricted_exec P x x
| re_step (x y z : A) : P x -> R x y ->
                        restricted_exec P y z ->
                        restricted_exec P x z.
Hint Constructors restricted_exec.

Lemma restricted_exec_fst P (x y : A) :
  restricted_exec P x y -> P x.
Proof. intro H. inv H; trivial. Qed.

Lemma restricted_exec_snd P (x y : A) :
  restricted_exec P x y -> P y.
Proof. induction 1; eauto. Qed.

Lemma restricted_exec_trans P (x y z : A) :
  restricted_exec P x y ->
  restricted_exec P y z ->
  restricted_exec P x z.
Proof. induction 1; eauto. Qed.
Hint Resolve restricted_exec_trans.

Inductive exec_until (P Q : A -> Prop) x y : Prop :=
| eu_intro (z : A) : restricted_exec P x z -> Q y -> R z y -> exec_until P Q x y.

Lemma nexec_exists_exec_until P Q x :
  nexec P Q x ->
  P x ->
  exists x', exec_until P (fun x => ~ P x) x x' /\
             Q x'.
Proof.
  intros EXEC H.
  induction EXEC as [ | x x' STEP Hx' EXEC IH ]; try tauto.
  specialize (EXEC x' STEP). specialize (IH x' STEP).
  inversion EXEC as [HNP HQ|x'' STEP' HP EXEC']; subst; clear EXEC.
  - exists x'. split; eauto. econstructor; eauto.
  - specialize (IH HP). destruct IH as (x''' & EXEC & POST).
    eexists x'''. split; eauto.
    destruct EXEC.
    econstructor; trivial.
    * eapply re_step; eauto.
    * trivial.
Qed.

Hypothesis determ : forall s s1 s2, R s s1 -> R s s2 -> s1 = s2.

Lemma exec_until_determ P Q1 Q2 s s1 s2 :
  exec_until P Q1 s s1 -> (forall s, P s -> Q1 s -> False) ->
  exec_until P Q2 s s2 -> (forall s, P s -> Q2 s -> False) ->
  s1 = s2.
Proof.
  intros [s1' EXEC1 H1' STEP1'] INCOMP1 [s2' EXEC2 H2' STEP2'] INCOMP2.
  induction EXEC1 as [s H1 |s s1' s1'' H1 STEP1 EXEC1 IH].
  - inversion EXEC2 as [|? s2'' ? H2'' STEP2]; subst; clear EXEC2; eauto.
    assert (s1 = s2'') by eauto. subst s2''.
    assert (P1 : P s1) by (eapply restricted_exec_fst; eauto).
    destruct (INCOMP1 _ P1 H1').
  - inversion EXEC2 as [|? s2'' ? H2'' STEP2]; subst; clear EXEC2.
    + assert (s1' = s2) by eauto. subst s2.
      assert (P1 : P s1') by (eapply restricted_exec_fst; eauto).
      destruct (INCOMP2 _ P1 H2').
    + specialize (IH STEP1').
      assert (s1' = s2'') by eauto. subst s2''.
      now auto.
Qed.

Definition exec := restricted_exec (fun _ => True).
Hint Unfold exec.

Lemma exec_one x y : R x y -> exec x y.
Proof. intros H. eapply re_step; eauto. Qed.

Lemma restricted_exec_weaken P (x y : A) :
  restricted_exec P x y ->
  exec x y.
Proof. induction 1; eauto. Qed.

Lemma exec_until_weaken P Q x y :
  exec_until P Q x y ->
  exec x y.
Proof.
  intros [z EXEC _ STEP].
  eapply restricted_exec_trans.
  - eapply restricted_exec_weaken; eauto.
  - eapply exec_one. trivial.
Qed.

Inductive single : A -> A -> Prop :=
  | single_refl : forall x, single x x
  | single_single : forall (x y : A), R x y -> single x y.
Hint Constructors single.

(* Capture steps from s to s' (with s') *)
Inductive interm : list A -> A -> A -> Prop :=
  | interm_single : forall (x y : A), R x y -> interm [x;y] x y
  | interm_multi : forall (x y z : A) (xs : list A),
                    R x y ->
                    interm xs y z ->
                    interm (x :: xs) x z.
Hint Constructors interm.

Inductive interm_reverse : list A -> A -> A -> Prop :=
  | intermrev_single : forall (x y : A), R x y -> interm_reverse [x;y] x y
  | intermrev_multi : forall (x y z : A) (xs : list A),
                      R y z ->
                      interm_reverse xs x y ->
                      interm_reverse (xs ++ [z]) x z.
Hint Constructors interm_reverse.

Inductive intermr : list A -> A -> A -> Prop :=
  | intermr_refl : forall x, intermr [x] x x
  | intermr_multi : forall (x y z : A) (xs : list A),
                    R x y ->
                    intermr xs y z ->
                    intermr (x :: xs) x z.
Hint Constructors intermr.

Lemma interm_first_step : forall xs (si s s' : A),
                            interm (si :: xs) s s' ->
                            si = s.
Proof.
  intros xs si s s' INTERM.
  inversion INTERM; subst; auto.
Qed.

Lemma interm_last_step : forall xs (si s s' : A),
                           interm (xs ++ [si]) s s' ->
                           si = s'.
Proof.
  intros xs si s s' INTERM.
  generalize dependent s.
  induction xs; intros s INTERM.
  * simpl in *. inversion INTERM as [? ? STEP|? ? ? ? STEP INTERM2]; subst. inversion INTERM2.
  * inversion INTERM as [? ? STEP |? ? ? ? STEP INTERM2]; subst.
    - destruct xs; simpl. inversion H1 as [EQ]. reflexivity. destruct xs; inversion H1.
    - apply IHxs in INTERM2. assumption.
Qed.

Lemma interm_mid_step : forall xs ys (si sj s s' : A),
                           interm (xs ++ si :: sj :: ys) s s' ->
                           R si sj.
Proof.
  intros xs ys si sj s s' INTERM.
  generalize dependent s.
  induction xs; intros s INTERM.
  * simpl in *. inversion INTERM as [? ? STEP |? ? ? ? STEP INTERM2]; subst. assumption.
    inversion INTERM2; subst; assumption.
  * inversion INTERM as [? ? STEP|? ? ? ? STEP INTERM2]; subst.
    - destruct xs; inversion H1; subst. destruct xs; inversion H1.
    - apply IHxs in INTERM2. assumption.
Qed.

Lemma interm_states_step : forall (s s' si : A) xs,
                             interm xs s s' ->
                             In si xs ->
                             (exists sj, R si sj) \/ si = s'.
Proof.
  intros s s' si xs INTERM IN.
  apply in_split in IN.
  destruct IN as [ys IN].
  destruct IN as [zs IN].
  destruct zs as [| z zs']; subst xs.
  * right. eapply interm_last_step; eassumption.
  * left. apply interm_mid_step in INTERM. eexists. eassumption.
Qed.

Lemma interm_step_upto : forall xs (s s' si : A),
                          In si xs ->
                          interm xs s s' ->
                          (exists zs, interm zs s si) \/ si = s.
Proof.
  intros xs s s' si IN INTERM. generalize dependent si.
  induction INTERM; intros.
  + destruct IN. subst.
    - right. reflexivity.
    - destruct H0. subst. left. eexists. econstructor. assumption.
      destruct H0.
  + destruct IN. subst. right. reflexivity.
    destruct (IHINTERM si H0).
    destruct H1 as [zs H2].
    left. eexists. eapply interm_multi; eauto.
    subst.
    left. exists [x;y]. constructor. auto.
Qed.

Lemma interm_step_upto_strong : forall xs (s s' si : A),
                                  In si xs ->
                                  interm xs s s' ->
                                  (exists zs, interm zs s si /\ forall sj, In sj zs -> In sj xs) \/ si = s.
Proof.
  intros xs s s' si IN INTERM.
  generalize dependent si.
  induction INTERM as [s s' STEP | s s'' s' ? STEP INTERM IHINTERM]; intros.
  + destruct IN as [|IN]; subst.
    - right; reflexivity.
    - destruct IN as [|CONTRA]; subst.
      left. eexists; split; eauto.
      destruct CONTRA.
  + destruct IN as [|IN]; subst.
    - right. reflexivity.
    - destruct (IHINTERM si IN) as [[? [IHINT IHIN]] | IHEQ].
      * left. eexists. split; eauto.
        intros sj INJ. destruct INJ as [|INJ]; subst; simpl; auto.
      * subst. left. exists [s;s'']. split.
        constructor. assumption.
        intros sj INJ. destruct INJ as [|INJ]; subst; simpl; auto.
        destruct INJ as [|INJ]; subst; simpl; auto.
        destruct INJ.
Qed.

Lemma interm_in_first_last : forall xs (s s' : A),
                               interm xs s s' ->
                               In s xs /\ In s' xs.
Proof.
  intros xs s s' INTERM.
  induction INTERM; subst; simpl; try (destruct IHINTERM); auto.
Qed.

Lemma interm_backwards : forall xs s s' s'',
  R s' s'' ->
  interm xs s s' ->
  interm (xs ++ [s'']) s s''.
Proof.
  intros xs s s' s'' STEP INTERM.
  induction INTERM.
  - simpl. eapply interm_multi. eauto.
    eapply interm_single; eauto.
  - eapply interm_multi; eauto.
Qed.

Lemma interm_destruct_last : forall xs s s',
  interm xs s s' ->
  exists ys, interm (ys ++ [s']) s s'.
Proof.
  intros xs s s' INTERM.
  induction INTERM.
  - exists [x]; constructor(assumption).
  - destruct (IHINTERM) as [ys INTERM'].
    exists (x::ys). eapply interm_multi; eauto.
Qed.

Lemma interm_in2_step : forall xs s s' si sj,
  interm xs s s' ->
  In2 si sj xs ->
  R si sj.
Proof.
  intros xs s s' si sj INTERM In2.
  induction INTERM.
  - destruct In2 as [[EQ1 EQ2] | CONTRA]; subst. assumption.
    destruct CONTRA.
  - destruct xs. inversion INTERM.
    inversion INTERM; subst.
    + destruct In3 as [[EQ1 EQ2] | CONTRA]; subst. assumption.
      auto.
    + destruct In3 as [[EQ1 EQ2] | CONTRA]; subst. assumption.
      auto.
Qed.

Lemma list_app_eq : forall {X:Type} xs ys (x y:X),
  xs ++ [x] = ys ++ [y] ->
  xs = ys /\ x = y.
Proof app_inj_tail.

Lemma intermrev_forward : forall xs s s' s'',
  interm_reverse xs s' s'' ->
  R s s' ->
  interm_reverse (s :: xs) s s''.
Proof.
  intro xs.
  induction xs using rev_ind. 
  - intros s s' s'' CONTRA ?. inversion CONTRA; subst. destruct xs; inversion H0.
  - intros.
    inversion H; subst.
    + assert (REW : [s;s';s''] = [s;s'] ++ [s'']) by reflexivity. rewrite REW.
      eapply intermrev_multi; eauto.
    + apply list_app_eq in H1. destruct H1; subst.
      apply IHxs with (s := s) in H3. 
      rewrite app_comm_cons.
      eapply intermrev_multi; eauto. assumption.
Qed.

Lemma interm_equiv_intermrev : forall xs s s',
  interm xs s s' <-> interm_reverse xs s s'.
Proof.

  intros xs s s'.
  split.
  - intro INTERM. generalize dependent s.
    induction xs. intros s CONTRA. inversion CONTRA.
    intros s INTERM.
    inversion INTERM; subst; eauto.
    apply intermrev_forward with (s' := y). apply IHxs. assumption. assumption.
  - intros INTERMREV.
    induction INTERMREV; eauto.
    eapply interm_backwards; eauto.
Qed.

(* Lemmas about intermr *)
Lemma intermr_first_step : forall xs (si s s' : A),
                            intermr (si :: xs) s s' ->
                            si = s.
Proof.
  intros xs si s s' INTERMR.
  inversion INTERMR; subst; auto.
Qed.

Lemma intermr_in_first_last : forall xs (s s' : A),
                               intermr xs s s' ->
                               In s xs /\ In s' xs.
Proof.
  intros xs s s' INTERMR.
  induction INTERMR; subst; simpl; try (destruct IHINTERM); auto.
  split; auto. destruct IHINTERMR. auto.
Qed.
     
Lemma intermr_trans : forall (s s' s'' : A) xs xs',
  intermr xs s s' ->
  intermr xs' s' s'' ->
  exists xs'', intermr xs'' s s'' /\
               forall x, (In x xs \/ In x xs'-> In x xs'').
Proof.
  intros s s' s'' xs xs' INTERMR INTERMR'.
  induction INTERMR as [s | s y s' xs'' SSTEP INTERMR IHINTERMR].
  + eexists; split. eauto.
    intros x H.
    destruct H as [IN | IN].
    - destruct IN as [H | H]; subst.
      apply intermr_in_first_last in INTERMR'. destruct INTERMR'; auto.
      inversion H.
    - assumption.
  + destruct (IHINTERMR INTERMR') as [zs [INTERMR'' INH]].
    exists (s :: zs).
    split.
    - eapply intermr_multi; eauto.
    - intros x H.
      destruct H as [IN | IN].
      * destruct IN as [IN | IN]; subst.
        simpl; auto.
        simpl. right. apply INH. auto.
      * simpl. right. apply INH. auto.
Qed.


Lemma intermr_trans2 : forall (s s' s'' : A) xs xs',
  intermr xs s s' ->
  intermr xs' s' s'' ->
  exists xs'', intermr xs'' s s'' /\
               forall x y, (In2 x y xs \/ In2 x y xs' -> In2 x y xs'') /\
               forall x, (In x xs \/ In x xs' -> In x xs'').
Proof.
  intros s s' s'' xs xs' INTERMR INTERMR'.
  induction INTERMR as [s | s y s' xs'' SSTEP INTERMR IHINTERMR].
  + eexists; split. eauto. intros. split. intro H. destruct H; [destruct H | assumption].
    intros x0 H. destruct H as [H | H]; 
                 [destruct H as [|CONTRA]; 
                   [subst; inversion INTERMR'; subst; simpl; auto | destruct CONTRA] | assumption].
  + destruct xs''; inversion INTERMR; subst.
    { destruct (IHINTERMR INTERMR') as [zs [INTERMR'' INH]].
      exists (s :: zs). split.
      - eapply intermr_multi; eauto.
      - intros x' y'. 
        split.
        { (* In2 *)
          intros H.
          destruct H as [H | H].
          destruct zs. inversion INTERMR''. inversion INTERMR''; subst.
          assumption.
          destruct H as [[EQ1 EQ2] | CONTRA]; subst. simpl; auto.
          destruct CONTRA.
          assert (H' : In2 x' y' [s'] \/ In2 x' y' xs') by auto.
          apply INH in H'.
          assert (H0: (s :: zs) = [s] ++ zs) by reflexivity. rewrite H0.
          apply in2_strengthen; assumption.
         }
        { (*In*)
          intros x H.
          destruct (INH x' y') as [? IN]. 
          destruct H as [H | H].
          - destruct H as [H | H]; subst.
            * simpl; auto.
            * simpl; right; apply IN; auto.
          - simpl; right; apply IN; auto.
        }
    }
    { destruct (IHINTERMR INTERMR') as [zs [INTERMR'' IH]].
      exists (s :: zs); split.
      eapply intermr_multi; eauto.
      intros x' y'. split.
      { (*In2*)
        intros H.
        assert (EQ : s :: zs = [s] ++ zs) by reflexivity.
        destruct H as [H | H].
      - destruct H as [[EQ1 EQ2] | H]; subst.
        * inversion INTERMR''; subst; simpl; auto.
        * rewrite EQ;
          apply in2_strengthen; apply IH; auto.
      - rewrite EQ;
        apply in2_strengthen; apply IH; auto.
      }
      { (*In1*)
        intros x H.
        destruct (IH x' y') as [? IN].
        destruct H as [H | H].
        - destruct H as [| H]; subst.
          * simpl; auto.
          * destruct H as [|H]; subst;
            simpl; right; apply IN; left; simpl; auto.
        - simpl; right; apply IN; auto.
      }
    }
Qed.

Lemma intermr_weak_trans : forall (s s' s'' : A) xs xs',
  intermr xs s s' ->
  intermr xs' s' s'' ->
  exists xs'', intermr xs'' s s''.
Proof.
  intros;
  destruct (intermr_trans H H0); destruct H1;
  eexists; eauto.
Qed.

Lemma intermr_implies_interm_weak : forall (s s' : A) xs,
  intermr xs s s' ->
  (exists xs', interm xs' s s') \/ s = s'.
Proof.
  intros s s' xs INTERMR.
  induction INTERMR.
  * right. reflexivity.
  * destruct IHINTERMR as [[zs INTERM] | EQ]; subst.
    + left. assert (interm (x::zs) x z) by eauto.
      eexists; eassumption.
    + left. exists [x;z]. constructor. assumption.
Qed.

Lemma intermr_implies_interm : forall (s s' : A) xs,
  intermr xs s s' ->
  interm xs s s' \/ (s = s' /\ xs = [s]).
Proof.
  intros s s' xs INTERM.
  inversion INTERM; subst.
  right. auto.
  destruct xs0. inversion H0.
  left. generalize dependent s. induction H0.
  eauto.
  intros.
  assert (intermr (x :: xs) x z).
  { eapply intermr_multi; eauto. }
  apply IHintermr in H; try assumption.
  eapply interm_multi; eauto.
Qed.

End exec.

Section vectors.

Definition caseS A n (T : Vector.t A (S n) -> Type)
                     (H : forall a v, T (Vector.cons A a n v))
                     (v : Vector.t A (S n)) : T v :=
  match v in Vector.t _ n'
          return match n' return Vector.t A n' -> Type with
                 | 0 => fun _ => unit
                 | S n => fun v => forall (T : Vector.t A (S n) -> Type)
                                          (H : forall a v, T (Vector.cons _ a _ v)),
                                     T v
                 end v
  with
  | Vector.nil => tt
  | Vector.cons a n v => fun T H => H a v
  end T H.

Import DoNotation.

Fixpoint sequence A n (v : Vector.t (option A) n) : option (Vector.t A n) :=
  match v with
  | Vector.nil => Some (Vector.nil _)
  | Vector.cons a n' v' =>
    do! a  <- a;
    do! v' <- sequence v';
    Some (Vector.cons _ a _ v')
  end.

End vectors.

(* Borrowed from ssr *)
Module Option.

Definition apply aT rT (f : aT -> rT) x u :=
  match u with Some y => f y | _ => x end.

Definition default T := apply (fun x : T => x).

Definition bind aT rT (f : aT -> option rT) := apply f None.

Definition map aT rT (f : aT -> rT) := bind (fun x => Some (f x)).

End Option.

Notation oapp := Option.apply.
Notation odflt := Option.default.
Notation obind := Option.bind.
Notation omap := Option.map.
Notation some := (@Some _) (only parsing).

Section Injections.

(* rT must come first so we can use @ to mitigate the Coq 1st order   *)
(* unification bug (e..g., Coq can't infer rT from a "cancel" lemma). *)
Variables (rT aT : Type) (f : aT -> rT).

Definition injective := forall x1 x2, f x1 = f x2 -> x1 = x2.

Definition pcancel g := forall x, g (f x) = Some x.

Definition ocancel (g : aT -> option rT) h := forall x, oapp h x (g x) = x.

Definition cancel g := forall x, g (f x) = x.

Lemma can_pcan g : cancel g -> pcancel (fun y => Some (g y)).
Proof. now intros fK x; rewrite fK. Qed.

Lemma pcan_inj g : pcancel g -> injective.
Proof.
intros fK x y eq_f.
apply (f_equal g) in eq_f.
rewrite !fK in eq_f.
now injection eq_f as ->.
Qed.

Lemma can_inj g : cancel g -> injective.
Proof.
intros can_g; apply can_pcan in can_g.
now revert can_g; apply pcan_inj.
Qed.

End Injections.

Lemma Some_inj {T} : injective (@Some T).
Proof. now intros x y H; injection H. Qed.

(* Notations for argument transpose *)
Notation "f ^~ y" := (fun x => f x y)
  (at level 10, y at level 8, no associativity, format "f ^~  y") : fun_scope.
Notation "@^~ x" := (fun f => f x)
  (at level 10, x at level 8, no associativity, format "@^~  x") : fun_scope.

Section OperationProperties.

Open Scope fun_scope.

Variables S T R : Type.

Section SopTisR.
Implicit Type op :  S -> T -> R.
Definition left_inverse e inv op := forall x, op (inv x) x = e.
Definition right_inverse e inv op := forall x, op x (inv x) = e.
Definition left_injective op := forall x, injective (op^~ x).
Definition right_injective op := forall y, injective (op y).
End SopTisR.

Section SopTisS.
Implicit Type op :  S -> T -> S.
Definition right_id e op := forall x, op x e = x.
Definition left_zero z op := forall x, op z x = z.
Definition right_commutative op := forall x y z, op (op x y) z = op (op x z) y.
Definition left_distributive op add :=
  forall x y z, op (add x y) z = add (op x z) (op y z).
Definition right_loop inv op := forall y, cancel (op^~ y) (op^~ (inv y)).
Definition rev_right_loop inv op := forall y, cancel (op^~ (inv y)) (op^~ y).
End SopTisS.

Section SopTisT.
Implicit Type op :  S -> T -> T.
Definition left_id e op := forall x, op e x = x.
Definition right_zero z op := forall x, op x z = z.
Definition left_commutative op := forall x y z, op x (op y z) = op y (op x z).
Definition right_distributive op add :=
  forall x y z, op x (add y z) = add (op x y) (op x z).
Definition left_loop inv op := forall x, cancel (op x) (op (inv x)).
Definition rev_left_loop inv op := forall x, cancel (op (inv x)) (op x).
End SopTisT.

Section SopSisT.
Implicit Type op :  S -> S -> T.
Definition self_inverse e op := forall x, op x x = e.
Definition commutative op := forall x y, op x y = op y x.
End SopSisT.

Section SopSisS.
Implicit Type op :  S -> S -> S.
Definition idempotent op := forall x, op x x = x.
Definition associative op := forall x y z, op x (op y z) = op (op x y) z.
Definition interchange op1 op2 :=
  forall x y z t, op1 (op2 x y) (op2 z t) = op2 (op1 x z) (op1 y t).
End SopSisS.

End OperationProperties.