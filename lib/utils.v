From mathcomp Require Import ssreflect ssrbool ssrfun eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Ltac split3 := split; [| split].
Ltac split4 := split; [| split3].

Ltac inv H := inversion H; subst; clear H.

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

Require Coq.Strings.String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

(* Wrappers around the backtracking version of (e)constructor, which
changed between 8.4 and 8.5 *)

Tactic Notation "s_constructor" tactic(t) :=
  [> once (constructor; t) ..].

Tactic Notation "s_econstructor" tactic(t) :=
  [> once (econstructor; t) ..].

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

End EqualityTactics.
Export EqualityTactics.

Ltac andb_true_split :=
  hnf;
  try match goal with
    (*| [|- Is_true _]  => apply Is_true_eq_left*)
    | [|- true  =  _] => symmetry
    (*| [|- false <> _] => symmetry; apply not_false_iff_true
    | [|- _ <> false] => apply not_false_iff_true*)
  end;
  match goal with
    | [|- ?b1 && ?b = true] => apply/andP; split;
                               try andb_true_split
  end.

Notation "f ∘ g" := (f \o g) (at level 30).

Lemma obind_inv A B (f : A -> option B) (a : option A) (b : B) :
  obind f a = Some b -> exists a', a = Some a' /\ f a' = Some b.
Proof.
  destruct a as [a'|]; simpl; solve [eauto | discriminate].
Qed.

Theorem obind_assoc : forall A B C
                             (mx : option A)
                             (my : A -> option B)
                             (mz : B -> option C),
  obind (obind mz \o my) mx = obind mz (obind my mx).
Proof.
  intros A B C mx my mz.
  destruct mx as [x|]; [destruct (my x) as [y|]|]; reflexivity.
Qed.

(* This notation breaks parsing of the "do" tactical, so it should be
packaged in a module. *)
Module DoNotation.

Import ssrfun.

Notation "'do!' X <- A ; B" :=
  (obind (fun X => B) A)
  (at level 200, X ident, A at level 100, B at level 200).

Notation "'do!' X : T <- A ; B" :=
  (obind (fun X : T => B) A)
  (at level 200, X ident, A at level 100, B at level 200).

Notation "'do!' 'guard' cond ; rest" :=
  (if cond then rest else None)
  (at level 200, cond at level 100, rest at level 200).

Notation "'do!' 'guard?' ocond ; rest" :=
  match ocond with
    | Some true         => rest
    | Some false | None => None
  end
  (at level 200, ocond at level 100, rest at level 200).

End DoNotation.

Section In2.

Variable A : Type.

Variable x y : A.

Fixpoint In2 (l : seq A) {struct l} : Prop :=
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

Lemma in2_trivial : forall xs ys,
  In2 (xs ++ x :: y :: ys).
Proof.
  intros xs ys. induction xs; intros. simpl; auto.
  simpl.
  destruct (xs ++ x :: y :: ys). inversion IHxs.
  right; assumption.
Qed.

Lemma In2_inv xs xmid xs' :
  In2 (xs ++ xmid :: xs') ->
  In2 (xs ++ [:: xmid]) \/
  In2 (xmid :: xs').
Proof.
  intros IN2.
  induction xs.
  - rewrite cat0s in IN2.
    right; trivial.
  - destruct xs.
    + destruct IN2 as [[E1 E2] | IN2].
      * subst.
        left; simpl; auto.
      * right; assumption.
    + destruct IN2 as [[E1 E2] | IN2].
      * subst. left; simpl; auto.
      * apply IHxs in IN2.
        destruct IN2 as [IN2 | IN2].
        { left. simpl; right; auto. }
        { right. trivial. }
Qed.

End In2.

Lemma In2_implies_In (A : eqType) (x y : A) xs :
  In2 x y xs ->
  x \in xs.
Proof.
  intros IN2.
  induction xs.
  - now destruct IN2.
  - destruct xs.
    + now destruct IN2.
    + destruct IN2 as [[? ?] | IN2]; subst.
      * by rewrite inE eqxx.
      * rewrite inE; apply/orP; right. apply IHxs; assumption.
Qed.

Section exec.

(* Several notions of execution. Essentially variations on the
   reflexive-transitive closure of a relation. *)

Variable A : eqType.
Variable R : A -> A -> Prop.

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

(* Capture steps from s to s' (with s') *)
Inductive interm : seq A -> A -> A -> Prop :=
  | interm_single : forall (x y : A), R x y -> interm [:: x;y] x y
  | interm_multi : forall (x y z : A) (xs : seq A),
                    R x y ->
                    interm xs y z ->
                    interm (x :: xs) x z.
Hint Constructors interm.

Inductive interm_reverse : seq A -> A -> A -> Prop :=
  | intermrev_single : forall (x y : A), R x y -> interm_reverse [:: x;y] x y
  | intermrev_multi : forall (x y z : A) (xs : seq A),
                      R y z ->
                      interm_reverse xs x y ->
                      interm_reverse (xs ++ [:: z]) x z.
Hint Constructors interm_reverse.

Inductive intermr : seq A -> A -> A -> Prop :=
  | intermr_refl : forall x, intermr [:: x] x x
  | intermr_multi : forall (x y z : A) (xs : seq A),
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

Lemma interm_in2_step : forall xs s s' si sj,
  interm xs s s' ->
  In2 si sj xs ->
  R si sj.
Proof.
  intros xs s s' si sj INTERM HIn2.
  induction INTERM.
  - destruct HIn2 as [[EQ1 EQ2] | CONTRA]; subst. assumption.
    destruct CONTRA.
  - destruct xs. inversion INTERM.
    inversion INTERM; subst.
    + destruct HIn2 as [[EQ1 EQ2] | CONTRA]; subst. assumption.
      auto.
    + destruct HIn2 as [[EQ1 EQ2] | CONTRA]; subst. assumption.
      auto.
Qed.

(* Lemmas about intermr *)
Lemma intermr_first_step : forall xs (si s s' : A),
                            intermr (si :: xs) s s' ->
                            si = s.
Proof.
  intros xs si s s' INTERMR.
  inversion INTERMR; subst; auto.
Qed.

Lemma intermr_implies_interm : forall (s s' : A) xs,
  intermr xs s s' ->
  interm xs s s' \/ (s = s' /\ xs = [:: s]).
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

Ltac single_match_inv :=
  match goal with
  | H : obind (fun x : _ => _) _ = Some _ |- _ =>
    apply obind_inv in H;
    let x := fresh x in
    let E := fresh "E" in
    destruct H as (x & H & E);
    simpl in H; simpl in E
  | H : (if ?b then _ else _) = Some _ |- _ =>
    let E := fresh "E" in
    destruct b eqn:E;
    try discriminate
  | H : match ?E with _ => _ end = _ |- _ =>
    destruct E eqn:?; try discriminate
  | H : Some _ = Some _ |- _ => inv H
  | H : ?O = Some _ |- context[ssrfun.obind _ ?O] => rewrite H; simpl
  | H : True |- _ => clear H
  end.

Ltac match_inv := repeat single_match_inv.

Fixpoint stepn {A} (step : A -> option A) (max_steps : nat) (st : A) : option A :=
  match max_steps with
  | O => Some st
  | S max_steps' =>
    match step st with
      Some st' => stepn step max_steps' st'
    | None => None
    end
  end.

Fixpoint runn {A} (step : A -> option A) (max_steps : nat) (st : A) : seq A :=
  st ::
  match max_steps with
  | O => [::]
  | S max_steps' =>
    match step st with
    | None => [::]
    | Some st' => runn step max_steps' st'
    end
  end.

Definition run {A} (step: A -> option A) (st : A) := runn step 10000 st.

Lemma pair2_inj (T : eqType) (S : T -> Type) (x : T) : injective (existT S x).
Proof.
  move=> y1 y2 H.
  have [p {H} H] := match H in _ = P
                    return let: existT x' y2' := P in
                           { p : x' = x & y1 = eq_rect x' S y2' x p }
                    with
                    | erefl => existT _ erefl erefl
                    end.
  by rewrite H eq_axiomK.
Qed.
