Require Import Coq.Classes.SetoidDec.
Require Import ZArith. (* omega *)
Require Import Bool.
Require Import ssreflect ssrbool ssrfun eqtype seq.

Close Scope Z_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Useful tactics *)
Ltac gdep x := generalize dependent x.

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
  forall (n1 n2: nat) (P: seq (seq nat) -> nat -> Prop),
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
  hnf;
  try match goal with
    | [|- Is_true _]  => apply Is_true_eq_left
    | [|- true  =  _] => symmetry
    | [|- false <> _] => symmetry; apply not_false_iff_true
    | [|- _ <> false] => apply not_false_iff_true
  end;
  match goal with
    | [|- ?b1 && ?b = true] => apply andb_true_iff; split;
                               try andb_true_split
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
Lemma rev_nil_nil (A: Type) : forall (l: seq A),
  rev l = nil ->
  l = nil.
Proof.
  move=> l.
  rewrite -{1}[[::]]/(rev [::]).
  exact: (inv_inj revK).
Qed.

Notation "f ∘ g" := (f \o g) (at level 30).

Fixpoint update_list A (n : nat) (y : A) (xs : seq A) : option (seq A) :=
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

Definition update_list_Z A i y (xs: seq A) : option (seq A) :=
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

Fixpoint just_somes {X Y} (l : seq (X * option Y)) :=
  match l with
  | nil => nil
  | (_, None) :: l' => just_somes l'
  | (x, Some y) :: l' => (x,y) :: just_somes l'
  end.

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
  (at level 200, cond at level 100, rest at level 200).

End DoNotation.

Fixpoint assoc_list_lookup {T1 T2 : Type} (xys : seq (T1 * T2)%type)
    (select : T1 -> bool) : option T2 :=
  match xys with
  | [::] => None
  | (x,y) :: xys' => if select x then Some y
                     else assoc_list_lookup xys' select
  end.

Require Import Recdef.
Require Import Omega.

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
  In2 (xs ++ [:: i;j]) ->
  In2 (xs ++ [:: i]) \/ i = x /\ j = y.
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

Variable A : eqType.
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

Inductive zero_one : A -> A -> Prop :=
  | zero_one_refl : forall x, zero_one x x
  | zero_one_single : forall (x y : A), R x y -> zero_one x y.
Hint Constructors zero_one.

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

Lemma interm_last_step : forall xs (si s s' : A),
                           interm (xs ++ [:: si]) s s' ->
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

Lemma interm_step_upto : forall xs (s s' si : A),
                          si \in xs ->
                          interm xs s s' ->
                          (exists zs, interm zs s si) \/ si = s.
Proof.
Admitted.
(*
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
    left. exists [:: x;y]. constructor. auto.
Qed.
*)

(*
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
      * subst. left. exists [:: s;s'']. split.
        constructor. assumption.
        intros sj INJ. destruct INJ as [|INJ]; subst; simpl; auto.
        destruct INJ as [|INJ]; subst; simpl; auto.
        destruct INJ.
Qed.
*)

(*
Lemma interm_in_first_last : forall xs (s s' : A),
                               interm xs s s' ->
                               In s xs /\ In s' xs.
Proof.
  intros xs s s' INTERM.
  induction INTERM; subst; simpl; try (destruct IHINTERM); auto.
Qed.
*)

Lemma interm_backwards : forall xs s s' s'',
  R s' s'' ->
  interm xs s s' ->
  interm (xs ++ [:: s'']) s s''.
Proof.
  intros xs s s' s'' STEP INTERM.
  induction INTERM.
  - simpl. eapply interm_multi. eauto.
    eapply interm_single; eauto.
  - eapply interm_multi; eauto.
Qed.

Lemma interm_destruct_last : forall xs s s',
  interm xs s s' ->
  exists ys, interm (ys ++ [:: s']) s s'.
Proof.
  intros xs s s' INTERM.
  induction INTERM.
  - exists [:: x]; constructor(assumption).
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

(* Lemmas about intermr *)
Lemma intermr_first_step : forall xs (si s s' : A),
                            intermr (si :: xs) s s' ->
                            si = s.
Proof.
  intros xs si s s' INTERMR.
  inversion INTERMR; subst; auto.
Qed.

(*
Lemma intermr_in_first_last : forall xs (s s' : A),
                               intermr xs s s' ->
                               In s xs /\ In s' xs.
Proof.
  intros xs s s' INTERMR.
  induction INTERMR; subst; simpl; try (destruct IHINTERM); auto.
  split; auto. destruct IHINTERMR. auto.
Qed.
*)

(*
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
*)

(*
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
          assert (H' : In2 x' y' [:: s'] \/ In2 x' y' xs') by auto.
          apply INH in H'.
          assert (H0: (s :: zs) = [:: s] ++ zs) by reflexivity. rewrite H0.
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
        assert (EQ : s :: zs = [:: s] ++ zs) by reflexivity.
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
*)

(*
Lemma intermr_weak_trans : forall (s s' s'' : A) xs xs',
  intermr xs s s' ->
  intermr xs' s' s'' ->
  exists xs'', intermr xs'' s s''.
Proof.
  intros;
  destruct (intermr_trans H H0); destruct H1;
  eexists; eauto.
Qed.
*)

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
    + left. exists [:: x;z]. constructor. assumption.
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

Section preservation.

Variables X Y : eqType.
Variables (stepX : X -> X -> Prop) (stepY : Y -> Y -> Prop).
Variables (P : X -> Prop) (Q : Y -> Prop).
Variable (vis : Y -> bool). (* Whether a given state is visible or not *)
Variable (ref : X -> Y -> Prop).

Hypothesis ref_single :
  forall x y y',
    vis y = true -> vis y' = true ->
    stepY y y' ->
    ref x y ->
    exists x', stepX x x' /\ ref x' y'.

Hypothesis ref_mult :
  forall x y yk yk' y',
    vis y = true -> vis y' = true ->
    stepY y yk ->
    restricted_exec stepY (fun y => vis y = false) yk yk' ->
    stepY yk' y' ->
    ref x y ->
    ref x y' \/
    exists x', stepX x x' /\ ref x' y'.

Hypothesis preservation :
  forall x x', P x -> stepX x x' -> P x'.

Hypothesis compatible :
  forall x y, ref x y -> (P x <-> Q y).

Hypothesis ref_vis : forall x y, ref x y -> vis y = true.

Definition ref_weak x y :=
  ref x y \/
  exists y0 yk,
    ref x y0 /\
    stepY y0 yk /\
    restricted_exec stepY (fun y => vis y = false) yk y.

End preservation.

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

End vectors.

Ltac single_match_inv :=
  match goal with
  | H : ssrfun.obind (fun x : _ => _) _ = Some _ |- _ =>
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

Instance eqType_EqDec (A : eqType) : EqDec (eq_setoid A).
Proof.
move=> x y.
have [->|neq_xy] := altP (x =P y); first by left.
by right=> eq_xy; move: neq_xy; rewrite eq_xy eqxx.
Qed.

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
