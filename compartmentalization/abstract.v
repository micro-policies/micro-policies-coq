Require Import List Arith Sorted Bool.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype finset.

Require Import lib.Integers lib.utils lib.partial_maps lib.ordered common.common.
Require Import lib.list_utils.
Require Import compartmentalization.isolate_sets compartmentalization.common.

Set Bullet Behavior "Strict Subproofs".
Import DoNotation.

Set Implicit Arguments.

Import ListNotations.

Module Abs.

Open Scope bool_scope.

Section WithClasses.

Import PartMaps.

Context (t            : machine_types)
        {ops          : machine_ops t}
        {spec         : machine_ops_spec ops}
        {scr          : @syscall_regs t}
        {cmp_syscalls : compartmentalization_syscall_addrs t}.

Open Scope word_scope.
Local Notation word  := (word t).
Local Notation value := word.
Local Notation memory := (word_map t word).
Local Notation registers := (reg_map t word).

Implicit Type pc : value.
Implicit Type M : memory.
Implicit Type R : registers.
Implicit Type r rsrc rdest rpsrc rpdest rtgt : reg t.

(* I want to use S as a variable. *)
Let S := Datatypes.S.
Local Notation Suc := Datatypes.S.

(* BCP: Can we change `store_targets' to `writable_memory', and disallow writes
   to `address_space'?  [TODO] *)
Record compartment := Compartment { address_space : {set value}
                                  ; jump_targets  : {set value}
                                  ; store_targets : {set value} }.
Notation "<< A , J , S >>" := (Compartment A J S) (format "<< A , J , S >>").
Implicit Type c     : compartment.
Implicit Type A J S : {set value}.
Implicit Type C     : list compartment.

Definition compartment_eq c1 c2 :=
  [&& address_space c1 == address_space c2,
      jump_targets c1 == jump_targets c2 &
      store_targets c1 == store_targets c2].

Lemma compartment_eqP : Equality.axiom compartment_eq.
Proof.
move=> [? ? ?] [? ? ?]; apply: (iffP and3P) => [[]|[<- <- <-]]; try by [].
by simpl; repeat move/eqP->.
Qed.

Definition compartment_eqMixin := EqMixin compartment_eqP.
Canonical compartment_eqType :=
  Eval hnf in EqType compartment compartment_eqMixin.

Definition disjoint_comp : rel compartment :=
  [rel c1 c2 | ((address_space c1 != set0) ||
                (address_space c2 != set0)) &&
               [disjoint address_space c1 & address_space c2]].

Definition non_overlapping : list compartment -> bool :=
  all_tail_pairs_b disjoint_comp.

(* BCP: Do we need this?  Can we get away with just having all user memory
   inside a compartment at all times?  [TODO] *)
Definition contained_compartments (C : list compartment) : bool :=
  \bigcup_(i <- C) jump_targets i :|: \bigcup_(i <- C) store_targets i
  \subset \bigcup_(i <- C) address_space i.

Definition good_compartments (C : list compartment) : bool :=
  non_overlapping          C &&
  contained_compartments   C.

Reserved Notation "C ⊢ p ∈ c" (at level 70).

Definition in_compartment (p : value) (cs : seq compartment) (c : compartment) :=
  [&& p \in address_space c & c \in cs].

Notation "C ⊢ p ∈ c" := (in_compartment p C c).
Notation "C ⊢ p1 , p2 , .. , pk ∈ c" :=
  (and .. (and (C ⊢ p1 ∈ c) (C ⊢ p2 ∈ c)) .. (C ⊢ pk ∈ c))
  (at level 70).

Fixpoint in_compartment_opt (C : list compartment)
                            (p : value) : option compartment :=
  match C with
    | []     => None
    | c :: C => if p \in address_space c
                then Some c
                else in_compartment_opt C p
  end.

Record state := State { pc           : value
                      ; regs         : registers
                      ; mem          : memory
                      ; compartments : list compartment
                      ; step_kind    : where_from
                      ; previous     : compartment }.
                        (* Initially, step_kind should be INTERNAL and previous
                           should just be the initial main compartment *)

Definition permitted_now_in (C : list compartment)
                            (sk : where_from)
                            (prev : compartment)
                            (pc : word) : option compartment :=
  do! c <- in_compartment_opt C pc;
  do! guard (c == prev) || ((sk == JUMPED) && (pc \in jump_targets prev));
  Some c.
Arguments permitted_now_in C !sk prev pc /.

Record syscall := Syscall { address   : word
                          ; semantics : state -> option state }.

Definition isolate_fn (MM : state) : option state :=
  let '(State pc R M C sk c) := MM in
  do! c_sys <- permitted_now_in C sk c pc;
  do! pA <- get R syscall_arg1;
  do! pJ <- get R syscall_arg2;
  do! pS <- get R syscall_arg3;
  let '<<A,J,S>> := c in
  do! A' : {set value} <- isolate_create_set id M pA;
  do! guard A' \subset A;
  do! guard A' != set0;
  do! J' : {set value} <- isolate_create_set id M pJ;
  do! guard J' \subset (A :|: J);
  do! S' : {set value} <- isolate_create_set id M pS;
  do! guard S' \subset (A :|: S);
  let c_upd := <<A :\: A', J, S>> in
  let c'    := <<A',J',S'>> in
  let C'    := c_upd :: c' :: delete c C in
  do! pc'    <- get R ra;
  do! c_next <- in_compartment_opt C' pc';
  do! guard c_upd == c_next;
  do! guard pc' \in jump_targets c_sys;
  Some (State pc' R M C' JUMPED c_sys).

Definition isolate :=
  {| address   := isolate_addr
   ; semantics := isolate_fn |}.

(* There are two possible design choices for this function: either it takes a
   single address to add to the jump table, or it takes a pointer to memory with
   a jump table layout as for isolate.  The former seems nicer, but the latter's
   pretty easy too. *)

Definition add_to_compartment_component
             (rd : compartment -> {set value})
             (wr : {set value} -> compartment -> compartment)
             (MM : state) : option state :=
  let '(State pc R M C sk c) := MM in
  do! c_sys <- permitted_now_in C sk c pc;
  (* Is this necessary?  We don't need it for `isolate' because we can prove it
     there (due to non-emptiness constraints), but we can't prove it here.  It
     should always be true, since syscalls live in one-address compartments, so
     if they're entered via a JAL from elsewhere, we're fine. *)
  do! guard c != c_sys;
  do! p <- get R syscall_arg1;
  do! guard p \in (address_space c :|: rd c);
  let c' := wr (p |: rd c) c in
  let C' := c' :: delete c C in
  do! pc'    <- get R ra;
  do! c_next <- in_compartment_opt C' pc';
  do! guard c' == c_next;
  do! guard pc' \in jump_targets c_sys;
  Some (State pc' R M C' JUMPED c_sys).

Definition add_to_jump_targets :=
  {| address   := add_to_jump_targets_addr
   ; semantics := add_to_compartment_component
                    jump_targets
                    (fun J' c => let '<<A,_,S>> := c in <<A,J',S>>) |}.

Definition add_to_store_targets :=
  {| address   := add_to_store_targets_addr
   ; semantics := add_to_compartment_component
                    store_targets
                    (fun S' c => let '<<A,J,_>> := c in <<A,J,S'>>) |}.

Let table := [isolate; add_to_jump_targets; add_to_store_targets].

Definition get_syscall (addr : value) : option syscall :=
  List.find (fun sc => address sc == addr) table.

Definition user_address_space (M : memory) (c : compartment) : bool :=
  [forall x in address_space c, get M x].
Arguments user_address_space M !c /.

Definition syscall_address_space (M : memory) (c : compartment) : bool :=
  [exists sc, [&& ~~ get M sc, sc \in List.map address table &
                  address_space c == set1 sc] ].

Arguments syscall_address_space : simpl never.

Definition syscalls_separated (M : memory) : list compartment -> bool :=
  all (predU (user_address_space M) (syscall_address_space M)).
Arguments syscalls_separated M C /.

Definition syscalls_present (C : list compartment) : bool :=
  forallb (is_some ∘ (in_compartment_opt C) ∘ address) table.

Definition good_state (MM : state) : bool :=
  [&& previous MM \in compartments MM,
      good_compartments (compartments MM),
      syscalls_separated (mem MM) (compartments MM) &
      syscalls_present (compartments MM) ].

Definition good_syscall (sc : syscall) (MM : state) : bool :=
  if good_state MM
  then match in_compartment_opt (compartments MM) (pc MM) with
         | Some c => if syscall_address_space (mem MM) c
                     then match semantics sc MM with
                            | Some MM' => good_state MM'
                            | None     => true
                          end
                     else true
         | None => true
       end
  else true.

Definition decode M pc :=
  do! pc_val <- get M pc;
  decode_instr pc_val.

Inductive step (MM MM' : state) : Prop :=
| step_nop :     forall pc R M C sk prev c
                        (ST : MM = State pc R M C sk prev)
                   (INST  : decode M pc ?= Nop _)
                   (STEP  : permitted_now_in C sk prev pc ?= c)
                   (NEXT  : MM' = State (pc + 1) R M C INTERNAL c),
                        step MM MM'

| step_const :   forall pc R M C sk prev c x rdest R'
                        (ST : MM = State pc R M C sk prev)
                   (INST  : decode M pc ?= Const x rdest)
                   (STEP  : permitted_now_in C sk prev pc ?= c)
                   (UPD   : upd R rdest (Word.casts x) ?= R')
                   (NEXT  : MM' = State (pc + 1) R' M C INTERNAL c),
                        step MM MM'

| step_mov   :   forall pc R M C sk prev c rsrc rdest x R'
                        (ST : MM = State pc R M C sk prev)
                   (INST  : decode M pc ?= Mov rsrc rdest)
                   (STEP  : permitted_now_in C sk prev pc ?= c)
                   (GET   : get R rsrc ?= x)
                   (UPD   : upd R rdest x ?= R')
                   (NEXT  : MM' = State (pc + 1) R' M C INTERNAL c),
                        step MM MM'

| step_binop :   forall pc R M C sk prev c op rsrc1 rsrc2 rdest x1 x2 R'
                        (ST : MM = State pc R M C sk prev)
                   (INST  : decode M pc ?= Binop op rsrc1 rsrc2 rdest)
                   (STEP  : permitted_now_in C sk prev pc ?= c)
                   (GETR1 : get R rsrc1 ?= x1)
                   (GETR2 : get R rsrc2 ?= x2)
                   (UPDR  : upd R rdest (binop_denote op x1 x2) ?= R')
                   (NEXT  : MM' = State (pc + 1) R' M C INTERNAL c),
                        step MM MM'

| step_load  :   forall pc R M C sk prev c rpsrc rdest p x R'
                        (ST : MM = State pc R M C sk prev)
                   (INST  : decode M pc ?= Load rpsrc rdest)
                   (STEP  : permitted_now_in C sk prev pc ?= c)
                   (GETR  : get R rpsrc ?= p)
                   (GETM  : get M p     ?= x)
                   (UPDR  : upd R rdest x ?= R')
                   (NEXT  : MM' = State (pc + 1) R' M C INTERNAL c),
                        step MM MM'

| step_store :   forall pc R M C sk prev c rsrc rpdest x p M'
                        (ST : MM = State pc R M C sk prev)
                   (INST  : decode M pc ?= Store rpdest rsrc)
                   (STEP  : permitted_now_in C sk prev pc ?= c)
                   (GETRS : get R rpdest ?= p)
                   (GETRD : get R rsrc   ?= x)
                   (VALID : p \in address_space c :|: store_targets c)
                   (UPDR  : upd M p x ?= M')
                   (NEXT  : MM' = State (pc + 1) R M' C INTERNAL c),
                        step MM MM'

| step_jump  :   forall pc R M C sk prev c rtgt pc'
                        (ST : MM = State pc R M C sk prev)
                   (INST  : decode M pc ?= Jump rtgt)
                   (STEP  : permitted_now_in C sk prev pc ?= c)
                   (GETR  : get R rtgt ?= pc')
                   (NEXT  : MM' = State pc' R M C JUMPED c),
                        step MM MM'

| step_bnz   :   forall pc R M C sk prev c rsrc x b
                        (ST : MM = State pc R M C sk prev)
                   (INST  : decode M pc ?= Bnz rsrc x)
                   (GETR  : get R rsrc ?= b)
                   (STEP  : permitted_now_in C sk prev pc ?= c)
                   (NEXT  : MM' = State (pc + (if b == 0
                                               then 1
                                               else Word.casts x))
                                        R M C INTERNAL c),
                        step MM MM'

(* We make JAL inter-compartmental, like JUMP, but things must be set up so that
 * the return address is callable by the destination compartment.  However, see
 * [Note Fancy JAL] below. *)
| step_jal   :   forall pc R M C c sk prev rtgt pc' R'
                        (ST : MM = State pc R M C sk prev)
                   (INST  : decode M pc ?= Jal rtgt)
                   (STEP  : permitted_now_in C sk prev pc ?= c)
                   (GETR  : get R rtgt ?= pc')
                   (UPDR  : upd R ra (pc + 1) ?= R')
                   (NEXT  : MM' = State pc' R' M C JUMPED c),
                        step MM MM'

| step_syscall : forall pc R M C sk prev sc
                        (ST : MM = State pc R M C sk prev)
                   (INST  : get M pc = None)
                   (GETSC : get_syscall pc ?= sc)
                   (CALL  : semantics sc MM ?= MM'),
                        step MM MM'.

(* [Note Fancy JAL]
 * ~~~~~~~~~~~~~~~~
 * OK, you *could* do something fancy with JAL, but it would depart from the
 * original SFI paper.  In this model, JAL is inter-compartmental (like JUMP),
 * and the value stored into ra by JAL is special (either because ra is special,
 * or because JAL applies a special tag) in that it is ALWAYS a valid argument
 * to JUMP.  The ra-is-special version is nice because then we don't need to
 * introduce tags to the abstract machine, but then we can't stash it.  We can't
 * easily make JAL have the behavior that only the called compartment can return
 * via the produced address, because on the concrete machine, we won't know the
 * target compartment.  This recovers some of the ability to have proper
 * function calls, although not perfectly -- unless we introduce abstract tags,
 * we don't get nesting. *)

(***** PROOFS *****)

(*** Proofs for `user_address_space' and `syscall_address_space' ***)

Theorem user_address_space_same : forall M c c',
  address_space c = address_space c' ->
  user_address_space M c = user_address_space M c'.
Proof. clear S; move=> M [A J S] [A' J' S'] /= -> //. Qed.

Theorem syscall_address_space_same : forall M c c',
  address_space c = address_space c' ->
  syscall_address_space M c = syscall_address_space M c'.
Proof. clear S; move=> M [A J S] [A' J' S'] /= -> //. Qed.

Theorem user__not_syscall : forall M c,
  user_address_space M c -> ~~ syscall_address_space M c.
Proof.
  move=> M c /forallP USER.
  rewrite negb_exists.
  apply/forallP => p.
  apply/negP => /and3P [Hget _ /eqP Heq].
  move: USER => /(_ p).
  by rewrite Heq /= in_set1 eqxx /= (negbTE Hget).
Qed.

Theorem syscall___not_user : forall M c,
  syscall_address_space M c -> ~~ user_address_space M c.
Proof.
  move=> M c.
  apply contraTN.
  by apply user__not_syscall.
Qed.

Corollary not_user_and_syscall : forall M c,
  ~~ (user_address_space M c && syscall_address_space M c).
Proof.
  intros; destruct (user_address_space M c) eqn:UAS; simpl.
  - apply user__not_syscall; assumption.
  - auto.
Qed.

(*** Proofs for `good_compartments' ***)

Local Ltac good_compartments_trivial :=
  unfold good_compartments; intros C GOOD;
  repeat rewrite ->andb_true_iff in GOOD;
  tauto.

(* For `auto' *)
Lemma good_compartments__non_overlapping : forall C,
  good_compartments C = true -> non_overlapping C = true.
Proof. good_compartments_trivial. Qed.
(*Global*) Hint Resolve good_compartments__non_overlapping.

(* For `auto' *)
Lemma good_compartments__contained_compartments : forall C,
  good_compartments C = true -> contained_compartments C = true.
Proof. good_compartments_trivial. Qed.
(*Global*) Hint Resolve good_compartments__contained_compartments.

Theorem good_no_duplicates : forall C,
  good_compartments C -> uniq C.
Proof.
  move=> C /andP [Hover Hcontained].
  admit.
(*
  intros C GOOD;
    unfold good_compartments, non_overlapping in GOOD;
    repeat rewrite ->andb_true_iff in GOOD;
    rewrite <-all_pairs_in2_comm in GOOD;
    destruct GOOD as [[GOOD NOL] CC]; eauto 2.
  eapply all_pairs_distinct_nodup; [|eassumption]; cbv beta; auto.
*)
Qed.
(*Global*) Hint Resolve good_no_duplicates.

(*** Proofs for `non_overlapping' ***)

Theorem non_overlapping_subset : forall C1 C2,
  uniq C1 ->
  subpred (ssrbool.mem C1) (ssrbool.mem C2) ->
  non_overlapping C2 ->
  non_overlapping C1.
Proof.
  admit.
(*
  unfold non_overlapping; intros C1 C2 SUBSET NO_DUP GOOD NOL.
  apply all_pairs__all_tail_pairs.
  rewrite <-all_pairs_in2_comm in NOL; eauto 2.
*)
Qed.
(*Global*) Hint Resolve non_overlapping_subset.

Theorem non_overlapping_tail : forall c C,
  non_overlapping (c :: C) -> non_overlapping C.
Proof.
  admit.
(*
  unfold non_overlapping; intros c C NOL;
  rewrite ->all_tail_pairs_tail, ->andb_true_iff in NOL; tauto.
*)
Qed.
(*Global*) Hint Resolve non_overlapping_tail.

(*
Theorem non_overlapping_spec : forall C,
  non_overlapping C =

   (forall c1 c2,
      In2 c1 c2 C ->
      disjoint (address_space c1) (address_space c2) = true)).
Proof.
  intros C GOOD; unfold non_overlapping.
  rewrite <-all_pairs_in2_comm, all_pairs_spec; [reflexivity|eauto 2].
Qed.
*)

(*
Corollary non_overlapping_spec' : forall C,
  good_compartments C = true ->
  (non_overlapping C = true <->
   (forall c1 c2,
      In2 c1 c2 C ->
      disjoint (address_space c1) (address_space c2) = true)).
Proof. intros C GOOD; apply non_overlapping_spec; auto. Qed.
*)

(*
Corollary good_compartments__in2_disjoint  : forall C c1 c2,
  good_compartments C = true ->
  In2 c1 c2 C ->
  disjoint (address_space c1) (address_space c2) = true.
Proof.
  intros C c1 c2 GOOD;
    assert (non_overlapping C = true) by auto;
    apply non_overlapping_spec' in GOOD;
    apply GOOD; assumption.
Qed.
(*Global*) Hint Resolve good_compartments__in2_disjoint.
*)

Theorem non_overlapping_delete : forall c C,
  non_overlapping C ->
  non_overlapping (delete c C) = true.
Proof.
  admit.
(*
  intros c C GOOD NOL.
  rewrite ->non_overlapping_spec in * by auto.
  intros c1 c2 IN2; apply NOL.
  eapply in2_delete; eassumption.
*)
Qed.
(*Global*) Hint Resolve non_overlapping_delete.

Corollary non_overlapping_delete' : forall c C,
  good_compartments C ->
  non_overlapping (delete c C).
Proof. auto. Qed.
(*Global*) Hint Resolve non_overlapping_delete'.

Lemma non_overlapping_replace : forall c c' C,
  non_overlapping C ->
  non_overlapping (c' :: delete c C) =
  all (disjoint_comp c') (delete c C).
Proof.
  admit.
(*
  intros;
    unfold non_overlapping;
    repeat rewrite all_tail_pairs_tail;
    fold (non_overlapping (delete c C)).
  destruct (forallb _ (delete _ _)); [simpl | reflexivity].
  apply non_overlapping_delete; assumption. *)
Qed.
(*Global*) Hint Resolve non_overlapping_replace.

Lemma non_overlapping_replace' : forall c c' C,
  good_compartments C ->
  non_overlapping (c' :: delete c C) =
  all (disjoint_comp c') (delete c C).
Proof. auto. Qed.
(*Global*) Hint Resolve non_overlapping_replace'.

(*** Proofs for `in_compartment' and `in_compartment_opt' ***)

(* Ltac *)

(*
Ltac destruct_set_elem_xX_as_by x X Hy Hn t :=
  let H := fresh in
  destruct (set_elem x X) eqn:H;
    [ rename H into Hy; rewrite ->set_elem_true  in Hy by t
    | rename H into Hn; rewrite ->set_elem_false in Hn by t ].

(* If not re-implemented, the placeholders don't work *)
Ltac destruct_set_elem_as_by Hy Hn t :=
  let H := fresh in
  destruct (set_elem _ _) eqn:H;
    [ rename H into Hy; rewrite ->set_elem_true  in Hy by t
    | rename H into Hn; rewrite ->set_elem_false in Hn by t ].

Tactic Notation "destruct" "set_elem" constr(x) constr(X)
                "as" ident(Hy) "," ident(Hn)
                "by" tactic(t) :=
  destruct_set_elem_xX_as_by x X Hy Hn t.

Tactic Notation "destruct" "set_elem"
                "as" ident(Hy) "," ident(Hn)
                "by" tactic(t) :=
  (destruct_set_elem_as_by Hy Hn t).

Tactic Notation "destruct" "set_elem" constr(x) constr(X) "by" tactic(t) :=
  let Hy := fresh "Hy" in
  let Hn := fresh "Hn" in
  destruct set_elem x X as Hy , Hn by t.

Tactic Notation "destruct" "set_elem" "by" tactic(t) :=
  let Hy := fresh "Hy" in
  let Hn := fresh "Hn" in
  destruct set_elem as Hy , Hn by t.
*)

Theorem in_compartment_element : forall C p c,
  C ⊢ p ∈ c ->
  c \in C.
Proof. admit. Qed.
(*Global*) Hint Resolve in_compartment_element.

Theorem in_compartment__in_address_space : forall C p c,
  C ⊢ p ∈ c -> p \in address_space c.
Proof. admit. Qed.
(*Global*) Hint Resolve in_compartment__in_address_space.

Theorem in_same_compartment : forall C p p' c,
  C ⊢ p ∈ c ->
  p' \in address_space c ->
  C ⊢ p' ∈ c.
Proof. admit. Qed.
(*Global*) Hint Resolve in_same_compartment.

Theorem unique_here_not_there : forall C p c,
  c \notin C     ->
  c :: C ⊢ p ∈ c ->
  ~~ (C ⊢ p ∈ c).
Proof.
  admit.
(*
  intros until 0; intros OUT HERE THERE.
  apply in_compartment_element in HERE; apply in_compartment_element in THERE.
  assert (IN2 : In2 c c (c :: C)) by auto.
  inversion IN2; subst; auto.
*)
Qed.
(*Global*) Hint Resolve unique_here_not_there.

Theorem unique_must_be_here : forall C p c c',
  c' \notin C     ->
  c :: C ⊢ p ∈ c' ->
  c = c'.
Proof.
  admit.
(*
  clear. intros until 0; intros OUT IC.
  inversion IC; subst; auto.
  contradict OUT; eauto 2.*)
Qed.
(*Global*) Hint Resolve unique_must_be_here.

Theorem in_same_compartment__overlapping : forall C p c1 c2,
  C ⊢ p ∈ c1 ->
  C ⊢ p ∈ c2 ->
  ~~ disjoint_comp c1 c2.
Proof.
  admit.
(*
  intros until 0; intros GOOD1 GOOD2 IC1 IC2;
    apply in_compartment__in_address_space in IC1;
    apply in_compartment__in_address_space in IC2.
  unfold disjoint.
  assert (IN : In p (set_intersection (address_space c1) (address_space c2))) by
    (apply set_intersection_spec; auto).
  destruct (set_intersection (address_space c1) (address_space c2)).
  - inversion IN.
  - reflexivity.*)
Qed.
(*Global*) Hint Resolve in_same_compartment__overlapping.

Theorem in_compartment_opt_correct : forall C p c,
  in_compartment_opt C p ?= c -> C ⊢ p ∈ c.
Proof.
  admit.
(*
  clear.
  intros C p c GOOD ICO; rewrite ->forallb_forall in GOOD; gdep c; gdep p;
    induction C as [|ch C]; [inversion 1|];
    intros; simpl in *.
  destruct set_elem as Hy,Hn by auto.
  - inversion ICO; subst; destruct c; auto.
  - auto 10.
*)
Qed.
(*Global*) Hint Resolve in_compartment_opt_correct.

Theorem in_compartment_opt_missing_correct : forall C p,
  in_compartment_opt C p = None -> forall c, ~~ (C ⊢ p ∈ c).
Proof.
  admit.
(*
  clear.
  intros C p GOOD; rewrite ->forallb_forall in GOOD; gdep p;
    induction C as [|ch C]; intros p ICO c IC; [inversion IC|]; simpl in *.
  destruct set_elem by auto.
  - congruence.
  - inversion IC; subst; [simpl in *; solve [intuition] | eapply IHC; eauto].*)
Qed.
(*Global*) Hint Resolve in_compartment_opt_missing_correct.

Theorem in_compartment_opt_present : forall C p c,
  C ⊢ p ∈ c -> exists c', in_compartment_opt C p ?= c'.
Proof.
  admit.
(*
  clear.
  intros until 0; intros GOOD; rewrite ->forallb_forall in GOOD;
    induction 1 as [C A J S IN | C ch c IC].
  - exists <<A,J,S>>; simpl;
      (destruct set_elem by
        (eapply good_compartment_decomposed__is_set_address_space; auto));
      [reflexivity | intuition].
  - simpl; (destruct set_elem by auto); eauto.*)
Qed.
(*Global*) Hint Resolve in_compartment_opt_present.

Corollary in_compartment_opt_is_some : forall C p c,
  C ⊢ p ∈ c -> in_compartment_opt C p.
Proof.
  intros C p c IC; apply in_compartment_opt_present in IC; auto.
  destruct IC as [c' ICO]; rewrite ICO; reflexivity.
Qed.
(*Global*) Hint Resolve in_compartment_opt_is_some.

Theorem in_compartment_opt_sound : forall C p c,
  non_overlapping C ->
  C ⊢ p ∈ c ->
  in_compartment_opt C p ?= c.
Proof.
  admit.
(*
  clear.
  intros C p c GOOD NOL; rewrite ->forallb_forall in GOOD;
    induction 1 as [C A J S IN | C ch c IC];
    simpl.
  - (destruct set_elem by
      (eapply good_compartment_decomposed__is_set_address_space; auto));
    [reflexivity | intuition].
  - (destruct set_elem by auto); [|apply IHIC; eauto 4].
    assert (IN : In c C) by eauto 2; assert (IN2 : In2 ch c (ch :: C)) by auto.
    apply in_compartment__in_address_space in IC.
    apply non_overlapping_spec in IN2; try rewrite ->forallb_forall; auto.
    unfold disjoint in *.
    destruct (set_intersection _ _) eqn:SI; try congruence.
    rewrite ->nil_iff_not_in in SI; specialize SI with p.
    rewrite ->set_intersection_spec in SI by eauto; tauto. *)
Qed.
(*Global*) Hint Resolve in_compartment_opt_sound.

Corollary in_compartment_opt_sound' : forall C p c,
  good_compartments C ->
  C ⊢ p ∈ c ->
  in_compartment_opt C p ?= c.
Proof. auto. Qed.
(*Global*) Hint Resolve in_compartment_opt_sound'.

Corollary in_compartment_opt_sound_is_some : forall C p c,
  non_overlapping C ->
  C ⊢ p ∈ c -> in_compartment_opt C p.
Proof.
  admit. (*
  intros C p c NOL IC;
    apply in_compartment_opt_sound in IC; [rewrite IC | | ]; auto.*)
Qed.
(*Global*) Hint Resolve in_compartment_opt_sound_is_some.

Corollary in_compartment_opt_sound_is_some' : forall C p c,
  good_compartments C ->
  C ⊢ p ∈ c -> in_compartment_opt C p.
Proof. eauto. Qed.
(*Global*) Hint Resolve in_compartment_opt_sound_is_some'.

(*** Proofs for `contained_compartments' ***)

Theorem contained_compartments_spec : forall C,
  contained_compartments C = true <->
  (forall c a, c \in C -> (a \in jump_targets c \/ a \in store_targets c) ->
               exists c', c' \in C /\ a \in address_space c').
Proof.
  admit.
(*
  clear S; intros; unfold contained_compartments; rewrite subset_spec; split.
  - intros SUBSET c a IN_c IN_a.
    specialize SUBSET with a;
      rewrite ->in_app_iff in SUBSET; repeat rewrite ->concat_in in SUBSET.
    destruct SUBSET as [A [IN_A IN_a_A]].
    + destruct IN_a;
        [left; exists (jump_targets c) | right; exists (store_targets c)];
        (split; [apply in_map_iff; eauto | assumption]).
    + apply in_map_iff in IN_A; destruct IN_A as [c' [EQ IN_c']].
      exists c'; subst; tauto.
  - intros SPEC a IN_app.
    apply in_app_iff in IN_app.
    rewrite concat_in; repeat rewrite ->concat_in in IN_app.
    destruct IN_app as [[J [IN_J IN_a]] | [S [IN_S IN_a]]].
    + apply in_map_iff in IN_J; destruct IN_J as [c [EQ_J IN_c]].
      destruct SPEC with c a as [c' [IN_c' IN_a_c']];
        try solve [rewrite <- EQ_J in *; auto].
      exists (address_space c'); split; auto.
      apply in_map_iff; eauto.
    + apply in_map_iff in IN_S; destruct IN_S as [c [EQ_S IN_c]].
      destruct SPEC with c a as [c' [IN_c' IN_a_c']];
        try solve [rewrite <- EQ_S in *; auto].
      exists (address_space c'); split; auto.
      apply in_map_iff; eauto.
*)
Qed.

(*** Proofs for/requiring `good_compartments' ***)

Theorem good_in2_no_common_addresses : forall C c1 c2,
  good_compartments C ->
  In2 c1 c2 C ->
  forall a, ~ (a \in address_space c1 /\ a \in address_space c2).
Proof.
  admit.
(*  intros until 0; intros GOOD IN2 a [IN_A1 IN_A2].
  assert (Ins : In c1 C /\ In c2 C) by auto; destruct Ins as [IN_c1 IN_c2].
  apply good_compartments__in2_disjoint in IN2; auto.
  apply not_false_iff_true in IN2; apply IN2.
  unfold disjoint; destruct (set_intersection _ _) eqn:SI;
    [|reflexivity].
  rewrite -> nil_iff_not_in in SI; specialize SI with a.
  rewrite -> set_intersection_spec in SI by eauto 3; tauto.*)
Qed.
(*Global*) Hint Resolve good_in2_no_common_addresses.

Theorem in_unique_compartment : forall C p c1 c2,
  good_compartments C ->
  C ⊢ p ∈ c1 ->
  C ⊢ p ∈ c2 ->
  c1 = c2.
Proof.
  admit.
(*
  intros until 0; intros GOOD IC1 IC2.
  assert (OVERLAPPING : disjoint (address_space c1) (address_space c2) =
                        false) by
    (eapply in_same_compartment__overlapping; eauto 3).
  assert (NOL : non_overlapping C = true) by auto.
  rewrite ->non_overlapping_spec in NOL; auto.
  have [|/eqP neq_c1c2] := altP (c1 =P c2); auto.
  lapply (NOL c1 c2); [congruence | eauto].*)
Qed.
(*Global*) Hint Resolve in_unique_compartment.

(*** Proofs about `good_state' ***)

(* For `auto' *)
Lemma good_state__previous_is_compartment : forall MM,
  good_state MM ->
  previous MM \in compartments MM.
Proof.
  admit. (*unfold good_state; intros; repeat rewrite ->andb_true_iff in *; tauto.*)
Qed.
(*Global*) Hint Resolve good_state__previous_is_compartment.

(* For `auto' *)
Lemma good_state_decomposed__previous_is_compartment : forall pc R M C sk prev,
  good_state (State pc R M C sk prev) ->
  prev \in C.
Proof.
  intros pc R M C sk prev;
    apply (good_state__previous_is_compartment (State pc R M C sk prev)).
Qed.
(*Global*) Hint Resolve good_state_decomposed__previous_is_compartment.

(* For `auto' *)
Lemma good_state__good_compartments : forall MM,
  good_state MM -> good_compartments (compartments MM).
Proof.
  admit. (*unfold good_state; intros; repeat rewrite ->andb_true_iff in *; tauto.*)
Qed.
(*Global*) Hint Resolve good_state__good_compartments.

(* For `auto' *)
Lemma good_state_decomposed__good_compartments : forall pc R M C sk prev,
  good_state (State pc R M C sk prev) -> good_compartments C.
Proof.
  intros pc R M C sk prev;
    apply (good_state__good_compartments (State pc R M C sk prev)).
Qed.
(*Global*) Hint Resolve good_state_decomposed__good_compartments.

(* For `auto' *)
Lemma good_state__syscalls_separated : forall MM,
  good_state MM -> syscalls_separated (mem MM) (compartments MM).
Proof.
  admit. (*
  unfold good_state; intros; repeat rewrite ->andb_true_iff in *; tauto.*)
Qed.
(*Global*) Hint Resolve good_state__syscalls_separated.

(* For `auto' *)
Lemma good_state_decomposed__syscalls_separated : forall pc R M C sk prev,
  good_state (State pc R M C sk prev) -> syscalls_separated M C.
Proof.
  admit. (*
  intros pc R M C sk prev;
    apply (good_state__syscalls_separated (State pc R M C sk prev)).*)
Qed.
(*Global*) Hint Resolve good_state_decomposed__syscalls_separated.

(* For `auto' *)
Lemma good_state__syscalls_present : forall MM,
  good_state MM -> syscalls_present (compartments MM).
Proof.
  admit. (*
  unfold good_state; intros; repeat rewrite ->andb_true_iff in *; tauto.*)
Qed.
(*Global*) Hint Resolve good_state__syscalls_present.

(* For `auto' *)
Lemma good_state_decomposed__syscalls_present : forall pc R M C sk prev,
  good_state (State pc R M C sk prev) -> syscalls_present C.
Proof.
  intros pc R M C sk prev;
    apply (good_state__syscalls_present (State pc R M C sk prev)).
Qed.
(*Global*) Hint Resolve good_state_decomposed__syscalls_present.

(*** Proofs for `permitted_now_in' ***)

Theorem permitted_now_in_spec : forall C sk prev pc c,
  good_compartments C ->
  (permitted_now_in C sk prev pc ?= c <->
   C ⊢ pc ∈ c /\ (c = prev \/ (sk = JUMPED /\ pc \in jump_targets prev))).
Proof.
  intros C sk prev pc c GOODS; unfold permitted_now_in; simpl; split.
  - intros PNI.
    destruct (in_compartment_opt C pc) as [c'|] eqn:ICO; simpl in PNI;
      [|discriminate].
    destruct (_ || _) eqn:COND; simpl in PNI; [|discriminate].
    inversion PNI; subst c'.
    apply in_compartment_opt_correct in ICO; auto.
    split; [assumption|].
    admit. (*move: COND => /orP [/eqP EQ | /andP [/eqP EQ /set_elem_true IN]]; auto.*)
  - intros [IC COND].
    apply in_compartment_opt_sound in IC; auto.
    rewrite IC; simpl.
    admit. (*move: COND => [/eqP -> | [/eqP -> /set_elem_true ELEM]]; simpl.
    + reflexivity.
    + rewrite ELEM /=; auto; rewrite orb_true_r; reflexivity.*)
Qed.

Corollary permitted_now_in__in_compartment_opt : forall C sk prev pc c,
  good_compartments C ->
  permitted_now_in C sk prev pc ?= c ->
  in_compartment_opt C pc ?= c.
Proof.
  intros C sk prev pc c GOODS PNI.
  apply permitted_now_in_spec in PNI; try assumption.
  move: PNI => [IC _]; apply in_compartment_opt_sound in IC; auto.
Qed.

(*** Proofs about `good_syscall' and `get_syscall'. ***)

Theorem isolate_good : forall MM, good_syscall isolate MM = true.
Proof.
  clear S; unfold isolate, good_syscall; intros MM; simpl.
  destruct (good_state MM) eqn:GOOD; [simpl|reflexivity].
  destruct (in_compartment_opt _ _) as [c_sys0|] eqn:ICO_sys;
    [simpl|reflexivity].
  destruct (syscall_address_space _ _) eqn:SAS; [simpl|reflexivity].
  destruct MM as [pc R M C sk c];
    unfold good_state, isolate, isolate_fn;
    rewrite (lock in_compartment_opt);
    simpl in *.
  (* Now, compute in `isolate_fn'. *)
  admit. (*
  let (* Can't get the binder name, so we provide it *)
      DO var := match goal with
                  | |- match (do! _ <- ?GET;   _) with _ => _ end =>
                    let def_var := fresh "def_" var in
                    destruct GET as [var|] eqn:def_var
                  | |- match (match ?COND with true => _ | false => None end)
                       with _ => _ end =>
                    destruct COND eqn:var
                end; simpl; [|reflexivity]
  in DO c_sys;
     DO pA; DO pJ; DO pS;
     destruct c as [A J S] eqn:def_AJS; simpl;
     DO A'; DO SUBSET_A'; DO NONEMPTY_A';
     DO J'; DO SUBSET_J';
     DO S'; DO SUBSET_S';
     DO pc'; DO c_next; DO SAME; DO RETURN_OK;
     set (c_upd := <<set_difference A A',J,S>>) in *;
     set (c'    := <<A',J',S'>>) in *;
     repeat rewrite <-def_AJS in *.
  assert (c_sys0 = c_sys) by
    (apply permitted_now_in__in_compartment_opt in def_c_sys;
     solve [eauto 3 | congruence]);
    subst c_sys0.
  unfold good_compartments in *; simpl;
    assert (TEMP : good_compartments C = true) by
      (rewrite /good_state /good_compartments /= in GOOD *;
       repeat rewrite ->andb_true_iff in GOOD; andb_true_split; try tauto).
    move TEMP before GOOD; unfold good_compartments in TEMP;
    repeat rewrite ->andb_true_iff in TEMP; destruct TEMP as [[GOODS NOL] CC].
  assert (IN : In c C) by
    (rewrite /good_state /= in GOOD; repeat rewrite ->andb_true_iff in GOOD;
     destruct (elem c C); [assumption | repeat invh and; discriminate]).
  assert (NONEMPTY_A_A' : nonempty (set_difference A A') = true). {
    move/eqP in SAME; subst c_next.
    rewrite <-(lock in_compartment_opt) in *; simpl in *.
    destruct (set_difference A A'); [simpl in *|reflexivity].
    subst c' c_upd; destruct (set_elem pc' A').
    - inversion def_c_next; subst; discriminate.
    - apply in_compartment_opt_correct,in_compartment_spec in def_c_next;
        [simpl in * | auto using delete_preserves_forallb].
      tauto.
  }
  let is_good := (subst c c' c_upd; unfold good_compartment; simpl;
                  andb_true_split; eauto 2)
  in assert good_compartment c     by (rewrite ->forallb_forall in GOODS; auto);
     assert good_compartment c'    by is_good;
     assert good_compartment c_upd by is_good.
  assert (C'_DISJOINT :
            forallb (fun c'' => good_compartment c'' &&
                                disjoint (address_space c) (address_space c''))
                    (delete c C) =
            true). {
    rewrite ->non_overlapping_spec in NOL by assumption.
    apply forallb_forall; intros ct IN_ct; andb_true_split.
    - apply delete_in_iff in IN_ct; destruct IN_ct; eapply forallb_forall;
      eassumption.
    - apply NOL. apply delete_in_iff in IN_ct; apply in_neq_in2; intuition.
  }
  assert (NONEMPTY_A : nonempty A) by
    (destruct A,A'; simpl in NONEMPTY_A_A'; solve [auto | discriminate]).
  assert (NOT_SYSCALL_c : ~~ syscall_address_space M c). {
    apply/negP; intro SAS'; subst c.
    rewrite /syscall_address_space (lock elem) /= in SAS'.
    destruct A as [|sc [|]]; auto.
    apply permitted_now_in_spec in def_c_sys; eauto 3.
    move/id in def_c_sys; move/id in NONEMPTY_A_A'; move/id in SUBSET_A'.
    assert (NIN_pc : ~ In sc A'). {
      apply nonempty_iff_in in NONEMPTY_A_A'.
      destruct NONEMPTY_A_A' as [a IN_diff].
      apply set_difference_spec in IN_diff; auto; simpl in IN_diff.
      move: IN_diff => [[-> | []] NIN] //.
    }
    rewrite ->subset_spec in SUBSET_A'; auto; simpl in SUBSET_A'.
    destruct A' as [|a' A']; [discriminate|].
    move: (SUBSET_A' a' (or_introl Logic.eq_refl)) => [EQ | []].
    apply NIN_pc; rewrite EQ; auto.
  }
  assert (USER_c : user_address_space M c). {
    assert (SS : syscalls_separated M C = true) by eauto; simpl in *.
    rewrite ->forallb_forall in SS.
    specialize (SS c IN).
    move: SS => /orP [UAS | SAS'] //.
    by rewrite SAS' in NOT_SYSCALL_c.
  }
  assert (DIFF : c <> c_sys). {
    intro; subst c_sys.
    by rewrite SAS in NOT_SYSCALL_c.
  }
  unfold non_overlapping; repeat rewrite all_tail_pairs_tail; simpl in *.
  andb_true_split; auto;
    try (eapply forallb_impl; [|apply C'_DISJOINT]; cbv beta;
         simpl; intros c''; rewrite andb_true_iff; intros []; intros GOOD'';
         apply disjoint_subset; auto; simpl).
  - (* locked elem c_sys [:: c_upd, c' & delete c C] *)
    assert (In c_sys (c_upd :: c' :: delete c C)). {
      do 2 right. apply delete_in_iff; split; auto.
      apply permitted_now_in_spec in def_c_sys; eauto 3.
    }
    rewrite <-(lock elem);
      destruct (elem c_sys (c_upd :: c' :: delete c C)) eqn:ELEM;
      rewrite ELEM; auto.
  - (* non_overlapping c_upd c' *)
    unfold disjoint; subst c c_upd c'; simpl in *.
    rewrite ->set_intersection_difference_distrib,
            ->set_intersection_self_id,
            ->set_difference_intersection_distrib,
            ->set_difference_self_annihilating,
            ->set_intersection_nil_r
      by auto.
    destruct (set_difference A A'); [discriminate | reflexivity].
  - subst c; intros e; rewrite set_difference_spec; tauto.
  - subst c; eapply subset_spec; eassumption.
  - unfold contained_compartments; subst c_upd c'; simpl.
    assert (A_separated : forall a, In a A <->
                                    In a (set_difference A A') \/ In a A'). {
      intros; specialize (elem a A'); intros;
        rewrite ->set_difference_spec by (subst c; eauto 2);
        rewrite ->subset_spec in SUBSET_A'.
      split; [|destruct 1]; solve [auto | tauto].
    }
    assert (As_same : forall a,
              In a (set_difference A A' ++ A' ++
                    concat (List.map address_space (delete c C))) <->
              In a (concat (List.map address_space C))). {
      intros.
      repeat rewrite in_app_iff.
      rewrite <- or_assoc, <- A_separated.
      repeat rewrite concat_in; split.
      - destruct 1 as [IN_a_A | [A'' [IN_A'' IN_a_A'']]].
        + exists A; split; auto. apply in_map_iff; exists c; subst c; auto.
        + exists A''. split; auto.
          apply in_map_iff in IN_A''; destruct IN_A'' as [c'' [EQ_A'' IN_c'']].
          apply in_map_iff; exists c''; apply delete_in_iff in IN_c''; tauto.
      - destruct 1 as [A'' [IN_A'' IN_a_A'']].
        destruct (elem a A) as [IN_a_A | NOT_IN_a_A];
          [tauto|right].
        exists A''; split; auto.
        apply in_map_iff in IN_A''; destruct IN_A'' as [c'' [EQ_A'' IN_c'']].
        apply in_map_iff; exists c''; split; auto.
        apply delete_in_iff; split; auto.
        subst c; destruct c'' as [A''' J'' S'']; simpl in *; subst A''';
          intros EQ; inversion EQ; subst; congruence.
    }
    rewrite subset_spec; intros a.
    rewrite As_same.
    repeat rewrite <- app_assoc; repeat rewrite in_app_iff.
    rewrite ->subset_spec in SUBSET_A',SUBSET_J',SUBSET_S';
      specialize SUBSET_A' with a;
      specialize SUBSET_J' with a;
      specialize SUBSET_S' with a;
      rewrite ->set_union_spec in SUBSET_J', SUBSET_S'.
    intros [IN_a_J | [IN_a_J' | [IN_a_JTs |
           [IN_a_S | [IN_a_S' |  IN_a_SMs]]]]].
    (* There are essentially three proofs here: (1) In a J/S; (2) In a J'/S'
       (which calls out to (1)); and (3) In a (concat (map
       jump_targets/store_targets (delete c C)).  I could not figure out how to
       Ltac them together nicely, however, so here you have it. *)
    + (* Proof (1) *)
      move CC after IN_a_J.
      rewrite ->contained_compartments_spec in CC;
        specialize (CC c a IN);
        subst c; simpl in *;
        specialize (CC (or_introl IN_a_J));
        destruct CC as [c'' [IN_c'' IN_a_c'']].
      apply concat_in; exists (address_space c'').
      split; auto. apply in_map_iff; eauto.
    + (* Proof (2) *)
      destruct (SUBSET_J' IN_a_J') as [IN_A | IN_J].
      * apply concat_in; exists A; split; auto.
        apply in_map_iff; exists c; subst c; simpl; tauto.
      * (* Proof (1) *)
        rewrite ->contained_compartments_spec in CC;
          specialize (CC c a IN);
          subst c; simpl in *;
          specialize (CC (or_introl IN_J));
          destruct CC as [c'' [IN_c'' IN_a_c'']].
        apply concat_in; exists (address_space c'').
        split; auto. apply in_map_iff; eauto.
    + (* Proof (3) *)
      apply concat_in in IN_a_JTs; destruct IN_a_JTs as [J'' [IN_J'' IN_a_J'']].
      apply in_map_iff in IN_J''; destruct IN_J'' as [c'' [EQ_J'' IN_c'']].
      apply delete_in_iff in IN_c''; destruct IN_c'' as [NEQ_c'' IN_c''].
      move CC after IN_a_J''.
      rewrite ->contained_compartments_spec in CC.
        specialize (CC c'' a IN_c'');
        rewrite EQ_J'' in CC;
        specialize (CC (or_introl IN_a_J''));
        destruct CC as [c''' [IN_c''' IN_a_c''']].
      apply concat_in; exists (address_space c'''); split; auto.
      apply in_map_iff; eauto.
    + (* Proof (1) *)
      rewrite ->contained_compartments_spec in CC;
        specialize (CC c a IN);
        subst c; simpl in *;
        specialize (CC (or_intror IN_a_S));
        destruct CC as [c'' [IN_c'' IN_a_c'']].
      apply concat_in; exists (address_space c'').
      split; auto. apply in_map_iff; eauto.
    + (* Proof (2) *)
      destruct (SUBSET_S' IN_a_S') as [IN_A | IN_S].
      * apply concat_in; exists A; split; auto.
        apply in_map_iff; exists c; subst c; simpl; tauto.
      * (* Proof (1) *)
        rewrite ->contained_compartments_spec in CC;
          specialize (CC c a IN);
          subst c; simpl in *;
          specialize (CC (or_intror IN_S));
          destruct CC as [c'' [IN_c'' IN_a_c'']].
        apply concat_in; exists (address_space c'').
        split; auto. apply in_map_iff; eauto.
    + (* Proof (3) *)
      apply concat_in in IN_a_SMs; destruct IN_a_SMs as [S'' [IN_S'' IN_a_S'']].
      apply in_map_iff in IN_S''; destruct IN_S'' as [c'' [EQ_S'' IN_c'']].
      apply delete_in_iff in IN_c''; destruct IN_c'' as [NEQ_c'' IN_c''].
      move CC after IN_a_S''.
      rewrite ->contained_compartments_spec in CC.
        specialize (CC c'' a IN_c'');
        rewrite EQ_S'' in CC;
        specialize (CC (or_intror IN_a_S''));
        destruct CC as [c''' [IN_c''' IN_a_c''']].
      apply concat_in; exists (address_space c'''); split; auto.
      apply in_map_iff; eauto.
  - (* user_address_space M c_upd || syscall_address_space M c_upd *)
    subst c c_upd; simpl in *.
    apply/orP; left.
    eapply forallb_subset; [|apply USER_c].
    intros a IN_diff.
    apply set_difference_spec in IN_diff; tauto.
  - (* user_address_space M c' || syscall_address_space M c' *)
    subst c c_upd; simpl in *.
    apply/orP; left.
    eapply forallb_subset; [|apply USER_c].
    intros a IN_A'.
    eapply subset_spec in SUBSET_A'; eassumption.
  - (* syscalls_separated (delete c C) *)
    assert (SS : syscalls_separated M C = true) by eauto; simpl in *.
    eauto using delete_preserves_forallb.
  - (* syscalls_present *)
    assert (SP : syscalls_present C) by eauto.
    rewrite /syscalls_present /table /is_true in SP *.
    rewrite ->forallb_forall in SP; rewrite ->forallb_forall.
    intros sc IN_sc; specialize (SP sc IN_sc); cbv [compose] in *.
    destruct sc as [sc sc_fn]; cbv [address] in *; clear IN_sc sc_fn.
    destruct (in_compartment_opt C sc) as [c_sc|] eqn:ICO;
      [clear SP | discriminate].
    generalize ICO => ICO'.
    apply in_compartment_opt_correct, in_compartment_spec in ICO'; auto;
      destruct ICO' as [IN_c_sc IN_sc].
    destruct (c_sc == c) eqn:EQ; move/eqP in EQ.
    + subst; simpl in *.
      assert (IN_sc' : In sc (set_difference A A') \/ In sc A'). {
        apply set_union_spec.
        rewrite set_union_difference_distrib; auto.
        rewrite set_difference_self_annihilating set_difference_nil_r.
        rewrite set_union_comm; auto.
        rewrite set_union_subset_id; auto.
        apply subset_spec; auto.
      }
      destruct IN_sc' as [IN_diff | IN_A'].
      * apply set_elem_true in IN_diff; auto.
        rewrite IN_diff; auto.
      * apply set_elem_true in IN_A'; auto.
        rewrite IN_A'; destruct (set_elem sc (set_difference A A')); auto.
    + simpl.
      destruct (set_elem sc (set_difference A A')); auto.
      destruct (set_elem sc A'); auto.
      assert (IN_c_sc' : In c_sc (delete c C)) by by apply delete_in_iff.
      assert (IC' : delete c C ⊢ sc ∈ c_sc) by by apply in_compartment_spec.
      apply in_compartment_opt_sound in IC'; auto.
      rewrite IC'; auto. *)
Qed.
(*Global*) Hint Resolve isolate_good.

Lemma good_compartments_preserved_for_add_to_compartment_component :
  forall c c' C,
    good_compartments C ->
    In c C ->
    address_space c = address_space c' ->
    jump_targets c' \subset address_space c :|: jump_targets c ->
    store_targets c' \subset address_space c :|: store_targets c ->
    good_compartments (c' :: delete c C).
Proof.
  intros c c' C GOOD IN ADDR SUBSET_J SUBSET_S.
  unfold good_compartments; repeat (andb_true_split; simpl); auto.
  - rewrite ->non_overlapping_replace', forallb_forall by assumption.
    intros c'' IN'; rewrite ->delete_in_iff in IN'; destruct IN' as [NEQ IN'].
    replace (address_space c') with (address_space c) by assumption.
    admit. (*
    assert (NOL : non_overlapping C) by auto;
      rewrite ->non_overlapping_spec' in NOL by assumption.
    auto.*)
  - apply contained_compartments_spec; simpl.
    intros d a IN_d IN_a.
    assert (CC : contained_compartments C) by auto.
    admit. (*
    rewrite ->contained_compartments_spec in CC.
    rewrite ->subset_spec in SUBSET_J,SUBSET_S;
      specialize (SUBSET_J a); specialize (SUBSET_S a);
      rewrite ->set_union_spec in SUBSET_J,SUBSET_S.
    have [EQ | /eqP NEQ] := altP (c' =P d); ssubst.
    + specialize (CC c a IN); simpl in CC.
      destruct IN_a as [IN_a | IN_a];
        [apply SUBSET_J in IN_a | apply SUBSET_S in IN_a];
        ( destruct IN_a as [IN_a | IN_a]
        ; [ rewrite ->ADDR in IN_a; solve [eauto]
          | destruct CC as [d' [IN_d' IN'_a]];
            [ solve [auto]
            | solve [ have [? | /eqP ?] := altP (d' =P c);
                      [ ssubst; rewrite ->ADDR in *; eauto
                      | exists d'; rewrite ->delete_in_iff; auto ]]]]).
    + destruct IN_d as [<- | IN_d]; [congruence|].
      specialize CC with d a. destruct CC as [d' [IN_d' IN'_a]].
      * apply delete_in_iff in IN_d; tauto.
      * exact IN_a.
      * have [? | /eqP ?] := altP (d' =P c); [ssubst; rewrite ->ADDR in *; eauto|].
        exists d'; rewrite ->delete_in_iff; auto.*)
Qed.

Lemma add_to_compartment_component_good : forall addr rd wr MM,
  (forall X c, address_space c = address_space (wr X c)) ->
  (forall X c, jump_targets (wr X c) = jump_targets c \/
               jump_targets (wr X c) = X /\ rd c = jump_targets c) ->
  (forall X c, store_targets (wr X c) = store_targets c \/
               store_targets (wr X c) = X /\ rd c = store_targets c) ->
  good_syscall (Syscall addr (add_to_compartment_component rd wr)) MM.
Proof.
  admit. (*
  clear S.
  unfold good_syscall; simpl;
    intros _ rd wr MM ADDR rd_set wr_good eqJ eqS.
  destruct (good_state MM) eqn:GOOD; [simpl|reflexivity].
  destruct (in_compartment_opt _ _) as [c_sys0|] eqn:ICO_pc;
    [simpl|reflexivity].
  destruct (syscall_address_space _ _) eqn:SAS; [simpl|reflexivity].
  destruct MM as [pc R M C sk c];
    unfold good_state, add_to_compartment_component;
    rewrite (lock in_compartment_opt) (lock elem);
    simpl in *.
  generalize GOOD; rewrite /good_state /= =>
    /andP [/andP [/andP [PREV GOODS] SS] SP].
  destruct (permitted_now_in _ _ _ _) as [c_sys|] eqn:PNI; [simpl|reflexivity].
  destruct (c != c_sys)               eqn:NEQ;             [simpl|reflexivity].
  destruct (get R syscall_arg1)       as [p|];             [simpl|reflexivity].
  destruct (set_elem p        _)      eqn:ELEM;            [simpl|reflexivity].
  destruct (get R ra)                 as [pc'|];           [simpl|reflexivity].
  rewrite <-(lock in_compartment_opt);
    destruct (in_compartment_opt _ pc') as [c_next|] eqn:ICO_pc';
    simpl; [|reflexivity].
  destruct (_ == c_next) eqn:EQ; move/eqP in EQ; simpl;
    [subst c_next | reflexivity].
  destruct (set_elem pc' _) eqn:ELEM_pc'; simpl; [|reflexivity].
  assert (IN : In c C) by
    (repeat rewrite ->andb_true_iff in GOOD; destruct (elem c C);
     [assumption | repeat invh and; discriminate]).
  assert (GOOD_c : good_compartment c) by eauto.
  assert (c_sys0 = c_sys) by
    (apply permitted_now_in__in_compartment_opt in PNI; congruence);
    subst c_sys0.
  apply in_compartment_opt_correct, in_compartment_spec in ICO_pc; auto.
  rewrite <-(lock elem).
  andb_true_split.
  - move/eqP in NEQ.
    assert (In c_sys (delete c C)) by (apply delete_in_iff; split; auto; tauto).
    match goal with |- context[elem c_sys ?C'] =>
      destruct (elem c_sys C') eqn:ELEM'; try rewrite ELEM'; auto
    end.
  - destruct c as [A J S]; simpl in *.
    rewrite ->set_elem_true, ->set_union_spec in ELEM by
      (apply set_union_preserves_set; eauto 2).
    apply good_compartments_preserved_for_add_to_compartment_component; auto;
      rewrite subset_spec; intros a; rewrite set_union_spec; simpl;
      match goal with
        | |- context[wr ?X ?c] =>
          destruct (eqJ X c) as [eqWr | [eqWr eqRd]]; rewrite eqWr; auto
        | |- context[wr ?X ?c] =>
          destruct (eqS X c) as [eqWr | [eqWr eqRd]]; rewrite eqWr; auto
      end;
      rewrite ->insert_unique_spec, eqRd in *; simpl in *;
      intros [-> | IN_a]; auto.
  - rewrite (user_address_space_same M _ c); auto.
    rewrite (syscall_address_space_same M _ c); auto.
    unfold is_true in SS; rewrite ->forallb_forall in SS; auto.
  - auto using delete_preserves_forallb.
  - move/id in SP.
    rewrite /syscalls_present /table /is_true in SP *.
    rewrite ->forallb_forall in SP; rewrite ->forallb_forall.
    intros sc IN_sc; specialize (SP sc IN_sc); cbv [compose] in *.
    destruct sc as [sc sc_fn]; cbv [address] in *; clear IN_sc sc_fn.
    simpl; rewrite <-ADDR.
    destruct (in_compartment_opt C sc) as [c_sc|] eqn:ICO;
      [clear SP | discriminate].
    generalize ICO => ICO'.
    apply in_compartment_opt_correct, in_compartment_spec in ICO'; auto;
      destruct ICO' as [IN_c_sc IN_sc].
    destruct (c_sc == c) eqn:EQ; move/eqP in EQ.
    + subst; simpl in *.
      destruct (set_elem sc (address_space c)) eqn:ELEM'; auto.
      apply set_elem_false in ELEM'; auto.
    + destruct (set_elem sc (address_space c)); auto.
      assert (IN_c_sc' : In c_sc (delete c C)) by by apply delete_in_iff.
      assert (IC' : delete c C ⊢ sc ∈ c_sc) by by apply in_compartment_spec.
      apply in_compartment_opt_sound in IC'; auto.
      rewrite IC'; auto. *)
Qed.

Theorem add_to_jump_targets_good : forall MM,
  good_syscall add_to_jump_targets MM.
Proof.
  clear - t ops spec.
  intros; apply add_to_compartment_component_good;
    intros; destruct c as [A J S]; auto.
Qed.
(*Global*) Hint Resolve add_to_jump_targets_good.

Theorem add_to_store_targets_good : forall MM,
  good_syscall add_to_store_targets MM.
Proof.
  clear - t ops spec.
  intros; apply add_to_compartment_component_good;
    intros; destruct c as [A J S]; auto.
Qed.
(*Global*) Hint Resolve add_to_store_targets_good.

Corollary good_syscalls_b : forall MM,
  all (fun sc => good_syscall sc MM) table.
Proof. admit. (* unfold table; simpl; intros; andb_true_split; auto. *) Qed.
(*Global*) Hint Resolve good_syscalls_b.

(*
Corollary good_syscalls : forall MM sc,
  In sc table -> good_syscall sc MM.
Proof. intros MM; apply forallb_forall; auto. Qed.
(*Global*) Hint Resolve good_syscalls.
*)

Lemma get_syscall_in : forall addr sc,
  get_syscall addr ?= sc -> In sc table.
Proof.
  unfold get_syscall; intros addr sc GS; apply find_in in GS; tauto.
Qed.
(*Global*) Hint Resolve get_syscall_in.

Lemma get_syscall_good : forall addr sc,
  get_syscall addr ?= sc -> forall MM, good_syscall sc MM.
Proof.
  admit. (*
  intros addr sc GS; apply get_syscall_in in GS; auto.*)
Qed.
(*Global*) Hint Resolve get_syscall_good.

(*** Proofs about the machine. ***)

Generalizable Variables MM.

Theorem step_deterministic : forall MM0 MM1 MM2
                                    (STEP1 : step MM0 MM1)
                                    (STEP2 : step MM0 MM2),
  good_state MM0 ->
  MM1 = MM2.
Proof.
  intros; destruct STEP1, STEP2; subst; try congruence;
    repeat match goal with pc' := _ |- _ => subst pc' end;
    match goal with ST : State _ _ _ _ _ _ = State _ _ _ _ _ _ |- _ =>
      inversion ST; subst
    end;
    try match goal with
      | INST  : decode ?M ?pc ?= _,
        INST' : get    ?M ?pc = None |- _
        => unfold decode in INST; rewrite INST' in INST; discriminate
    end;
    repeat f_equal; try congruence.
  match goal with
    |- (match ?b1 == 0 with true => 1 | false => Word.casts ?x1 end) =
       (match ?b2 == 0 with true => 1 | false => Word.casts ?x2 end) =>
    replace b2 with b1 by congruence; replace x2 with x1 by congruence
  end; reflexivity.
Qed.

Lemma stepping_syscall_preserves_good : forall MM MM' sc,
  get (mem MM) (pc MM)                                    = None       ->
  pc MM                                                   = address sc ->
  is_some (in_compartment_opt (compartments MM) (pc MM))        ->
  good_syscall sc MM                                            ->
  semantics sc MM                                        ?= MM'        ->
  good_state MM                                                 ->
  good_state MM'                                         .
Proof.
  intros MM MM' sc INST PC ICO GOODSC CALL GOOD.
  unfold good_syscall in GOODSC; rewrite GOOD CALL in GOODSC.
  destruct MM as [pc R M C sk prev]; simpl in *; subst.
  destruct (in_compartment_opt C _) as [c|] eqn:ICO';
    [clear ICO; rename ICO' into ICO | discriminate].
  destruct (syscall_address_space M c) eqn:SAS; [assumption | clear GOODSC].
  apply in_compartment_opt_correct in ICO; eauto 3;
    destruct ICO as [IN IN'].
  assert (SS : syscalls_separated M C) by eauto; simpl in *.
  admit. (*
  rewrite ->forallb_forall in SS.
  specialize (SS c IN).
  rewrite SAS orb_false_r /user_address_space /= in SS.
  rewrite ->forallb_forall in SS.
  specialize (SS (address sc) IN').
  by rewrite INST in SS. *)
Qed.

Lemma syscall_step_preserves_good : forall MM MM' sc,
  get (mem MM) (pc MM)  = None ->
  get_syscall (pc MM)  ?= sc   ->
  semantics sc MM      ?= MM'  ->
  good_state MM         ->
  good_state MM'       .
Proof.
  intros MM MM' sc INST GETSC CALL GOOD; generalize GETSC => GETSC'.
  unfold get_syscall,table in GETSC; simpl in *.
  assert (SP : syscalls_present (compartments MM)) by eauto.
  unfold syscalls_present,is_true in SP; rewrite ->forallb_forall in SP.
  unfold get_syscall,table in *; simpl in *.
  specialize SP with sc; cbv [compose] in *.
  repeat match type of GETSC with
    | context[if ?COND then _ else _] =>
        destruct COND eqn:EQ; [move/eqP in EQ | clear EQ]
    | None ?= _ =>
      discriminate
    | Some _ ?= _ =>
      lapply SP; [clear SP; intros SP; simpl in SP | solve [auto]];
      clear CALL
  end; inversion GETSC; subst; clear GETSC;
  eapply stepping_syscall_preserves_good; try eassumption; eauto 3.
  (* Have to repeat this thanks, I think, to evar unification timing *)
  - rewrite <-EQ; auto.
  - rewrite <-EQ; auto.
  - rewrite <-EQ; auto. admit.
Qed.

Lemma previous_compartment : forall `(STEP : step MM MM'),
  good_state MM -> (* This hypothesis only needed for syscalls *)
  previous MM' \in compartments MM'.
Proof. admit. (*
  intros MM MM' STEP GOOD; destruct STEP; try solve [
    subst; simpl in *;
    match goal with
      | STEP : permitted_now_in ?C ?sk ?prev ?pc ?= ?c |- context[elem ?c ?C] =>
        apply permitted_now_in_spec in STEP; try (eauto 3);
        destruct STEP as [IC _]; apply in_compartment_spec in IC;
        destruct IC; destruct (elem c C); [auto | contradiction]
    end
  ].
  (* Syscalls *)
  assert (GOOD' : good_state MM') by
   (apply syscall_step_preserves_good with MM sc; subst; assumption);
   auto.*)
Qed.
(*Global*) Hint Resolve previous_compartment.

Lemma good_compartments_preserved : forall `(STEP : step MM MM'),
  good_state MM -> (* Full strength only needed for syscalls *)
  good_compartments (compartments MM').
Proof.
  intros MM MM' STEP GOOD;
    assert (GOODC : good_compartments (compartments MM)) by auto;
    destruct STEP; try (subst; simpl in *; exact GOODC).
  (* Syscalls *)
  assert (GOOD' : good_state MM') by
   (apply syscall_step_preserves_good with MM sc; subst; assumption);
   auto.
Qed.
(*Global*) Hint Resolve good_compartments_preserved.

Lemma syscalls_separated_preserved : forall `(STEP : step MM MM'),
  good_state MM ->
  syscalls_separated (mem MM') (compartments MM').
Proof.
  admit. (*
  intros MM MM' STEP GOOD; destruct STEP;
    try solve [subst; cbv [mem compartments]; eauto 2].
  - (* Store *)
    subst; assert (SS : syscalls_separated M C) by eauto; simpl in *.
    rewrite ->forallb_forall in *.
    intros c' IN; specialize (SS c' IN).
    apply/orP; move/orP in SS.
    clear S; destruct c' as [A J S]; simpl in *.
    destruct SS as [UAS | SAS]; [left | right].
    + eapply forallb_impl; [|apply UAS].
      move=> /= a GET.
      destruct (get M a) eqn:GET';
        [clear GET; rename GET' into GET | discriminate].
      destruct (defined_preserved GET UPDR) as [v GET'].
      by rewrite GET'.
    + unfold syscall_address_space in *; cbv [address_space] in *.
      destruct A as [|sc [|]]; auto.
      move/andP in SAS; apply/andP.
      split; [move: SAS => [/negP NGET _]; apply/negP | tauto].
      generalize UPDR => SET; unfold upd in SET.
      destruct (get M p) as [old|] eqn:GET; [|discriminate].
      assert (NEQ : sc <> p) by by intro; subst; rewrite GET in NGET.
      assert (EQ : get M' sc = get M sc) by
        (eapply get_upd_neq; try eassumption; apply word_map_axioms).
      rewrite EQ; assumption.
  - (* Syscall *)
    assert (GOOD' : good_state MM') by
      (apply syscall_step_preserves_good with MM sc; subst; assumption);
      auto. *)
Qed.

Lemma syscalls_present_preserved : forall `(STEP : step MM MM'),
  good_state MM ->
  syscalls_present (compartments MM').
Proof.
  intros MM MM' STEP GOOD; destruct STEP;
    try solve [subst; simpl in *; eauto 2].
  (* Syscall *)
  assert (GOOD' : good_state MM') by
    (apply syscall_step_preserves_good with MM sc; subst; assumption);
    auto.
Qed.

Theorem good_state_preserved : forall `(STEP : step MM MM'),
  good_state MM  ->
  good_state MM'.
Proof.
  intros MM MM' STEP GOOD; unfold good_state; andb_true_split.
  - eapply previous_compartment; eassumption.
  - eapply good_compartments_preserved; eassumption.
  - eapply syscalls_separated_preserved; eassumption.
  - eapply syscalls_present_preserved; eassumption.
Qed.
(*Global*) Hint Resolve good_state_preserved.

Lemma step__permitted_now_in : forall `(STEP : step MM MM'),
  good_state MM ->
  exists c, permitted_now_in (compartments MM)
                             (step_kind MM)
                             (previous MM)
                             (pc MM)
              ?= c.
Proof.
  clear S; intros MM MM' STEP GOOD; destruct STEP; subst; simpl in *;
    try (eexists; eassumption).
  (* Syscalls *)
  unfold get_syscall in GETSC; unfold table in GETSC; simpl in GETSC.
  repeat match type of GETSC with
    | context[if ?EQ then _ else _] => destruct EQ
    | None ?= _ => discriminate
    | Some _ ?= _ => inversion GETSC; subst; clear GETSC;
                     simpl in CALL;
                     destruct (permitted_now_in C sk prev pc0);
                     [eauto | discriminate]
  end.
Qed.

Theorem was_in_compartment : forall `(STEP : step MM MM'),
  good_state MM ->
  in_compartment_opt (compartments MM) (pc MM).
Proof.
  clear S.
  intros MM MM' STEP GOOD; apply step__permitted_now_in in STEP; auto.
  move: STEP => [c /permitted_now_in_spec PNI].
  repeat (lapply PNI; clear PNI; [intros PNI | auto]).
  destruct PNI as [IC _].
  apply in_compartment_opt_sound in IC; auto.
  by rewrite IC.
  admit.
Qed.

Theorem permitted_pcs : forall MM MM' MM''
                               (STEP : step MM MM') (STEP' : step MM' MM''),
  good_state MM ->
  exists c, compartments MM ⊢ pc MM ∈ c /\
            (pc MM' \in address_space c \/ pc MM' \in jump_targets c).
Proof.
  admit.
(*
  clear S; intros MM MM' MM'' STEP STEP' GOOD; generalize STEP => STEPPED;
    destruct STEP;
    subst; simpl in *;
    try solve
      [ apply permitted_now_in_spec in STEP; eauto 3;
        apply step__permitted_now_in in STEP'; eauto 3;
        destruct STEP' as [c' PNI];
        destruct STEP as [IC STEP]; exists c; split; [exact IC|];
        assert (good_compartment c) by eauto;
        apply permitted_now_in_spec in PNI; simpl in *; eauto 3;

        destruct PNI as [IC' [-> | [EQ IN_J]]];
          [|solve [discriminate | right; auto]];
        left; apply in_compartment_spec in IC'; tauto ].
  (* Syscalls *)
  generalize GOOD =>
    /andP /= [/andP [/andP [ELEM /andP [/andP [GOODS NOL] CC]] SS] SP].
  unfold is_true in GOODS; rewrite ->forallb_forall in GOODS.
  unfold get_syscall in GETSC; unfold table in GETSC; simpl in GETSC.
  repeat match type of GETSC with
    | context[if ?EQ then _ else _] => destruct EQ
    | None ?= _ => discriminate
    | Some _ ?= _ => inversion GETSC; subst; clear GETSC
  end.
  - (* isolate *)
    unfold semantics,isolate,isolate_fn in CALL;
      rewrite (lock in_compartment_opt) in CALL;
      simpl in *.
    let (* Can't get the binder name, so we provide it *)
        DO var := match type of CALL with
                    | (do! _ <- ?GET;   _) ?= _ =>
                      let def_var := fresh "def_" var in
                      destruct GET as [var|] eqn:def_var
                    | (match ?COND with true => _ | false => None end) ?= _ =>
                      destruct COND eqn:var
                  end; simpl in CALL; [|discriminate]
    in DO c_sys; DO pA; DO pJ; DO pS;
       destruct prev as [A J S] eqn:def_AJS; simpl in CALL;
       DO A'; DO SUBSET_A'; DO NONEMPTY_A';
       DO J'; DO SUBSET_J';
       DO S'; DO SUBSET_S';
       DO pc'; DO c_next; DO SAME; DO RETURN_OK;
       set (c_upd := <<set_difference A A',J,S>>) in *;
       set (c'    := <<A',J',S'>>) in *;
       repeat rewrite <-def_AJS in *;
       inversion CALL; subst; clear CALL; simpl.
    apply permitted_now_in__in_compartment_opt in def_c_sys; eauto 3.
    exists c_sys; split.
    + apply in_compartment_opt_correct; eauto.
    + right; apply set_elem_true in RETURN_OK; [assumption|].
      apply in_compartment_opt_correct, in_compartment_spec in def_c_sys;
        [|eauto 3].
      destruct def_c_sys as [IN IN']; specialize (GOODS c_sys IN); auto.
  - (* add_to_jump_targets *)
    unfold semantics,add_to_jump_targets,add_to_compartment_component in CALL;
      rewrite (lock in_compartment_opt) in CALL;
      simpl in CALL.
    let (* Can't get the binder name, so we provide it *)
        DO var := match type of CALL with
                    | (do! _ <- ?GET;   _) ?= _ =>
                      let def_var := fresh "def_" var in
                      destruct GET as [var|] eqn:def_var
                    | (match ?COND with true => _ | false => None end) ?= _ =>
                      destruct COND eqn:var
                  end; simpl in CALL; [|discriminate]
    in DO c_sys; DO NEQ;
       DO p; DO ELEM_p;
       DO pc'; DO c_next;
       destruct (_ == c_next) eqn:EQ; simpl in CALL; [|discriminate];
       DO RETURN_OK;
       move/eqP in EQ; rewrite EQ in def_c_next CALL;
       inversion CALL; subst; simpl in *; clear CALL.
    apply permitted_now_in__in_compartment_opt in def_c_sys; eauto 3.
    exists c_sys; split.
    + apply in_compartment_opt_correct; eauto.
    + right; apply set_elem_true in RETURN_OK; [assumption|].
      apply in_compartment_opt_correct, in_compartment_spec in def_c_sys;
        [|eauto 3].
      destruct def_c_sys as [IN IN']; specialize (GOODS c_sys IN); auto.
  - (* add_to_store_targets *)
    unfold semantics,add_to_store_targets,add_to_compartment_component in CALL;
      rewrite (lock in_compartment_opt) in CALL;
      simpl in CALL.
    let (* Can't get the binder name, so we provide it *)
        DO var := match type of CALL with
                    | (do! _ <- ?GET;   _) ?= _ =>
                      let def_var := fresh "def_" var in
                      destruct GET as [var|] eqn:def_var
                    | (match ?COND with true => _ | false => None end) ?= _ =>
                      destruct COND eqn:var
                  end; simpl in CALL; [|discriminate]
    in DO c_sys; DO NEQ;
       DO p; DO ELEM_p;
       DO pc'; DO c_next;
       destruct (_ == c_next) eqn:EQ; simpl in CALL; [|discriminate];
       DO RETURN_OK;
       move/eqP in EQ; rewrite EQ in def_c_next CALL;
       inversion CALL; subst; simpl in *; clear CALL.
    apply permitted_now_in__in_compartment_opt in def_c_sys; eauto 3.
    exists c_sys; split.
    + apply in_compartment_opt_correct; eauto.
    + right; apply set_elem_true in RETURN_OK; [assumption|].
      apply in_compartment_opt_correct, in_compartment_spec in def_c_sys;
        [|eauto 3].
      destruct def_c_sys as [IN IN']; specialize (GOODS c_sys IN); auto.*)
Qed.

Theorem permitted_modifications : forall `(STEP : step MM MM') c,
  good_state MM        ->
  compartments MM ⊢ pc MM ∈ c ->
  forall a,
    get (mem MM) a <> get (mem MM') a ->
    a \in address_space c \/ a \in store_targets c.
Proof.
  intros MM MM' STEP c GOOD_STATE IC a DIFF; destruct STEP;
    try (subst; simpl in *; congruence).
  - (* Store *)
    subst; simpl in *.
    have [EQ|/eqP NE] := altP (a =P p); [subst|].
    + apply permitted_now_in__in_compartment_opt,
            in_compartment_opt_correct
        in STEP; eauto 3.
      admit.
      (*apply in_app_iff; replace c0 with c in * by eauto 3; assumption.*)
    + rewrite (PartMaps.get_upd_neq NE UPDR) in DIFF. by intuition.
  - (* Syscall *)
    unfold get_syscall,table in *; simpl in *.
    repeat match type of GETSC with
      | (if ?COND then Some _ else _) ?= _ =>
        destruct COND
      | Some _ ?= _ =>
        inversion GETSC; subst; clear GETSC
      | None ?= _ =>
        discriminate
    end; simpl in *;
      repeat match type of CALL with
        | (do! _ <- ?GET; _) ?= _ =>
          destruct GET; simpl in CALL; [|discriminate]
        | (do! guard ?COND; _) ?= _ =>
          destruct COND; simpl in CALL; [|discriminate]
        | match ?c with <<_,_,_>> => _ end ?= _ =>
          destruct c; simpl in CALL
      end;
      inversion CALL; subst; simpl in *; clear CALL;
      elim DIFF; reflexivity.
Qed.

End WithClasses.

Module Notations.
(* Repeated notations *)
Notation memory t := (word_map t (word t)).
Notation registers t := (reg_map t (word t)).
Notation "<< A , J , S >>" := (@Compartment _ A J S) (format "<< A , J , S >>").
Notation "C ⊢ p ∈ c" := (in_compartment p C c) (at level 70).
Notation "C ⊢ p1 , p2 , .. , pk ∈ c" :=
  (and .. (and (C ⊢ p1 ∈ c) (C ⊢ p2 ∈ c)) .. (C ⊢ pk ∈ c))
  (at level 70).
End Notations.

Module Hints.
(* Can be updated automatically by an Emacs script; see `global-hint.el' *)
(* Start globalized hint section *)
Hint Resolve good_compartments__non_overlapping.
Hint Resolve good_compartments__contained_compartments.
Hint Resolve good_no_duplicates.
Hint Resolve non_overlapping_subset.
Hint Resolve non_overlapping_tail.
Hint Resolve non_overlapping_delete.
Hint Resolve non_overlapping_delete'.
Hint Resolve non_overlapping_replace.
Hint Resolve non_overlapping_replace'.
Hint Resolve in_compartment_element.
Hint Resolve in_compartment__in_address_space.
Hint Resolve in_same_compartment.
Hint Resolve unique_here_not_there.
Hint Resolve unique_must_be_here.
Hint Resolve in_same_compartment__overlapping.
Hint Resolve in_compartment_opt_correct.
Hint Resolve in_compartment_opt_missing_correct.
Hint Resolve in_compartment_opt_present.
Hint Resolve in_compartment_opt_is_some.
Hint Resolve in_compartment_opt_sound.
Hint Resolve in_compartment_opt_sound'.
Hint Resolve in_compartment_opt_sound_is_some.
Hint Resolve in_compartment_opt_sound_is_some'.
Hint Resolve good_in2_no_common_addresses.
Hint Resolve in_unique_compartment.
Hint Resolve good_state__previous_is_compartment.
Hint Resolve good_state_decomposed__previous_is_compartment.
Hint Resolve good_state__good_compartments.
Hint Resolve good_state_decomposed__good_compartments.
Hint Resolve good_state__syscalls_separated.
Hint Resolve good_state_decomposed__syscalls_separated.
Hint Resolve good_state__syscalls_present.
Hint Resolve good_state_decomposed__syscalls_present.
Hint Resolve isolate_good.
Hint Resolve add_to_jump_targets_good.
Hint Resolve add_to_store_targets_good.
Hint Resolve good_syscalls_b.
Hint Resolve get_syscall_in.
Hint Resolve get_syscall_good.
Hint Resolve previous_compartment.
Hint Resolve good_compartments_preserved.
Hint Resolve good_state_preserved.
(* End globalized hint section *)
End Hints.

End Abs.
