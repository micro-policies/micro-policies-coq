Require Import List Arith Sorted Bool.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop fintype finset.

Require Import lib.Integers lib.utils lib.partial_maps lib.ordered common.common.
Require Import lib.list_utils lib.ssr_list_utils lib.ssr_set_utils.
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
  [&& c \in cs & p \in address_space c].

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
  let C'    := c_upd :: c' :: rem_all c C in
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
  let C' := c' :: rem_all c C in
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

(*** Proofs for `disjoint_comp' ***)

Lemma disjoint_comp_irrefl c :
  ~~ disjoint_comp c c.
Proof.
  by rewrite /disjoint_comp /= orb_diag -setI_eq0 setIid andb_comm andb_negb_r.
Qed.
(*Global*) Hint Resolve disjoint_comp_irrefl.

Lemma disjoint_comp_sym c1 c2 :
  disjoint_comp c1 c2 = disjoint_comp c2 c1.
Proof. by rewrite /disjoint_comp /= disjoint_sym orb_comm. Qed.
(*Global*) Hint Resolve disjoint_comp_sym.

Lemma common_not_disjoint_comp a c1 c2 :
  a \in address_space c1 -> a \in address_space c2 ->
  ~~ disjoint_comp c1 c2.
Proof.
  move=> IN_A1 IN_A2.
  by rewrite /disjoint_comp /= negb_and (common_not_disjoint a) // orbT.
Qed.
(*Global*) Hint Resolve common_not_disjoint_comp.
Arguments common_not_disjoint_comp a [c1 c2] _ _.

Lemma common_not_disjoint_comp_decomposed a A1 J1 S1 A2 J2 S2 :
  a \in A1 -> a \in A2 ->
  ~~ disjoint_comp <<A1,J1,S1>> <<A2,J2,S2>>.
Proof. by move=> *; rewrite (common_not_disjoint_comp a). Qed.
(*Global*) Hint Resolve common_not_disjoint_comp_decomposed.
Arguments common_not_disjoint_comp_decomposed a [A1 J1 S1 A2 J2 S2] _ _.

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
  clear S.
  move=> C /andP [NOL CC].
  rewrite /non_overlapping -all_pairs_in2_comm in NOL; last done.
  apply all_pairs_distinct_nodup in NOL.
  + by apply/uniqP.
  + by move=> ?; apply negbTE, disjoint_comp_irrefl.
Qed.
(*Global*) Hint Resolve good_no_duplicates.

(*** Proofs for `non_overlapping' ***)

Theorem non_overlapping_subset : forall C1 C2,
  uniq C1 ->
  subpred (ssrbool.mem C1) (ssrbool.mem C2) ->
  non_overlapping C2 ->
  non_overlapping C1.
Proof.
  rewrite /non_overlapping; move=> C1 C2 SUBSET ND NOL.
  apply all_pairs__all_tail_pairs; rewrite -all_pairs_in2_comm in NOL; last done.
  rewrite /subpred /= in ND.
  apply all_pairs_subset with C2.
  - by move=> c /inP IN; apply/inP; apply ND.
  - by apply/uniqP.
  - by [].
Qed.
(*Global*) Hint Resolve non_overlapping_subset.

Theorem non_overlapping_tail : forall c C,
  non_overlapping (c :: C) -> non_overlapping C.
Proof.
  move=> c C.
  by rewrite /non_overlapping all_tail_pairs_tail; move=> /andP[].
Qed.
(*Global*) Hint Resolve non_overlapping_tail.

Theorem non_overlapping_spec : forall C,
  non_overlapping C <->
  (forall c1 c2,
     In2 c1 c2 C ->
     disjoint_comp c1 c2).
Proof.
  move=> C; rewrite /non_overlapping.
  by rewrite -all_pairs_in2_comm // /is_true all_pairs_spec.
Qed.

Corollary good_compartments__in2_disjoint : forall C c1 c2,
  good_compartments C ->
  In2 c1 c2 C ->
  disjoint_comp c1 c2.
Proof.
  move=> C c1 c2 /andP [NOL _].
  by move/non_overlapping_spec in NOL; apply NOL.
Qed.
(*Global*) Hint Resolve good_compartments__in2_disjoint.

Theorem non_overlapping_rem : forall c C,
  non_overlapping C ->
  non_overlapping (rem_all c C).
Proof.
  move=> c C; rewrite !non_overlapping_spec.
  move=> NOL c1 c2 IN2; apply NOL.
  by move: IN2; rewrite rem_all_is_delete; apply in2_delete.
Qed.
(*Global*) Hint Resolve non_overlapping_rem.

Corollary non_overlapping_rem' : forall c C,
  good_compartments C ->
  non_overlapping (rem_all c C).
Proof. auto. Qed.
(*Global*) Hint Resolve non_overlapping_rem'.

Lemma non_overlapping_replace : forall c c' C,
  non_overlapping C ->
  non_overlapping (c' :: rem_all c C) =
  all (disjoint_comp c') (rem_all c C).
Proof.
  move=> c c' C NOL;
    rewrite /non_overlapping all_tail_pairs_tail;
    fold (non_overlapping (rem c C));
    replace @forallb with @all by reflexivity.
  case (all _ (rem_all _ _)) => //=.
  by apply non_overlapping_rem.
Qed.
(*Global*) Hint Resolve non_overlapping_replace.

Lemma non_overlapping_replace' : forall c c' C,
  good_compartments C ->
  non_overlapping (c' :: rem_all c C) =
  all (disjoint_comp c') (rem_all c C).
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

Theorem in_compartment_here : forall p C A J S,
  p \in A -> <<A,J,S>> :: C ⊢ p ∈ <<A,J,S>>.
Proof.
  clear S; move=> p C A J S IN.
  rewrite /in_compartment inE /=.
  apply/andP; split.
  - by apply/orP; left.
  - by [].
Qed.
(*Global*) Hint Resolve in_compartment_here.

Theorem in_compartment_there : forall p C c c',
  C ⊢ p ∈ c' -> c :: C ⊢ p ∈ c'.
Proof.
  move=> p C c c' /andP [IN_C IN_A].
  rewrite /in_compartment inE /=.
  apply/andP; split.
  - by apply/orP; right.
  - by [].
Qed.
(*Global*) Hint Resolve in_compartment_there.

Theorem in_compartment_element C p c :
  C ⊢ p ∈ c ->
  c \in C.
Proof. by move=> /andP []. Qed.
(*Global*) Hint Resolve in_compartment_element.

Theorem in_compartment__in_address_space C p c :
  C ⊢ p ∈ c -> p \in address_space c.
Proof. by move=> /andP []. Qed.
(*Global*) Hint Resolve in_compartment__in_address_space.

Theorem in_same_compartment C p p' c :
  C ⊢ p ∈ c ->
  p' \in address_space c ->
  C ⊢ p' ∈ c.
Proof. by move=> /andP [] *; apply/andP. Qed.
(*Global*) Hint Resolve in_same_compartment.

Theorem unique_here_not_there C p c :
  c \notin C     ->
  c :: C ⊢ p ∈ c ->
  ~~ (C ⊢ p ∈ c).
Proof.
  move=> /negP OUT HERE; apply/negP; move=> /in_compartment_element THERE.
  by contradict OUT.
Qed.
(*Global*) Hint Resolve unique_here_not_there.

Theorem unique_must_be_here C p c c' :
  c' \notin C     ->
  c :: C ⊢ p ∈ c' ->
  c = c'.
Proof.
  move=> OUT /andP [IN_C _].
  rewrite inE in IN_C; move/orP in IN_C.
  case: IN_C.
  - by move=> /eqP.
  - by move/negP in OUT.
Qed.
(*Global*) Hint Resolve unique_must_be_here.

Theorem in_same_compartment__overlapping C p c1 c2 :
  C ⊢ p ∈ c1 ->
  C ⊢ p ∈ c2 ->
  ~~ disjoint_comp c1 c2.
Proof.
  move=> /in_compartment__in_address_space IC1
         /in_compartment__in_address_space IC2.
  by rewrite (common_not_disjoint_comp p).
Qed.
(*Global*) Hint Resolve in_same_compartment__overlapping.

Theorem in_compartment_opt_correct : forall C p c,
  in_compartment_opt C p ?= c -> C ⊢ p ∈ c.
Proof.
  elim=> [// | /= c' C IH p c].
  case I: (p \in address_space c'); move: I; [move=> IN | move=> NIN].
  - case=> ?; subst; apply/andP; split.
    + by rewrite inE; apply/orP; left.
    + by [].
  - move=> ICO; apply IH in ICO.
    by apply in_compartment_there.
Qed.
(*Global*) Hint Resolve in_compartment_opt_correct.

Theorem in_compartment_opt_missing_correct : forall C p,
  in_compartment_opt C p = None -> forall c, ~~ (C ⊢ p ∈ c).
Proof.
  elim=> [// | /= c' C IH p].
  case I: (p \in address_space c'); move: I; [by [] | move=> NIN NICO].
  move/IH in NICO; move=> c; apply/negP; move=> /andP [IN_C IN_A].
  move: (NICO c) => /negP NICO'; apply NICO'; apply/andP.
  split; last by [].
  rewrite inE in IN_C; move/orP in IN_C.
  case: IN_C => [/eqP ? | //]; subst.
  by rewrite NIN in IN_A.
Qed.
(*Global*) Hint Resolve in_compartment_opt_missing_correct.

Theorem in_compartment_opt_present : forall C p c,
  C ⊢ p ∈ c -> exists c', in_compartment_opt C p ?= c'.
Proof.
  elim=> [// | /= c' C IH p c /andP [IN_C IN_A]].
  rewrite inE in IN_C.
  case/orP: IN_C => [/eqP<- | IN_C].
  - by rewrite IN_A; exists c.
  - specialize IH with p c; rewrite /in_compartment IN_C IN_A /= in IH;
      case: (IH erefl) => [c'' ICO].
    rewrite ICO.
    by case: (p \in address_space c') => /=; [exists c' | exists c''].
Qed.
(*Global*) Hint Resolve in_compartment_opt_present.

Corollary in_compartment_opt_is_some C p c :
  C ⊢ p ∈ c -> in_compartment_opt C p.
Proof.
  move=> IC; apply in_compartment_opt_present in IC.
  by case: IC => c' ICO; rewrite ICO.
Qed.
(*Global*) Hint Resolve in_compartment_opt_is_some.

Theorem in_compartment_opt_sound : forall C p c,
  non_overlapping C ->
  C ⊢ p ∈ c ->
  in_compartment_opt C p ?= c.
Proof.
  elim=> [// | /= c' C IH p c NOL /andP [IN_C IN_A]].
  rewrite inE in IN_C.
  case/orP: IN_C=> [/eqP<- | IN_C]; first by rewrite IN_A.
  case IN_A': (p \in address_space c'); last rename IN_A' into NIN_A'.
  - have NDJ : (~~ disjoint_comp c' c) by apply (common_not_disjoint_comp p).
    have IN2 : In2 c' c (c' :: C) by apply In2_here_1; apply/inP.
    apply non_overlapping_spec in IN2; last assumption.
    by contradict IN2; apply/negP.
  - apply IH.
    + by apply non_overlapping_tail in NOL.
    + by apply/andP.
Qed.
(*Global*) Hint Resolve in_compartment_opt_sound.

Corollary in_compartment_opt_sound' : forall C p c,
  good_compartments C ->
  C ⊢ p ∈ c ->
  in_compartment_opt C p ?= c.
Proof. auto. Qed.
(*Global*) Hint Resolve in_compartment_opt_sound'.

Corollary in_compartment_opt_sound_is_some C p c :
  non_overlapping C ->
  C ⊢ p ∈ c -> in_compartment_opt C p.
Proof. by move=> NOL IC; apply in_compartment_opt_sound in IC; rewrite ?IC. Qed.
(*Global*) Hint Resolve in_compartment_opt_sound_is_some.

Corollary in_compartment_opt_sound_is_some' : forall C p c,
  good_compartments C ->
  C ⊢ p ∈ c -> in_compartment_opt C p.
Proof. eauto. Qed.
(*Global*) Hint Resolve in_compartment_opt_sound_is_some'.

(*** Proofs for `contained_compartments' ***)

Theorem contained_compartments_spec C :
  contained_compartments C = true <->
  (forall c a, c \in C -> (a \in jump_targets c \/ a \in store_targets c) ->
               exists c', c' \in C /\ a \in address_space c').
Proof.
  clear S; rewrite /contained_compartments; split.
  - rewrite subUset; move=> /andP [IN_a_J IN_a_S] c a IN_c IN_a.
    by case: IN_a => IN_a; [move: IN_a_J => IN | move: IN_a_S => IN];
       move/subsetP/(_ a) in IN;
       rewrite (bigcup_seq_in c) // in IN;
       move/(_ erefl)/bigcup_seqP in IN.
  - move=> SPEC; apply/subsetP; move=> a IN_a; rewrite inE in IN_a.
    apply/bigcup_seqP.
    by case/orP: IN_a => IN_a; move: IN_a => /bigcup_seqP [c [IN_c IN_a]];
       apply (SPEC c) => //;
       [left | right].
Qed.    

(*** Proofs for/requiring `good_compartments' ***)

Theorem good_in2_no_common_addresses C c1 c2 :
  good_compartments C ->
  In2 c1 c2 C ->
  forall a, ~ (a \in address_space c1 /\ a \in address_space c2).
Proof.
  move=> GOOD IN2 a [IN_A1 IN_A2].
  have [/inP IN_c1 /inP IN_c2] : In c1 C /\ In c2 C by auto.
  apply good_compartments__in2_disjoint in IN2 => //.
  by contradict IN2; apply/negP; apply (common_not_disjoint_comp a).
Qed.
(*Global*) Hint Resolve good_in2_no_common_addresses.

Theorem in_unique_compartment C p c1 c2 :
  good_compartments C ->
  C ⊢ p ∈ c1 ->
  C ⊢ p ∈ c2 ->
  c1 = c2.
Proof.
  move=> /andP [/non_overlapping_spec NOL CC] IC1 IC2.
  have OL : ~~ disjoint_comp c1 c2
    by eapply in_same_compartment__overlapping; eassumption.
  have [|/eqP neq_c1c2] := altP (c1 =P c2); first by [].
  lapply (NOL c1 c2); first by move/negP in OL.
  by apply in_neq_in2 => //;
     apply/inP; eapply in_compartment_element; eassumption.
Qed.
(*Global*) Hint Resolve in_unique_compartment.

(*** Proofs about `good_state' ***)

(* For `auto' *)
Lemma good_state__previous_is_compartment MM :
  good_state MM ->
  previous MM \in compartments MM.
Proof. by move=> /and4P [] *. Qed.
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
Lemma good_state__good_compartments MM :
  good_state MM -> good_compartments (compartments MM).
Proof. by move=> /and4P [] *. Qed.
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
Lemma good_state__syscalls_separated MM :
  good_state MM -> syscalls_separated (mem MM) (compartments MM).
Proof. by move=> /and4P [] *. Qed.
(*Global*) Hint Resolve good_state__syscalls_separated.

(* For `auto' *)
Lemma good_state_decomposed__syscalls_separated : forall pc R M C sk prev,
  good_state (State pc R M C sk prev) -> syscalls_separated M C.
Proof.
  intros pc R M C sk prev;
    apply (good_state__syscalls_separated (State pc R M C sk prev)).
Qed.
(*Global*) Hint Resolve good_state_decomposed__syscalls_separated.

(* For `auto' *)
Lemma good_state__syscalls_present MM :
  good_state MM -> syscalls_present (compartments MM).
Proof. by move=> /and4P [] *. Qed.
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
    by move: COND => /orP [/eqP EQ | /andP [/eqP EQ IN]]; auto.
  - intros [IC COND].
    apply in_compartment_opt_sound in IC; auto.
    rewrite IC; simpl.
    move: COND => [/eqP -> | [/eqP -> ELEM]]; simpl.
    + reflexivity.
    + rewrite ELEM /=; auto; rewrite orb_true_r; reflexivity.
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
  let (* Can't get the binder name, so we provide it *)
      DO var := match goal with
                  | |- match (do! _ <- ?GET;   _) with _ => _ end = true =>
                    let def_var := fresh "def_" var in
                    destruct GET as [var|] eqn:def_var
                  | |- match (match ?COND with true => _ | false => None end)
                       with _ => _ end = true =>
                    destruct COND eqn:var
                end; simpl; [|reflexivity]
  in DO c_sys;
     DO pA; DO pJ; DO pS;
     destruct c as [A J S] eqn:def_AJS; simpl;
     DO A'; DO SUBSET_A'; DO NONEMPTY_A';
     DO J'; DO SUBSET_J';
     DO S'; DO SUBSET_S';
     DO pc'; DO c_next; DO SAME; DO RETURN_OK;
     set (c_upd := <<A :\: A',J,S>>) in *;
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
    repeat rewrite ->andb_true_iff in TEMP; destruct TEMP as [NOL CC].
  assert (IN : In c C) by
    (rewrite /good_state /= in GOOD; repeat rewrite ->andb_true_iff in GOOD;
     destruct (elem c C);
     [assumption | repeat invh and; try discriminate; by apply/inP]).
  assert (NONEMPTY_A_A' : (A :\: A') != set0). {
    move/eqP in SAME; subst c_next.
    rewrite <-(lock in_compartment_opt) in *; simpl in *.
    have [EQ|] := altP (A :\: A' =P set0); last by [].
    subst c' c_upd; rewrite EQ in_set0 in def_c_next.
    have [IN_pc' | NIN_pc'] := boolP (pc' \in A').
    - rewrite IN_pc' in def_c_next; inversion def_c_next; subst.
      by move/eqP in NONEMPTY_A'.
    - rewrite (negbTE NIN_pc') in def_c_next.
      apply in_compartment_opt_correct in def_c_next.
      move: def_c_next => /andP /= [] _.
      by rewrite in_set0.
  }
  assert (C'_DISJOINT :
            forallb (fun c'' => disjoint_comp c c'') (delete c C) = true). {
    move/non_overlapping_spec in NOL.
    apply forallb_forall; intros ct IN_ct.
    apply NOL. apply delete_in_iff in IN_ct; apply in_neq_in2; intuition.
  }
  assert (NONEMPTY_A : A != set0) by
    by apply/negP => /eqP EQ; rewrite EQ set0D in NONEMPTY_A_A';
       move/eqP in NONEMPTY_A_A'.
  assert (NOT_SYSCALL_c : ~~ syscall_address_space M c). {
    apply/negP; intro SAS'; subst c.
    move: SAS'; rewrite /syscall_address_space /=
      => /existsP [sc /andP [NGET /andP [IN_sc /eqP EQ_sc]]];
      rewrite !inE in IN_sc.
    rewrite EQ_sc in c_upd SAME def_c_next; subst A.
    apply permitted_now_in_spec in def_c_sys; eauto 3.
    move/id in def_c_sys; move/id in NONEMPTY_A_A'; move/id in SUBSET_A'.
    assert (NIN_pc : sc \notin A'). {
      move: NONEMPTY_A_A' => /set0Pn [a IN_diff].
      rewrite in_setD in IN_diff.
      move: IN_diff => /andP [NIN IN_a] //.
      by rewrite in_set1 in IN_a; move: IN_a => /eqP<-.
    }
    move/subsetP in SUBSET_A'.
    move: NONEMPTY_A' => /set0Pn [a' IN_a'].
    move: (SUBSET_A' a' IN_a'); rewrite in_set1 => /eqP ?; subst a'.
    by move/negP in NIN_pc.
  }
  assert (USER_c : user_address_space M c). {
    assert (SS : syscalls_separated M C = true) by
      (eapply good_state_decomposed__syscalls_separated; eassumption).
    rewrite /syscalls_separated in SS; rewrite ->forallb_forall in SS.
    specialize (SS c IN).
    move: SS => /orP [UAS | SAS'] //.
    by rewrite SAS' in NOT_SYSCALL_c.
  }
  assert (DIFF : c <> c_sys). {
    intro; subst c_sys.
    by rewrite SAS in NOT_SYSCALL_c.
  }
  rewrite /non_overlapping !all_tail_pairs_tail /=.
  andb_true_split; auto;
    try (eapply forallb_impl; [|apply C'_DISJOINT]; cbv beta;
         simpl; intros c''; rewrite andb_true_iff; intros []; intros GOOD'';
         apply disjoint_subset; auto; simpl).
  - (* c_sys \in [:: c_upd, c' & delete c C] *)
    apply/inP; rewrite rem_all_is_delete.
    do 2 right; apply delete_in_iff; split; auto.
    assert (GC : good_compartments C) by
      (eapply good_state_decomposed__good_compartments; eassumption).
    by move: def_c_sys => /permitted_now_in_spec => /(_ GC) [] /andP [] /inP.
  - (* non_overlapping c_upd c' *)
    rewrite /disjoint_comp; subst c c_upd c'; simpl in *.
    rewrite -setI_eq0 setIDAC setDIl setDv setI0 eq_refl andbT.
    by rewrite NONEMPTY_A_A'.
  - eapply forallb_impl; last (rewrite rem_all_is_delete; exact C'_DISJOINT).
    subst c c_upd => d.
    rewrite /disjoint_comp /= NONEMPTY_A NONEMPTY_A_A' /= -!setI_eq0 setIDAC
            => /eqP->.
    by rewrite set0D eq_refl.
  - eapply forallb_impl; last (rewrite rem_all_is_delete; exact C'_DISJOINT).
    subst c c' => d.
    rewrite /disjoint_comp /= NONEMPTY_A NONEMPTY_A' /= -!setI_eq0
           => /eqP DJ.
    apply setSI with (C := address_space d) in SUBSET_A'.
    rewrite DJ subset0 in SUBSET_A'.
    move: SUBSET_A' => /eqP->.
    by rewrite eq_refl.
  - by rewrite rem_all_is_delete; apply delete_preserves_all_tail_pairs.
  - unfold contained_compartments; subst c_upd c'; simpl.
    assert (As_same :
              (A :\: A' :|: A' :|: \bigcup_(d <- rem_all c C) address_space d) =
              \bigcup_(d <- C) address_space d). {
      rewrite -subsetDU // (big_rem c (r := C)) def_AJS /=.
      - do 2 f_equal.
        by rewrite rem_filter //; eauto 3.
      - by apply/inP; subst c.
    }
    apply/subsetP => a /=.
    rewrite !big_cons /= !setUA As_same !inE.
    let fix_sub SS := move/subsetP/(_ a) in SS; rewrite ?inE in SS
    in fix_sub SUBSET_A'; fix_sub SUBSET_J'; fix_sub SUBSET_S'.
    move/inP in IN; move/contained_compartments_spec in CC;
      move: (CC) => /(_ c a IN) CC_c; subst c; simpl in *.
    (* a \in J/S *)
    let solve_in_orig  := apply/CC_c; by [left | right] in
    (* a \in J'/S' *)
    let solve_in_prime := idtac; match goal with
                            | SS  : is_true (a \in pred_of_set ?JS) -> _
                            , IN' : is_true (a \in pred_of_set ?JS) |- _ =>
                                move: (SS IN') => /orP [] *;
                                [exists <<A,J,S>> | solve_in_orig]
                          end in
    (* a \in \bigcup_(d <- rem_all c C) jump_targets/store_targets d *)
    let solve_in_rest  := idtac; match goal with
                           | INs : is_true
                                     (a \in pred_of_set
                                            (\bigcup_(_ <- _) _ _)) |- _ =>
                               move: INs
                                     => /bigcup_seqP [c'' [IN_c'' IN_a'']];
                               rewrite in_rem_all in IN_c'';
                               move: IN_c'' => /andP [/eqP NEQ_c'' IN_c''];
                               apply/(CC c'' a IN_c''); by [left | right]
                         end
    in by rewrite -!orbA; move=> /or4P [         IN_a_J | IN_a_J' | IN_a_JTs
                                       | /or3P [ IN_a_S | IN_a_S' | IN_a_STs ]];
          apply/bigcup_seqP;
          by [solve_in_orig | solve_in_prime | solve_in_rest].
  - (* user_address_space M c_upd || syscall_address_space M c_upd *)
    subst c c_upd; simpl in *.
    apply/orP; left.
    by eapply forall_subset; [rewrite subsetDl | exact USER_c].
  - (* user_address_space M c' || syscall_address_space M c' *)
    subst c c_upd; simpl in *.
    apply/orP; left.
    by eapply forall_subset; [|exact USER_c].
  - (* syscalls_separated (delete c C) *)
    
    assert (SS : syscalls_separated M C = true) by
      (eapply good_state_decomposed__syscalls_separated; eassumption).
    replace @all with @forallb by reflexivity; rewrite rem_all_is_delete.
    auto using delete_preserves_forallb.
  - (* syscalls_present *)
    assert (SP : syscalls_present C) by
      (eapply good_state_decomposed__syscalls_present; eassumption).
    rewrite /syscalls_present /table /is_true in SP *.
    rewrite ->forallb_forall in SP; rewrite ->forallb_forall.
    intros sc IN_sc; specialize (SP sc IN_sc); cbv [compose] in *.
    destruct sc as [sc sc_fn]; cbv [address] in *; clear IN_sc sc_fn.
    destruct (in_compartment_opt C sc) as [c_sc|] eqn:ICO;
      [clear SP | discriminate].
    move: (ICO) => /in_compartment_opt_correct /andP [IN_c_sc IN_sc].
    destruct (c_sc == c) eqn:EQ.
    + move/eqP in EQ; subst; simpl in *.
      have [->|->] // : sc \in A :\: A' \/ sc \in A'
        by apply/setUP; rewrite -subsetDU.
      by case: (sc \in A :\: A').
    + simpl.
      case: (sc \in A :\: A') => //; case: (sc \in A') => //.
      have /in_compartment_opt_sound -> // : rem_all c C ⊢ sc ∈ c_sc by
        apply/andP; rewrite in_rem_all EQ /=.
      by apply non_overlapping_rem.
Qed.
(*Global*) Hint Resolve isolate_good.

Lemma good_compartments_preserved_for_add_to_compartment_component :
  forall c c' C,
    good_compartments C ->
    In c C ->
    address_space c = address_space c' ->
    jump_targets c' \subset address_space c :|: jump_targets c ->
    store_targets c' \subset address_space c :|: store_targets c ->
    good_compartments (c' :: rem_all c C).
Proof.
  move=> c c' C GOOD /inP IN ADDR SUBSET_J SUBSET_S.
  unfold good_compartments; repeat (andb_true_split; simpl); auto.
  - rewrite ->non_overlapping_replace', forallb_forall by assumption.
    move=> c'' /inP; rewrite in_rem_all => /andP [/eqP NEQ IN'].
    rewrite /disjoint_comp /= -!ADDR.
    have /non_overlapping_spec NOL : non_overlapping C by auto.
    by apply/NOL/in_neq_in2; (apply nesym || apply/inP).
  - apply/contained_compartments_spec => /= d a IN_d IN_a.
    have /contained_compartments_spec CC : contained_compartments C by auto.
    let sub SS := move/subsetP/(_ a) in SS; rewrite inE in SS
    in sub SUBSET_J; sub SUBSET_S.
    have [EQ | /eqP NEQ] := altP (c' =P d); ssubst.
    + specialize (CC c a IN); simpl in CC.
      case: IN_a => IN_a;
        [apply SUBSET_J in IN_a | apply SUBSET_S in IN_a];
        case/orP: IN_a => IN_a.
      (* The first two... *)
      * by rewrite ADDR in IN_a; exists d.
      * case: CC => [ | d' [IN_d' IN'_a]]; first by left.
        { have [EQ | NEQ] := altP (d' =P c).
          - by subst; exists d; rewrite -ADDR.
          - by exists d'; rewrite inE in_rem_all NEQ /= IN_d' orbT. }
      (* ...are the same as the second two (except for a left/right swap). *)
      * by rewrite ADDR in IN_a; exists d.
      * case: CC => [ | d' [IN_d' IN'_a]]; first by right.
        { have [EQ | NEQ] := altP (d' =P c).
          - by subst; exists d; rewrite -ADDR.
          - by exists d'; rewrite inE in_rem_all NEQ /= IN_d' orbT. }
    + move: IN_d; rewrite inE => /orP [/eqP ? | IN_d]; [congruence|].
      move: CC => /(_ d a) [| // | d' [IN_d' IN'_a]].
      * by rewrite in_rem_all in IN_d; move: IN_d => /andP [].
      * { have [? | NEQ'] := altP (d' =P c).
          - by subst; exists c'; rewrite inE -ADDR eq_refl /=.
          - by exists d'; rewrite inE in_rem_all NEQ' IN_d' orbT. }
Qed.

Lemma add_to_compartment_component_good : forall addr rd wr MM,
  (forall X c, address_space c = address_space (wr X c)) ->
  (forall X c, jump_targets (wr X c) = jump_targets c \/
               jump_targets (wr X c) = X /\ rd c = jump_targets c) ->
  (forall X c, store_targets (wr X c) = store_targets c \/
               store_targets (wr X c) = X /\ rd c = store_targets c) ->
  good_syscall (Syscall addr (add_to_compartment_component rd wr)) MM.
Proof.
  clear S; rewrite /good_syscall /= => _ rd wr MM ADDR eqJ eqS.
  destruct (good_state MM) eqn:GOOD; [simpl|reflexivity].
  destruct (in_compartment_opt _ _) as [c_sys0|] eqn:ICO_pc;
    [simpl|reflexivity].
  destruct (syscall_address_space _ _) eqn:SAS; [simpl|reflexivity].
  destruct MM as [pc R M C sk c];
    unfold good_state, add_to_compartment_component;
    rewrite (lock in_compartment_opt);
    simpl in *.
  generalize GOOD; rewrite /good_state /= => /and4P [PREV GOODS SS SP].
  destruct (permitted_now_in _ _ _ _) as [c_sys|] eqn:PNI; [simpl|reflexivity].
  destruct (c != c_sys)               eqn:NEQ;             [simpl|reflexivity].
  destruct (get R syscall_arg1)       as [p|];             [simpl|reflexivity].
  destruct (p \in _)                  eqn:ELEM;            [simpl|reflexivity].
  destruct (get R ra)                 as [pc'|];           [simpl|reflexivity].
  rewrite <-(lock in_compartment_opt);
    destruct (in_compartment_opt _ pc') as [c_next|] eqn:ICO_pc';
    simpl; [|reflexivity].
  destruct (_ == c_next) eqn:EQ; move/eqP in EQ; simpl;
    [subst c_next | reflexivity].
  destruct (pc' \in _) eqn:ELEM_pc'; simpl; [|reflexivity].
  assert (c_sys0 = c_sys) by
    (apply permitted_now_in__in_compartment_opt in PNI; congruence);
    subst c_sys0.
  apply in_compartment_opt_correct in ICO_pc; auto.
  andb_true_split.
  - rewrite inE.
    have -> : c_sys \in rem_all c C. {
      rewrite in_rem_all eq_sym; apply/andP; split; first by [].
      eapply in_compartment_element; eassumption.
    }
    by rewrite orbT.
  - destruct c as [A J S]; simpl in *.
    rewrite inE in ELEM.
    by apply good_compartments_preserved_for_add_to_compartment_component;
       try (by try apply/inP);
       apply/subsetP => a; rewrite inE /=;
       [move: (eqJ) => eqX | move: (eqS) => eqX];
       case: (eqX (p |: rd <<A,J,S>>) <<A,J,S>>) => /= [-> | [-> eqRd]];
       first [ move=> ->; rewrite orbT
             | move: ELEM;
               rewrite inE in_set1 eqRd => ELEM /orP [/eqP -> // | ->];
               rewrite orbT ].
  - rewrite (user_address_space_same M _ c); auto.
    rewrite (syscall_address_space_same M _ c); auto.
    unfold is_true in SS; rewrite ->forallb_forall in SS.
    by apply/SS/inP.
  - rewrite rem_all_is_delete; replace @all with @forallb by reflexivity;
      auto using delete_preserves_forallb.
  - move/id in SP.
    rewrite /syscalls_present /table /is_true in SP *.
    rewrite ->forallb_forall in SP; rewrite ->forallb_forall.
    intros sc IN_sc; specialize (SP sc IN_sc); cbv [compose] in *.
    destruct sc as [sc sc_fn]; cbv [address] in *; clear IN_sc sc_fn.
    simpl; rewrite <-ADDR.
    destruct (in_compartment_opt C sc) as [c_sc|] eqn:ICO;
      [clear SP | discriminate].
    move: (ICO) => /in_compartment_opt_correct/andP [IN_c_sc IN_sc].
    have [<- | NEQ_sc] := altP (c_sc =P c).
    + by rewrite IN_sc.
    + case: (sc \in address_space c) => //.
      have IC' : rem_all c C ⊢ sc ∈ c_sc
        by apply/andP; rewrite in_rem_all; split; first apply/andP.
      apply in_compartment_opt_sound in IC'; auto.
      by rewrite IC'.
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
Proof. rewrite /table /= => MM; apply/and4P; split; auto. Qed.
(*Global*) Hint Resolve good_syscalls_b.

Corollary good_syscalls : forall MM sc,
  In sc table -> good_syscall sc MM.
Proof. intros MM; apply forallb_forall. apply good_syscalls_b. Qed.
(*Global*) Hint Resolve good_syscalls.

Lemma get_syscall_in : forall addr sc,
  get_syscall addr ?= sc -> In sc table.
Proof.
  unfold get_syscall; intros addr sc GS; apply find_in in GS; tauto.
Qed.
(*Global*) Hint Resolve get_syscall_in.

Lemma get_syscall_good : forall addr sc,
  get_syscall addr ?= sc -> forall MM, good_syscall sc MM.
Proof. move=> addr sc GS; apply get_syscall_in in GS; auto. Qed.
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
    move: ICO => /andP [/inP IN IN'].
  assert (SS : syscalls_separated M C) by eauto; simpl in *.
  move: SS => /forallb_forall/(_ c IN) /= SS.
  rewrite SAS orb_false_r /user_address_space /= in SS.
  move/forallP/(_ (address sc))/implyP/(_ IN') in SS.
  by rewrite INST in SS.
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
  - rewrite <-EQ; apply SP; auto.
Qed.

Lemma previous_compartment : forall `(STEP : step MM MM'),
  good_state MM -> (* This hypothesis only needed for syscalls *)
  previous MM' \in compartments MM'.
Proof.
  intros MM MM' STEP GOOD; destruct STEP; try solve [
    subst; simpl in *;
    match goal with
      | STEP : permitted_now_in ?C ?sk ?prev ?pc ?= ?c |- context[?c \in ?C] =>
        apply permitted_now_in_spec in STEP; last (by eauto 2);
        by case: STEP => [/andP []] *
    end
  ].
  (* Syscalls *)
  assert (GOOD' : good_state MM') by
   (apply syscall_step_preserves_good with MM sc; subst; assumption);
   auto.
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
  - by rewrite IC.
  - by apply good_compartments__non_overlapping, good_state__good_compartments.
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
      by rewrite inE in VALID; replace c0 with c in * by eauto 3; apply/orP.
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
  Hint Resolve disjoint_comp_sym.
  Hint Resolve good_no_duplicates.
  Hint Resolve non_overlapping_subset.
  Hint Resolve non_overlapping_tail.
  Hint Resolve good_compartments__in2_disjoint.
  Hint Resolve non_overlapping_rem.
  Hint Resolve non_overlapping_rem'.
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
  Hint Resolve good_syscalls.
  Hint Resolve get_syscall_in.
  Hint Resolve get_syscall_good.
  Hint Resolve previous_compartment.
  Hint Resolve good_compartments_preserved.
  Hint Resolve good_state_preserved.
(* End globalized hint section *)
End Hints.

End Abs.
