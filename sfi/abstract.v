Require Import List Arith Sorted Bool.
Require Import Coq.Classes.SetoidDec.
Require Import lib.utils concrete.common lib.ordered list_utils set_utils.

Import DoNotation.

Set Implicit Arguments.

(* This abstract machine corresponds to the abstract machine section in
 * verif/sfi/sfi.pdf. *)

Import ListNotations.

Module Abstract.

Open Scope bool_scope.
Open Scope Z_scope.

Section WithClasses.

Context (t : machine_types).
Context {ops : machine_ops t}.
Existing Instance eq_word.
Existing Instance ord_word.

Notation W0 := (Z_to_word 0).
Notation W1 := (Z_to_word 1).
Open Scope word_scope.

Local Notation word  := (word t).
Local Notation value := word.

(* I want to use S as a variable. *)
Let S := Datatypes.S.
Local Notation Suc := Datatypes.S.

(**** RANGE ****)
(* TODO abstract and reify *)
Require Import ZArith.

Hypothesis word_to_Z_succ : forall x y,
  x < y -> word_to_Z (x + W1) = (word_to_Z x + 1)%Z.

Hypothesis word_to_Z_compare : forall x y,
  x <=> y = (word_to_Z x ?= word_to_Z y)%Z.

Theorem word_succ_le_lt : forall x y, x < y -> x + W1 <= y.
Proof.
 intros.
 unfold le; rewrite word_to_Z_compare;
   fold (Zle (word_to_Z (x + W1)%w) (word_to_Z y)).
 erewrite word_to_Z_succ by eassumption.
 unfold lt in *; rewrite word_to_Z_compare in *;
   fold (Zlt (word_to_Z x) (word_to_Z y)) in *;
   omega.
Qed.

Theorem word_succ_ltb_bounded : forall x y,
  x <? y = true -> x <? x + W1 = true.
Proof.
  intros x y; repeat rewrite ltb_lt; intros LT.
  unfold lt; rewrite word_to_Z_compare;
    fold (Zlt (word_to_Z x) (word_to_Z (x + W1))).
  erewrite word_to_Z_succ by eassumption; omega.
Qed.

Fixpoint range' (meas : nat) (l h : word) : list word :=
  match meas , l <=> h with
    | O         , _  => []
    | Suc meas' , Lt => l :: range' meas' (l + W1) h
    | Suc meas' , Eq => [l]
    | Suc meas' , Gt => []
  end.

Theorem range'_set : forall meas l h,
  is_set (range' meas l h) = true.
Proof.
  induction meas as [|meas]; simpl; [reflexivity|].
  intros l h; destruct (l <=> h) eqn:CMP; try reflexivity.
  simpl; rewrite IHmeas.
  destruct meas; simpl; [reflexivity|].
  destruct (l + W1 <=> h) eqn:CMP';
    try solve [ reflexivity
          | rewrite andb_true_r; eapply word_succ_ltb_bounded;
            (* I had to split the `eapply' up; I don't know why. *)
            eapply ltb_lt,CMP ].
Qed.

Theorem range'_elts_ok : forall meas l h e,
  In e (range' meas l h) -> l <= e <= h.
Proof.
  induction meas as [|meas]; [inversion 1|].
  simpl; intros until 0; intros IN.
  destruct (l <=> h) eqn:CMP; simpl in *.
  - apply compare_eq in CMP; destruct IN as [EQ|[]];
      repeat progress subst; auto 2 with ordered.
  - destruct IN as [EQ | IN]; subst; auto with ordered.
    apply IHmeas in IN; destruct IN as [LT LE].
    assert (l < l + W1) by
      (apply ltb_lt; apply word_succ_ltb_bounded with h; apply ltb_lt;
       assumption).
    split; eauto with ordered.
  - inversion IN.
Qed.

Definition range (l h : word) :=
  range' (Z.to_nat ((word_to_Z h - word_to_Z l) + 1)%Z) l h.

Corollary range_set : forall l h, is_set (range l h) = true.
Proof. intros until 0; apply range'_set. Qed.
Hint Resolve range_set.

Corollary range_elts_ok : forall l h e,
  In e (range l h) -> l <= e <= h.
Proof. intros until 0; apply range'_elts_ok. Qed.

Theorem range_elts_all : forall l h e,
  l <= e <= h -> In e (range l h).
Proof.
  unfold range; intros l h e [LE EH];
    assert (LH : l <= h) by eauto with ordered.
  remember (Z.to_nat ((word_to_Z h - word_to_Z l) + 1)%Z) as meas eqn:meas_def'.
  assert (meas_def : meas = S (Z.to_nat (word_to_Z h - word_to_Z l))). {
    rewrite Z2Nat.inj_add in meas_def'; try solve [vm_compute; inversion 1].
    - rewrite plus_comm in meas_def'; simpl in meas_def'; exact meas_def'.
    - apply Z.le_0_sub; unfold Zle; rewrite <- word_to_Z_compare; exact LH.
  }
  clear meas_def'; gdep e; gdep h; gdep l; induction meas; intros;
    simpl in *; inversion meas_def; subst; clear meas_def.
  destruct (l <=> h) eqn:CMP.
  - apply compare_eq in CMP; apply le__lt_or_eq in EH; apply le__lt_or_eq in LE;
      subst; destruct EH,LE; auto with ordered.
    elim (lt_asym h e); assumption.
  - simpl. apply le__lt_or_eq in LE; destruct LE as [LE | LE]; auto.
    right. apply IHmeas; auto using word_succ_le_lt.
    erewrite word_to_Z_succ by eassumption.
    replace (word_to_Z h - (word_to_Z l + 1))%Z
       with (word_to_Z h - word_to_Z l - 1)%Z
         by omega.
    rewrite <- Z2Nat.inj_succ.
    + f_equal; omega.
    + rewrite Z.sub_1_r; apply Zlt_0_le_0_pred,Z.lt_0_sub.
      unfold Zlt; rewrite <- word_to_Z_compare; exact CMP.
  - contradiction.
Qed.

Corollary range_elts : forall l h e,
  In e (range l h) <-> l <= e <= h.
Proof. split; [apply range_elts_ok | apply range_elts_all]. Qed.

Corollary range_empty : forall l h,
  range l h = [] <-> l > h.
Proof.
  intros; rewrite nil_iff_not_in; split.
  - intros NOT_IN; apply gt_not_le; intros LE.
    apply NOT_IN with l, range_elts; auto with ordered.
  - intros GT e IN. apply range_elts in IN.
    destruct IN; assert (l <= h) by eauto 2 with ordered; auto.
Qed.
(***** END RANGE *****)

Implicit Type pc : value.

Class abstract_params := {
  memory    : Type;
  registers : Type;
  
  get_mem : memory -> value -> option value;
  upd_mem : memory -> value -> value -> option memory;
  
  get_reg : registers -> reg t -> option value;
  upd_reg : registers -> reg t -> value -> option registers
}.

Class params_spec (ap : abstract_params) :=
  { mem_axioms : PartMaps.axioms get_mem upd_mem
  ; reg_axioms : PartMaps.axioms get_reg upd_reg }.

Context {ap : abstract_params}.

Implicit Type M : memory.
Implicit Type R : registers.
Implicit Type r rsrc rdest rpsrc rpdest rtgt : reg t.

(* BCP: Can we change `shared_memory' to `writable_memory', and disallow writes
   to `address_space'?  [TODO] *)
Record compartment := mk_compartment { address_space : list value
                                     ; jump_targets  : list value
                                     ; shared_memory : list value }.
Notation "<< A , J , S >>" := (mk_compartment A J S) (format "<< A , J , S >>").
Implicit Type c     : compartment.
Implicit Type A J S : list value.
Implicit Type C     : list compartment.

Instance compartment_eqdec : EqDec (eq_setoid compartment).
Proof.
  cbv; intros c1 c2; fold (c1 <> c2); decide equality; apply list_eqdec.
Defined.

Definition good_compartment (c : compartment) : bool :=
  is_set (address_space c) &&
  is_set (jump_targets  c) &&
  is_set (shared_memory c).

Definition non_overlapping (c1 c2 : compartment) : bool :=
  match set_intersection (address_space c1) (address_space c2),
        (address_space c1), (address_space c2)
  with
    | [], [], [] => false
    | [], _,  _  => true
    | _,  _,  _  => false
  end.

Definition non_overlapping_list : list compartment -> bool :=
  all_tail_pairs_b non_overlapping.

(* BCP: Do we need this?  Can we get away with just having all user memory
   inside a compartment at all times?  [TODO] *)
Definition contained_compartments (C : list compartment) : bool :=
  subset (concat (map jump_targets C) ++ concat (map shared_memory C))
         (concat (map address_space C)).

Definition good_compartments (C : list compartment) : bool :=
  forallb good_compartment C &&
  non_overlapping_list     C &&
  contained_compartments   C.

Reserved Notation "C ⊢ p ∈ c" (at level 70).
Inductive in_compartment (p : value) : list compartment -> compartment -> Prop :=
| ic_here  : forall C A J S, In p A     -> <<A,J,S>> :: C ⊢ p ∈ <<A,J,S>>
| ic_there : forall C c c',  C ⊢ p ∈ c' -> c :: C ⊢ p ∈ c'
where "C ⊢ p ∈ c" := (in_compartment p C c).
Notation "C ⊢ p1 , p2 , .. , pk ∈ c" :=
  (and .. (and (C ⊢ p1 ∈ c) (C ⊢ p2 ∈ c)) .. (C ⊢ pk ∈ c))
  (at level 70).
Hint Constructors in_compartment.

Fixpoint in_compartment_opt (C : list compartment)
                            (p : value) : option compartment :=
  match C with
    | []     => None
    | c :: C => if existsb (equiv_decb p) (address_space c)
                then Some c
                else in_compartment_opt C p
  end.

Record state := mk_state { pc           : value
                         ; regs         : registers
                         ; mem          : memory
                         ; compartments : list compartment  }.

Definition good_state (MM : state) : bool :=
  is_some (in_compartment_opt (compartments MM) (pc MM)) &&
  good_compartments (compartments MM).

Record syscall := Syscall { address   : word
                          ; semantics : state -> option state }.

Definition good_syscall (sc : syscall) (MM : state) : bool :=
  if good_state MM
  then match semantics sc MM with
         | Some MM' => good_state MM'
         | None     => true
       end
  else true.

Class isolate_params := {
  (* The registers ISOLATE reads from. *)
  riso1 : reg t; riso2 : reg t; riso3 : reg t; riso4 : reg t;

  (* The location of ISOLATE *)
  isolate_addr : word
}.
Context {IP : isolate_params}.

Notation "'do' 'guard' cond ; rest" :=
  (if cond then rest else None)
  (at level 200, cond at level 100, rest at level 200).

Definition isolate_create_set (M : memory)
                              (base size : value) : option (list value) :=
  let pre_set := map (fun p : value => get_mem M (p + W1 + base))
                     (range W0 (size - W1)) in
  do guard forallb is_some pre_set;
  Some (to_set (cat_somes pre_set)).

(* From Greg: An objection to SFI could be "but we have page table tricks for
   doing the same things".  So let's make the new address space similarly
   disjoint.  (Except with sets of pairs.)  [TODO] *)
Definition isolate_fn (MM : state) : option state :=
  let '(mk_state pc R M C) := MM in
  do c      <- in_compartment_opt C pc;
  do al     <- get_reg R riso1;
  do ah     <- get_reg R riso2;
  do jt     <- get_reg R riso3;
  do sm     <- get_reg R riso4;
  do jtsz   <- get_mem M jt;
  do smsz   <- get_mem M sm;
  do guard al <=? ah;
  let '<<A,J,S>> := c in
  let A' := range al ah in
  do guard subset A' A;
  do J' <- isolate_create_set M jt jtsz;
  do guard subset J' (A ++ J);
  do S' <- isolate_create_set M sm smsz;
  do guard subset S' (A ++ S);
  let c_upd := << set_difference A  A'
                , insert_unique  al J
                , S >> in
  let c'    := <<A',J',S'>> in
  let C'    := c_upd :: c' :: delete c C in
  do guard existsb (equiv_decb (pc + W1)) (address_space c_upd);
  Some (mk_state (pc + W1) R M C').

Definition isolate :=
  {| address   := isolate_addr
   ; semantics := isolate_fn |}.

Variable othercalls : list syscall.
Let table := isolate :: othercalls.

Definition get_syscall (addr : value) : option syscall :=
  find (fun sc => address sc ==b addr) table.

Notation simple_step C pc c := (C ⊢ pc, pc + W1 ∈ c).

Implicit Type pc_val : value.

Inductive step : state -> state -> Prop :=
| step_nop :     forall pc R M C c pc_val,
                 forall (PC    : get_mem      M pc   = Some pc_val),
                 forall (INST  : decode_instr pc_val = Some (Nop _)),
                 forall (STEP  : simple_step C pc c),
                 step (mk_state pc R M C) (mk_state (pc + W1) R M C)

| step_const :   forall pc R M C c pc_val x rdest R',
                 forall (PC    : get_mem      M pc   = Some pc_val),
                 forall (INST  : decode_instr pc_val = Some (Const _ x rdest)),
                 forall (STEP  : simple_step C pc c),
                 forall (UPD   : upd_reg R rdest (imm_to_word x) = Some R'),
                 step (mk_state pc R M C) (mk_state (pc + W1) R' M C)

| step_mov   :   forall pc R M C c pc_val rsrc rdest x R',
                 forall (PC    : get_mem      M pc   = Some pc_val),
                 forall (INST  : decode_instr pc_val = Some (Mov _ rsrc rdest)),
                 forall (STEP  : simple_step C pc c),
                 forall (GET   : get_reg R rsrc = Some x),
                 forall (UPD   : upd_reg R rdest x = Some R'),
                 step (mk_state pc R M C) (mk_state (pc + W1) R' M C)

| step_binop :   forall pc R M C c pc_val op rsrc1 rsrc2 rdest x1 x2 R',
                 forall (PC    : get_mem      M pc   = Some pc_val),
                 forall (INST  : decode_instr pc_val = Some (Binop _ op rsrc1 rsrc2 rdest)),
                 forall (STEP  : simple_step C pc c),
                 forall (GETR1 : get_reg R rsrc1 = Some x1),
                 forall (GETR2 : get_reg R rsrc2 = Some x2),
                 forall (UPDR  : upd_reg R rdest (binop_denote op x1 x2) = Some R'),
                 step (mk_state pc R M C) (mk_state (pc + W1) R' M C)

| step_load  :   forall pc R M C c pc_val rpsrc rdest p x R',
                 forall (PC    : get_mem      M pc   = Some pc_val),
                 forall (INST  : decode_instr pc_val = Some (Load _ rpsrc rdest)),
                 forall (STEP  : simple_step C pc c),
                 forall (GETR  : get_reg R rpsrc = Some p),
                 forall (GETM  : get_mem M p     = Some x),
                 forall (UPDR  : upd_reg R rdest x = Some R'),
                 step (mk_state pc R M C) (mk_state (pc + W1) R' M C)

| step_store :   forall pc R M C c pc_val rsrc rpdest x p M',
                 forall (PC    : get_mem      M pc   = Some pc_val),
                 forall (INST  : decode_instr pc_val = Some (Store _ rsrc rpdest)),
                 forall (STEP  : simple_step C pc c),
                 forall (GETRS : get_reg R rsrc   = Some x),
                 forall (GETRD : get_reg R rpdest = Some p),
                 forall (VALID : In p (address_space c ++ shared_memory c)),
                 forall (UPDR  : upd_mem M p x = Some M'),
                 step (mk_state pc R M C) (mk_state (pc + W1) R M' C)

| step_jump  :   forall pc R M C c pc_val rtgt pc',
                 forall (PC    : get_mem      M pc   = Some pc_val),
                 forall (INST  : decode_instr pc_val = Some (Jump _ rtgt)),
                 forall (IN_C  : C ⊢ pc ∈ c),
                 forall (GETR  : get_reg R rtgt = Some pc'),
                 forall (VALID : In pc' (address_space c ++ jump_targets c)),
                 step (mk_state pc R M C) (mk_state pc' R M C)

| step_bnz   :   forall pc R M C c pc_val rsrc x b,
                 forall (PC    : get_mem      M pc   = Some pc_val),
                 forall (INST  : decode_instr pc_val = Some (Bnz _ rsrc x)),
                 forall (GETR  : get_reg R rsrc = Some b),
                 let pc' := pc + (if b == W0 then W1 else imm_to_word x) in
                 forall (STEP  : C ⊢ pc,pc' ∈ c),
                 step (mk_state pc R M C) (mk_state pc' R M C)

(* We make JAL inter-compartmental, like JUMP, but things must be set up so that
 * the return address is callable by the destination compartment.  However, see
 * [Note Fancy JAL] below. *)
| step_jal   :   forall pc R M C c pc_val rtgt pc' R',
                 forall (PC    : get_mem      M pc   = Some pc_val),
                 forall (INST  : decode_instr pc_val = Some (Jal _ rtgt)),
                 forall (IN_C  : C ⊢ pc ∈ c),
                 forall (GETR  : get_reg R rtgt = Some pc'),
                 forall (USER  : get_syscall pc' = None),
                 forall (VALID : In pc' (address_space c ++ jump_targets c)),
                 forall (UPDR  : upd_reg R ra (pc + W1) = Some R'),
                 step (mk_state pc R M C) (mk_state pc' R' M C)

| step_syscall : forall pc R M C c pc_val rtgt sc_addr sc MM',
                 forall (PC    : get_mem      M pc   = Some pc_val),
                 forall (INST  : decode_instr pc_val = Some (Jal _ rtgt)),
                 forall (IN_C  : C ⊢ pc ∈ c),
                 forall (GETR  : get_reg R rtgt = Some sc_addr),
                 forall (GETSC : get_syscall sc_addr = Some sc),
                 forall (CALL  : semantics sc (mk_state pc R M C) = Some MM'),
                 step (mk_state pc R M C) MM'.

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

(*** Proofs for `in_compartment' and `in_compartment_opt' ***)

(* Ltac *)

Ltac destruct_good_compartment_hyp_impl name GOOD :=
  (* Copy the GOOD hypothesis so it can be used by `auto' and friends later. *)
  match type of GOOD with
    | good_compartment ?c = true =>
      let TEMP_c   := fresh "TEMP_"   name in
      let SET_AS_c := fresh "SET_AS_" name in
      let SET_JT_c := fresh "SET_JT_" name in
      let SET_SM_c := fresh "SET_SM_" name in
      assert (TEMP_c : good_compartment c = true) by exact GOOD;
      unfold good_compartment in TEMP_c; repeat rewrite andb_true_iff in TEMP_c;
      destruct TEMP_c as [[SET_AS_c SET_JT_c] SET_SM_c]
    | _ => fail 1 GOOD "is not a `good_compartment' assertion"
  end.

Ltac destruct_good_compartment_hyp GOOD :=
  destruct_good_compartment_hyp_impl GOOD GOOD.

Ltac destruct_good_compartment_hyp_smart_name_impl c GOOD :=
  (* Use `c' for the name if we can; otherwise, use `GOOD'.  Useful if the
     compartment `c' might or might not be a plain identifier. *)
  first [ destruct_good_compartment_hyp_impl c    GOOD
        | destruct_good_compartment_hyp_impl GOOD GOOD ].

Ltac destruct_one_good_compartment_impl c :=
  match goal with
    | [GOOD : context[good_compartment c] |- _] =>
      destruct_good_compartment_hyp_smart_name_impl c GOOD
    | _ => fail 3 c "is not a `good_compartment'"
  end.

Ltac destruct_good_compartments_cc_impl k c :=
  (* `match c with ... end' breaks violently when `c' is an out-of-scope
     identifier (it's treated as an intro pattern, which can't be matched on).
     Thus, we hide it inside a `match goal with ... end', so it fails over to
     the next case instead of exploding.  (We can't use `try' because we need to
     be tail recursive.) *)
  match goal with
    | _ => match c with
             | False => k
             | _     => destruct_good_compartments_cc_impl
                          ltac:(k; destruct_one_good_compartment_impl c)
           end
    | _ => fail 1 c "is not a known `good_compartment'"
  end.

(* Usage: `destruct_good_compartments c1 c2 ... cN False'.  I can't get Coq's
   tactic notations to reproduce the `c1 ... cN' alone syntax. *)
Ltac destruct_good_compartments :=
  destruct_good_compartments_cc_impl idtac.

Ltac destruct_good_compartment c := destruct_good_compartments c False.

(* Can't just use `repeat match goal with ... end', since the
   `destruct_good_compartment_*' tactics don't remove the original
   hypothesis.  This reorders the hypotheses, but I didn't see a better option.
   It will fail on dependent `good_compartment' hypothesis, but don't do that
   then. *)
Ltac destruct_all_good_compartments :=
  match goal with
    | [GOOD : context[good_compartment ?c] |- _] =>
      destruct_good_compartment_hyp_smart_name_impl c GOOD;
      revert GOOD;
      try destruct_all_good_compartments;
      intro GOOD
  end.

Ltac assert_good_compartment name c :=
  let GOOD_c   := fresh "GOOD_"   name in
  assert (GOOD_c : good_compartment c = true);
  [ (* Let the user prove that `good_compartment c = true'. *)
  | destruct_good_compartment c ].

(* The `as' clauses have to come first or we get parse errors later. *)

Tactic Notation "assert" "as" ident(name) "good_compartment" constr(c) :=
  assert_good_compartment name c.

Tactic Notation "assert" "good_compartment" ident(c) :=
  assert as c good_compartment c.

Tactic Notation (at level 0) "assert" "as" ident(name)
                             "good_compartment" constr(c)
                             "by" tactic1(t) :=
  assert as name good_compartment c; [solve [t]|].

Tactic Notation (at level 0) "assert" "good_compartment" ident(c)
                             "by" tactic1(t) :=
  assert as c good_compartment c by t.

Theorem in_compartment_opt_correct : forall C p c,
  in_compartment_opt C p = Some c -> C ⊢ p ∈ c.
Proof.
  clear.
  induction C as [|ch C]; [inversion 1|].
  intros p c ICO; simpl in *.
  destruct (existsb _ _) eqn:EX; auto.
  inversion ICO; subst; apply in_existsb_equiv_decb in EX; destruct c; auto.
Qed.
Hint Resolve in_compartment_opt.

Theorem in_compartment_opt_missing_correct : forall C p,
  in_compartment_opt C p = None -> forall c, ~ C ⊢ p ∈ c.
Proof.
  clear.
  induction C as [|ch C]; intros p ICO c IC; [inversion IC|]; simpl in *.
  destruct (existsb _ _) eqn:EX; try congruence.
  inversion IC as [C' A J S IN|]; subst; [|eapply IHC; eassumption].
  apply existsb_equiv_decb_in in IN; simpl in *; congruence.
Qed.
Hint Resolve in_compartment_opt_missing_correct.

Theorem in_compartment_opt_present : forall C p c,
  C ⊢ p ∈ c -> exists c', in_compartment_opt C p = Some c'.
Proof.
  clear.
  induction 1 as [C A J S IN | C ch c IC].
  - exists <<A,J,S>>; simpl; rewrite existsb_equiv_decb_in; auto.
  - simpl; destruct (existsb _ _); eauto.
Qed.
Hint Resolve in_compartment_opt_present.

Corollary in_compartment_opt_is_some : forall C p c,
  C ⊢ p ∈ c -> is_some (in_compartment_opt C p) = true.
Proof.
  intros C p c IC; apply in_compartment_opt_present in IC.
  destruct IC as [c' ICO]; rewrite ICO; reflexivity.
Qed.
Hint Resolve in_compartment_opt_is_some.

Theorem in_compartment_element : forall C p c,
  C ⊢ p ∈ c ->
  In c C.
Proof. induction 1; auto. Qed.
Hint Resolve in_compartment_element.

Theorem in_compartment__in_address_space : forall C p c,
  C ⊢ p ∈ c -> In p (address_space c).
Proof. induction C; inversion 1; subst; auto. Qed.
Hint Resolve in_compartment__in_address_space.

Theorem in_compartment_spec : forall C p c,
  C ⊢ p ∈ c <-> In c C /\ In p (address_space c).
Proof.
  clear; split; eauto.
  intros [IN_c IN_p].
  induction C as [|ch C].
  - inversion IN_c.
  - inversion IN_c as [EQ | IN_c'].
    + subst; destruct c; auto.
    + auto.
Qed.

Theorem in_same_compartment : forall C p p' c,
  C ⊢ p ∈ c ->
  In p' (address_space c) ->
  C ⊢ p' ∈ c.
Proof. induction 1; auto. Qed.
Hint Resolve in_same_compartment.

Theorem unique_here_not_there : forall C p c,
  ~ In c C       ->
  c :: C ⊢ p ∈ c ->
  ~ C ⊢ p ∈ c.
Proof.
  intros until 0; intros OUT HERE THERE.
  apply in_compartment_element in HERE; apply in_compartment_element in THERE.
  assert (IN2 : In2 c c (c :: C)) by auto.
  inversion IN2; subst; auto.
Qed.
Hint Resolve unique_here_not_there.

Theorem unique_must_be_here : forall C p c c',
  ~ In c' C        ->
  c :: C ⊢ p ∈ c' ->
  c = c'.
Proof.
  clear. intros until 0; intros OUT IC.
  inversion IC; subst; auto.
  contradict OUT; eauto 2.
Qed.
Hint Resolve unique_must_be_here.

Theorem in_same_compartment__overlapping : forall C p c1 c2,
  C ⊢ p ∈ c1 ->
  C ⊢ p ∈ c2 ->
  non_overlapping c1 c2 = false.
Proof.
  intros until 0; intros IN1 IN2;
    apply in_compartment__in_address_space in IN1;
    apply in_compartment__in_address_space in IN2.
  unfold non_overlapping.
  assert (IN : In p (set_intersection (address_space c1) (address_space c2))) by
    (apply set_intersection_spec; auto).
  destruct (set_intersection (address_space c1) (address_space c2)).
  - inversion IN.
  - reflexivity.
Qed.
Hint Resolve in_same_compartment__overlapping.

(*** Proofs for `non_overlapping' ***)

Theorem non_overlapping_irrefl : forall c,
  non_overlapping c c = false.
Proof.
  intros; unfold non_overlapping; rewrite set_intersection_self_id.
  destruct (address_space c); reflexivity.
Qed.
Hint Resolve non_overlapping_irrefl.

Theorem non_overlapping_comm : forall c1 c2,
  good_compartment c1 = true -> good_compartment c2 = true ->
  non_overlapping c1 c2 = non_overlapping c2 c1.
Proof.
  unfold non_overlapping; intros; rewrite set_intersection_comm;
  destruct c1 as [[|a1 A1] J1 S1], c2 as [[|a2 A2] J2 S2]; auto;
  destruct_all_good_compartments; auto.
Qed.
Hint Resolve non_overlapping_comm.

Theorem non_overlapping_in2_comm : forall c1 c2 C,
  forallb good_compartment C = true ->
  In2 c1 c2 C ->
  non_overlapping c1 c2 = non_overlapping c2 c1.
Proof.
  intros c1 c2 C GOOD IN2.
  apply in2_in in IN2; destruct IN2.
  rewrite forallb_forall in GOOD; auto.
Qed.
Hint Resolve non_overlapping_in2_comm.

Theorem non_overlapping_subcompartment : forall c1 c2 c3,
  good_compartment c1 = true -> good_compartment c2 = true ->
  nonempty (address_space c1) = true ->
  (forall a, In a (address_space c1) -> In a (address_space c2)) ->
  non_overlapping c2 c3 = true ->
  non_overlapping c1 c3 = true.
Proof.
  intros [A1 J1 S1] [A2 J2 S2] [A3 J3 S3] GOOD1 GOOD2 NONEMPTY SUBSET NO2;
    destruct_all_good_compartments; unfold non_overlapping in *; simpl in *.
  assert (SUBSET' : forall a, In a (set_intersection A1 A3) ->
                              In a (set_intersection A2 A3)) by
    (intros a; specialize SUBSET with a;
     repeat rewrite set_intersection_spec; tauto).
  destruct (set_intersection A2 A3).
  - destruct (set_intersection A1 A3).
    + destruct A1; [inversion NONEMPTY | reflexivity].
    + not_subset_cons_nil.
  - inversion NO2.
Qed.
Hint Resolve non_overlapping_subcompartment.

(*** Proofs for `contained_compartments' ***)

Theorem contained_compartments_spec : forall C,
  contained_compartments C = true <->
  (forall c a, In c C -> (In a (jump_targets c) \/ In a (shared_memory c)) ->
               exists c', In c' C /\ In a (address_space c')).
Proof.
  clear S; intros; unfold contained_compartments; rewrite subset_spec; split.
  - intros SUBSET c a IN_c IN_a.
    specialize SUBSET with a;
      rewrite in_app_iff in SUBSET; repeat rewrite concat_in in SUBSET.
    destruct SUBSET as [A [IN_A IN_a_A]].
    + destruct IN_a;
        [left; exists (jump_targets c) | right; exists (shared_memory c)];
        (split; [apply in_map_iff; eauto | assumption]).
    + apply in_map_iff in IN_A; destruct IN_A as [c' [EQ IN_c']].
      exists c'; subst; tauto.
  - intros SPEC a IN_app.
    apply in_app_iff in IN_app.
    rewrite concat_in; repeat rewrite concat_in in IN_app.
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
Qed.

(*** Proofs for `good_compartments' ***)

Local Ltac good_compartments_trivial :=
  unfold good_compartments; intros C GOOD;
  repeat rewrite andb_true_iff in GOOD;
  tauto.

(* For `auto' *)
Lemma good_compartments__all_good_compartment : forall C,
  good_compartments C = true -> forallb good_compartment C = true.
Proof. good_compartments_trivial. Qed.
Hint Resolve good_compartments__all_good_compartment.

(* For `auto' *)
Lemma good_compartments__non_overlapping_list : forall C,
  good_compartments C = true -> non_overlapping_list C = true.
Proof. good_compartments_trivial. Qed.
Hint Resolve good_compartments__non_overlapping_list.

(* For `auto' *)
Lemma good_compartments__contained_compartments : forall C,
  good_compartments C = true -> contained_compartments C = true.
Proof. good_compartments_trivial. Qed.
Hint Resolve good_compartments__contained_compartments.

Lemma good_compartment_in : forall c C,
  good_compartments C = true ->
  In c C ->
  good_compartment c = true.
Proof.
  intros c C GOOD IN;
    eapply good_compartments__all_good_compartment, forallb_forall in GOOD;
    eassumption.
Qed.
Hint Resolve good_compartment_in.
  
Theorem good_no_duplicates : forall C,
  good_compartments C = true ->
  NoDup C.
Proof.
  intros C GOOD;
    unfold good_compartments, non_overlapping_list in GOOD;
    repeat rewrite andb_true_iff in GOOD; rewrite <- all_pairs_in2_comm in GOOD;
    repeat invh and; eauto 2.
Qed.
Hint Resolve good_no_duplicates.

(*** Proofs for `non_overlapping_list' ***)

Theorem non_overlapping_subset : forall C1 C2,
  NoDup C1 ->
  forallb good_compartment C2 = true ->
  (forall c, In c C1 -> In c C2) ->
  non_overlapping_list C2 = true ->
  non_overlapping_list C1 = true.
Proof.
  unfold non_overlapping_list; intros C1 C2 SUBSET NO_DUP GOOD NOL.
  apply all_pairs__all_tail_pairs.
  rewrite <- all_pairs_in2_comm in NOL; eauto 2.
Qed.
Hint Resolve non_overlapping_subset.

Theorem non_overlapping_tail : forall c C,
  non_overlapping_list (c :: C) = true -> non_overlapping_list C = true.
Proof.
  unfold non_overlapping_list; intros c C NOL;
  rewrite all_tail_pairs_tail, andb_true_iff in NOL; tauto.
Qed.
Hint Resolve non_overlapping_tail.

Theorem non_overlapping_list_spec : forall C,
  forallb good_compartment C = true ->
  (non_overlapping_list C = true <-> (forall c1 c2,
                                        In2 c1 c2 C ->
                                        non_overlapping c1 c2 = true)).
Proof.
  intros C GOOD. unfold non_overlapping_list.
  rewrite <- all_pairs_in2_comm, all_pairs_spec; [reflexivity|eauto 2].
Qed.  

Corollary non_overlapping_list_spec' : forall C,
  good_compartments C = true ->
  (non_overlapping_list C = true <-> (forall c1 c2,
                                        In2 c1 c2 C ->
                                        non_overlapping c1 c2 = true)).
Proof. intros C GOOD; apply non_overlapping_list_spec; auto. Qed.

Corollary good_compartments__in2_non_overlapping  : forall C c1 c2,
  good_compartments C = true ->
  In2 c1 c2 C ->
  non_overlapping c1 c2 = true.
Proof.
  intros C c1 c2 GOOD;
    assert (non_overlapping_list C = true) by auto;
    apply non_overlapping_list_spec' in GOOD;
    apply GOOD; assumption.
Qed.
Hint Resolve good_compartments__in2_non_overlapping.

(*** Proofs for/requiring `good_compartments' ***)

Theorem good_in2_no_common_addresses : forall C c1 c2,
  good_compartments C = true ->
  In2 c1 c2 C ->
  forall a, ~ (In a (address_space c1) /\ In a (address_space c2)).
Proof.
  intros until 0; intros GOOD IN2 a [IN_A1 IN_A2].
  apply good_compartments__in2_non_overlapping in IN2; auto.
  apply not_false_iff_true in IN2; apply IN2.
  unfold non_overlapping; destruct (set_intersection _ _) eqn:SI;
    [|reflexivity].
  rewrite nil_iff_not_in in SI; specialize SI with a.
  rewrite set_intersection_spec in SI; tauto.
Qed.
Hint Resolve good_in2_no_common_addresses.

Theorem in_compartment_opt_sound : forall C p c,
  forallb good_compartment C = true -> non_overlapping_list C = true ->
  C ⊢ p ∈ c ->
  in_compartment_opt C p = Some c.
Proof.
  clear.
  intros C p c GOOD NOL; induction 1 as [C A J S IN | C ch c IC]; simpl in *.
  - rewrite existsb_equiv_decb_in; auto.
  - destruct (existsb _ _) eqn:EX;
      [|rewrite andb_true_iff in *; invh and; eauto 3].
    assert (IN : In c C) by eauto 2; assert (IN2 : In2 ch c (ch :: C)) by auto.
    apply in_existsb_equiv_decb in EX;
      apply in_compartment__in_address_space in IC.
    apply non_overlapping_list_spec in IN2; auto.
    unfold non_overlapping in *.
    destruct (set_intersection _ _) eqn:SI; try congruence.
    rewrite nil_iff_not_in in SI; specialize SI with p.
    rewrite set_intersection_spec in SI; tauto.
Qed.
Hint Resolve in_compartment_opt_sound.

Corollary in_compartment_opt_sound' : forall C p c,
  good_compartments C = true ->
  C ⊢ p ∈ c ->
  in_compartment_opt C p = Some c.
Proof. intros C p c GOOD; apply in_compartment_opt_sound; auto. Qed.
Hint Resolve in_compartment_opt_sound'.

Corollary in_compartment_opt_sound_is_some : forall C p c,
  forallb good_compartment C = true -> non_overlapping_list C = true ->
  C ⊢ p ∈ c -> is_some (in_compartment_opt C p) = true.
Proof.
  intros C p c GOOD NOL IC;
    apply in_compartment_opt_sound in IC; [rewrite IC | | ]; auto.
Qed.
Hint Resolve in_compartment_opt_sound_is_some.

Corollary in_compartment_opt_sound_is_some' : forall C p c,
  good_compartments C = true ->
  C ⊢ p ∈ c -> is_some (in_compartment_opt C p) = true.
Proof.
  intros C p c GOOD IC;
    apply in_compartment_opt_sound' in IC; [rewrite IC|]; auto.
Qed.
Hint Resolve in_compartment_opt_sound_is_some'.

Theorem in_unique_compartment : forall C p c1 c2,
  good_compartments C = true ->
  C ⊢ p ∈ c1 ->
  C ⊢ p ∈ c2 ->
  c1 = c2.
Proof.
  intros until 0; intros GOOD IC1 IC2.
  assert (OVERLAPPING : non_overlapping c1 c2 = false) by eauto 2.
  assert (NOL : non_overlapping_list C = true) by auto.
  rewrite non_overlapping_list_spec in NOL; auto.
  destruct (c1 == c2); auto.
  lapply (NOL c1 c2); [congruence | eauto].
Qed.
Hint Resolve in_unique_compartment.

(*** Proofs about `good_syscall' and `get_syscall'. ***)

Hypothesis good_othercalls : forall MM,
  forallb (fun sc => good_syscall sc MM) othercalls = true.

Lemma isolate_create_set_is_set : forall M x sz X,
  isolate_create_set M x sz = Some X -> is_set X = true.
Proof.
  intros until 0; unfold isolate_create_set;
    destruct (forallb _ _); inversion 1; auto.
Qed.
Hint Resolve isolate_create_set_is_set.

Theorem isolate_good : forall MM, good_syscall isolate MM = true.
Proof.
  clear; unfold isolate, good_syscall; intros MM; simpl.
  destruct (good_state MM) eqn:GOOD, MM as [pc R M C];
    [unfold good_state in *; simpl in * | reflexivity].
  rewrite andb_true_iff in GOOD; destruct GOOD as [EICO GOOD].
  assert (ICO : exists c, in_compartment_opt C pc = Some c) by
    (destruct (in_compartment_opt _ _) eqn:?; [eauto | simpl in *; congruence]);
    clear EICO; move ICO after GOOD; destruct ICO as [c ICO].
  assert (IC : C ⊢ pc ∈ c) by (eapply in_compartment_opt_correct; eassumption);
    move IC after GOOD.
  (* Now, compute in `isolate_fn'. *)
  let (* Can't get the binder name, so we provide it *)
      DO var := match goal with
                  | |- match (do _ <- ?GET;   _) with _ => _ end = true =>
                    let def_var := fresh "def_" var in
                    destruct GET as [var|] eqn:def_var
                  | |- match (do guard ?COND; _) with _ => _ end = true =>
                    destruct COND eqn:var
                end; simpl; [|reflexivity]
  in rewrite ICO; simpl;
     DO al; DO ah; DO jt; DO sm; DO jtsz; DO smsz;
     DO LE; apply leb_le in LE;
     destruct c as [A J S] eqn:def_c; simpl;
     set (A' := range al ah); DO SUBSET_A';
     DO J'; DO SUBSET_J';
     DO S'; DO SUBSET_S';
     DO IC';
     rewrite IC'; simpl;
     set (c_upd := <<set_difference A A', insert_unique al J,S>>);
     set (c'    := <<A',J',S'>>);
     repeat rewrite <- def_c in *.
  unfold good_compartments in *; simpl;
    assert (good_compartments C = true) as TEMP by exact GOOD;
    move TEMP before GOOD; unfold good_compartments in TEMP;
    repeat rewrite andb_true_iff in TEMP; destruct TEMP as [[GOODS NOL] CC].
  assert (IN : In c C) by (subst; eauto 2).
  let is_good := (subst c c' c_upd A'; unfold good_compartment; simpl;
                  andb_true_split; eauto 2)
  in assert good_compartment c     by (rewrite forallb_forall in GOODS; auto);
     assert good_compartment c'    by is_good;
     assert good_compartment c_upd by is_good.
  assert (C'_NON_OVERLAPPING : forallb (non_overlapping c) (delete c C) =
                               true). {
    rewrite non_overlapping_list_spec in NOL; [|assumption].
    apply forallb_forall; intros ct IN_ct; apply NOL.
    apply delete_in_iff in IN_ct; apply in_neq_in2; intuition.
  }
  unfold non_overlapping_list; repeat rewrite all_tail_pairs_tail; simpl in *.
  andb_true_split; auto; try (eapply forallb_impl; [|apply C'_NON_OVERLAPPING]).
  - unfold non_overlapping; subst c c_upd c'; simpl in *.
    rewrite set_intersection_difference_distrib,
            set_intersection_self_id,
            set_difference_intersection_distrib,
            set_difference_self_annihilating,
            set_intersection_nil_r;
      try solve [subst A'; auto].
    subst A'; destruct (range _ _) eqn:RANGE;
      [|destruct (set_difference _ _); reflexivity].
    apply range_empty in RANGE; exfalso; auto.
  - intros c''; apply non_overlapping_subcompartment; auto; simpl.
    + apply nonempty_iff_in; rewrite existsb_exists in IC';
        destruct IC' as [pc' IC']; exists pc'; tauto.
    + subst c; intros a; rewrite set_difference_spec; tauto.
  - intros c''; apply non_overlapping_subcompartment; auto;
      subst c' A'; simpl in *.
    + apply nonempty_iff_in; exists al. apply range_elts; auto with ordered.
    + subst c; eapply subset_spec; eassumption.
  - unfold contained_compartments; subst c_upd c'; simpl.
    assert (In_dec : forall a A, In a A \/ ~ In a A). {
      clear -ops; intros; destruct (existsb (equiv_decb a) A) eqn:EX.
      - apply in_existsb_equiv_decb in EX; auto.
      - right. intro IN_a; apply existsb_equiv_decb_in in IN_a; congruence.
    }
    assert (A_separated : forall a, In a A <->
                                    In a (set_difference A A') \/ In a A'). {
      intros; specialize In_dec with a A';
        rewrite set_difference_spec; rewrite subset_spec in SUBSET_A'.
      split; [|destruct 1]; solve [auto | tauto].
    }
    assert (As_same : forall a,
              In a (set_difference A A' ++ A' ++
                    concat (map address_space (delete c C))) <->
              In a (concat (map address_space C))). {
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
        specialize In_dec with a A; destruct In_dec as [IN_a_A | NOT_IN_a_A];
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
    rewrite subset_spec in SUBSET_A',SUBSET_J',SUBSET_S';
      specialize SUBSET_A' with a;
      specialize SUBSET_J' with a;
      specialize SUBSET_S' with a;
      rewrite in_app_iff in SUBSET_J', SUBSET_S'.
    intros [IN_a_alJ | [IN_a_J' | [IN_a_JTs |
           [IN_a_S   | [IN_a_S' |  IN_a_SMs]]]]].
    (* There are essentially three proofs here: (1) In a J/S; (2) In a J'/S'
       (which calls out to (1)); and (3) In a (concat (map
       jump_targets/shared_memory (delete c C)).  I could not figure out how to
       Ltac them together nicely, however, so here you have it. *)
    + (* Unique proof *)
      apply insert_unique_spec in IN_a_alJ.
      destruct IN_a_alJ as [EQ | IN_J].
      * (* Unique proof *)
        subst a A'.
        assert (IN_al_range : In al (range al ah)) by
          (apply range_elts; auto with ordered).
        specialize (SUBSET_A' IN_al_range).
        rewrite concat_in; exists A; split; auto.
        apply in_map_iff. exists c; subst c; auto.
      * (* Proof (1) *)
        move CC after IN_J.
        rewrite contained_compartments_spec in CC;
          specialize (CC c a IN);
          subst c; simpl in *;
          specialize (CC (or_introl IN_J));
          destruct CC as [c'' [IN_c'' IN_a_c'']].
        apply concat_in; exists (address_space c'').
        split; auto. apply in_map_iff; eauto.
    + (* Proof (2) *)
      destruct (SUBSET_J' IN_a_J') as [IN_A | IN_J].
      * apply concat_in; exists A; split; auto.
        apply in_map_iff; exists c; subst c; simpl; tauto.
      * (* Proof (1) *)
        rewrite contained_compartments_spec in CC;
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
      rewrite contained_compartments_spec in CC.
        specialize (CC c'' a IN_c'');
        rewrite EQ_J'' in CC;
        specialize (CC (or_introl IN_a_J''));
        destruct CC as [c''' [IN_c''' IN_a_c''']].
      apply concat_in; exists (address_space c'''); split; auto.
      apply in_map_iff; eauto.
    + (* Proof (1) *)
      rewrite contained_compartments_spec in CC;
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
        rewrite contained_compartments_spec in CC;
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
      rewrite contained_compartments_spec in CC.
        specialize (CC c'' a IN_c'');
        rewrite EQ_S'' in CC;
        specialize (CC (or_intror IN_a_S''));
        destruct CC as [c''' [IN_c''' IN_a_c''']].
      apply concat_in; exists (address_space c'''); split; auto.
      apply in_map_iff; eauto.
Qed.
Hint Resolve isolate_good.

Corollary good_syscalls_b : forall MM,
  forallb (fun sc => good_syscall sc MM) table = true.
Proof. unfold table; simpl; intros; andb_true_split; auto. Qed.
Hint Resolve good_syscalls_b.

Corollary good_syscalls : forall MM sc,
  In sc table -> good_syscall sc MM = true.
Proof. intros MM; apply forallb_forall; auto. Qed.
Hint Resolve good_syscalls.

Lemma get_syscall_in : forall addr sc,
  get_syscall addr = Some sc -> In sc table.
Proof.
  unfold get_syscall; intros addr sc GS; apply find_in in GS; tauto.
Qed.
Hint Resolve get_syscall_in.

Lemma get_syscall_good : forall addr sc,
  get_syscall addr = Some sc -> forall MM, good_syscall sc MM = true.
Proof.
  intros addr sc GS; apply get_syscall_in in GS; auto.
Qed.
Hint Resolve get_syscall_good.

(*** Proofs about `good_state' ***)

(* For `auto' *)
Lemma good_state__in_compartment_opt : forall MM,
  good_state MM = true ->
  is_some (in_compartment_opt (compartments MM) (pc MM)) = true.
Proof.
  unfold good_state; intros; rewrite andb_true_iff in *; tauto.
Qed.
Hint Resolve good_state__in_compartment_opt.

(* For `auto' *)
Lemma good_state_decomposed__in_compartment_opt : forall pc R M C,
  good_state (mk_state pc R M C) = true ->
  is_some (in_compartment_opt C pc) = true.
Proof.
  intros pc R M C; apply (good_state__in_compartment_opt (mk_state pc R M C)).
Qed.
Hint Resolve good_state_decomposed__in_compartment_opt.

(* For `auto' *)
Lemma good_state__good_compartments : forall MM,
  good_state MM = true -> good_compartments (compartments MM) = true.
Proof.
  unfold good_state; intros; rewrite andb_true_iff in *; tauto.
Qed.
Hint Resolve good_state__good_compartments.

(* For `auto' *)
Lemma good_state_decomposed__good_compartments : forall pc R M C,
  good_state (mk_state pc R M C) = true -> good_compartments C = true.
Proof.
  intros pc R M C; apply (good_state__good_compartments (mk_state pc R M C)).
Qed.
Hint Resolve good_state_decomposed__good_compartments.

(*** Proofs about the machine. ***)

Lemma in_compartment_preserved : forall MM MM',
  good_compartments (compartments MM) = true ->
  step MM MM' ->
  is_some (in_compartment_opt (compartments MM)  (pc MM))  = true ->
  is_some (in_compartment_opt (compartments MM') (pc MM')) = true.
Proof.
  clear S.
  intros MM MM' GOOD_COMPARTMENTS STEP; induction STEP; simpl; intros GOOD;
    try (destruct STEP; eauto).
  - (* Jump *)
    apply in_app_or in VALID; destruct VALID as [VALID | VALID]; [eauto|].
    assert (CC : contained_compartments C = true) by auto.
    unfold contained_compartments in CC;
      rewrite subset_spec in CC; specialize CC with pc';
      rewrite in_app_iff in CC.
    lapply CC; clear CC; [intros CC|].
    + apply concat_in in CC; destruct CC as [A [IN_A IN_pc']].
      apply in_map_iff in IN_A; destruct IN_A as [c' [EQ IN_c']]; subst.
      apply in_compartment_opt_is_some with c', in_compartment_spec; auto.
    + left. apply concat_in; exists (jump_targets c); split; auto.
      apply in_map_iff; eauto.
  - (* Jal *)
    (* Exactly the same as above.  Not sure how to Ltac this. *)
    apply in_app_or in VALID; destruct VALID as [VALID | VALID]; [eauto|].
    assert (CC : contained_compartments C = true) by auto.
    unfold contained_compartments in CC;
      rewrite subset_spec in CC; specialize CC with pc';
      rewrite in_app_iff in CC.
    lapply CC; clear CC; [intros CC|].
    + apply concat_in in CC; destruct CC as [A [IN_A IN_pc']].
      apply in_map_iff in IN_A; destruct IN_A as [c' [EQ IN_c']]; subst.
      apply in_compartment_opt_is_some with c', in_compartment_spec; auto.
    + left. apply concat_in; exists (jump_targets c); split; auto.
      apply in_map_iff; eauto.
  - (* Syscall *)
    assert (GOOD_STATE : good_state (mk_state pc0 R M C) = true) by
      (unfold good_state; simpl; andb_true_split; auto).
    apply good_state__in_compartment_opt.
    apply get_syscall_good with (MM := mk_state pc0 R M C) in GETSC;
      unfold good_syscall in GETSC; rewrite GOOD_STATE in GETSC.
    destruct (semantics _ _); inversion CALL; subst; auto.
Qed.    
Hint Resolve in_compartment_preserved.

Lemma good_compartments_preserved : forall MM MM',
  step MM MM' ->
  good_compartments (compartments MM)  = true ->
  good_compartments (compartments MM') = true.
Proof.
  clear S.
  intros MM MM' STEP; induction STEP; simpl; intros GOOD; try (exact GOOD).
  assert (GOOD_STATE : good_state (mk_state pc0 R M C) = true) by (
    unfold good_state; simpl; andb_true_split; auto;
    apply in_compartment_opt_sound' in IN_C; [rewrite IN_C|]; auto
  ).
  apply get_syscall_good with (MM := mk_state pc0 R M C) in GETSC;
    unfold good_syscall in GETSC; rewrite GOOD_STATE in GETSC.
  destruct (semantics _ _); inversion CALL; subst; auto.
Qed.
Hint Resolve good_compartments_preserved.

Theorem good_state_preserved : forall MM MM',
  step MM MM'           ->
  good_state MM  = true ->
  good_state MM' = true.
Proof.
  unfold good_state; intros; rewrite andb_true_iff in *; invh and; eauto 4.
Qed.
Hint Resolve good_state_preserved.

(******************************************************************************)

Inductive valid_trace : list state -> Prop :=
| vt_nil  : valid_trace []
| vt_one  : forall MM, valid_trace [MM]
| vt_step : forall {MM MM' MMs}, step MM MM' -> valid_trace (MM' :: MMs) ->
            valid_trace (MM :: MM' :: MMs).  

(* There has GOT to be a better way to do this *)
Inductive direct_parent : forall {MMs : list state}, valid_trace MMs ->
                          compartment -> compartment -> Prop :=
(* step_isolate went away *)
(* | dp_here  : forall pc R M C c pc_val rtgt al ah jt sm jtsz smsz
                    PC INST STEP ISISO GETR1 GETR2 GETR3 GETR4 GETM3 GETM4
                    RANGE SUBA SUBJ SUBS,
             let A     := address_space c in
             let J     := jump_targets  c in
             let S     := shared_memory c in
             let A'    := range al ah in
             let J'    := isolate_create_set M jt jtsz in
             let S'    := isolate_create_set M sm smsz in
             let c_upd := <<set_difference A A', insert_unique al J, S>> in
             let c'    := <<A',J',S'>> in
             let C'    := c_upd :: c' :: delete c C in
             forall {MMs} (VT : valid_trace (mk_state (pc + 1) R M C' :: MMs)),
             direct_parent (vt_step (@step_isolate pc R M C c pc_val rtgt al ah jt sm jtsz smsz PC INST STEP ISISO GETR1 GETR2 GETR3 GETR4 GETM3 GETM4 RANGE SUBA SUBJ SUBS) VT) c c' *)
| dp_there : forall MM MM' MMs
                    (STEP : step MM MM') (VT : valid_trace (MM' :: MMs))
                    c1 c2
                    (DP : direct_parent VT c1 c2),
             direct_parent (vt_step STEP VT) c1 c2.

Inductive direct_descendant : forall {MMs : list state}, valid_trace MMs ->
                              compartment -> compartment -> Prop :=
(* step_isolate went away *)
(* | dd_here  : forall pc R M C c pc_val rtgt al ah jt sm jtsz smsz
                    PC INST STEP ISISO GETR1 GETR2 GETR3 GETR4 GETM3 GETM4
                    RANGE SUBA SUBJ SUBS,
             let A     := address_space c in
             let J     := jump_targets  c in
             let S     := shared_memory c in
             let A'    := range al ah in
             let J'    := isolate_create_set M jt jtsz in
             let S'    := isolate_create_set M sm smsz in
             let c_upd := <<set_difference A A', insert_unique al J, S>> in
             let c'    := <<A',J',S'>> in
             let C'    := c_upd :: c' :: delete c C in
             forall {MMs} (VT : valid_trace (mk_state (pc + 1) R M C' :: MMs)),
             direct_descendant (vt_step (@step_isolate pc R M C c pc_val rtgt al ah jt sm jtsz smsz PC INST STEP ISISO GETR1 GETR2 GETR3 GETR4 GETM3 GETM4 RANGE SUBA SUBJ SUBS) VT) c c_upd *)
| dd_there : forall MM MM' MMs
                    (STEP : step MM MM') (VT : valid_trace (MM' :: MMs))
                    c1 c2
                    (DP : direct_descendant VT c1 c2),
             direct_descendant (vt_step STEP VT) c1 c2.

Inductive parent {MMs : list state} (VT : valid_trace MMs) :
                 compartment -> compartment -> Prop :=
| parent_refl : forall c, parent VT c c
| parent_step : forall c1 c2 c3
                       (DIRECT : direct_parent VT c1 c2)
                       (PARENT : parent        VT c2 c3),
                parent VT c1 c3.

Inductive descendant {MMs : list state} (VT : valid_trace MMs) :
                     compartment -> compartment -> Prop :=
| descendant_refl : forall c, descendant VT c c
| descendant_step : forall c1 c2 c3
                           (DIRECT     : direct_descendant VT c1 c2)
                           (DESCENDANT : descendant        VT c2 c3),
                    descendant VT c1 c3.

Inductive in_cone {MMs : list state} (VT : valid_trace MMs) :
                  compartment -> compartment -> Prop :=
| in_cone_refl       : forall c,
                       in_cone VT c c
| in_cone_parent     : forall c1 c2 c3
                              (PARENT : parent  VT c1 c2)
                              (CONE   : in_cone VT c2 c3),
                       in_cone VT c1 c3
| in_cone_descendant : forall c1 c2 c3
                              (DESCENDANT : descendant VT c1 c2)
                              (CONE       : in_cone    VT c2 c3),
                       in_cone VT c1 c3.

Inductive step_in (MM MM' : state) :
                  forall {MMs : list state}, valid_trace MMs -> Prop :=
| step_in_here  : forall (STEP : step MM MM')
                         {MMs : list state} (VT : valid_trace (MM' :: MMs)),
                  step_in MM MM' (vt_step STEP VT)
| step_in_there : forall MM'' MM''' (STEP : step MM'' MM''')
                         {MMs : list state} (VT : valid_trace (MM''' :: MMs))
                         (STEP_IN : step_in MM MM' VT),
                  step_in MM MM' (vt_step STEP VT).

Lemma permitted_execution_steps : forall MM MM' (STEP : step MM MM') c,
  (* Need to define `good_state' *)
  good_state MM = true ->
  compartments MM  ⊢ pc MM  ∈ c ->
  compartments MM' ⊢ pc MM' ∈ c \/ In (pc MM') (jump_targets c).
Proof.
  intros until 1; induction STEP; intros c0 NOL IN_c0; simpl in *;
    try solve
      [ (* Intra-compartment *)
        destruct STEP; left;
        apply in_unique_compartment with (c1 := c) in IN_c0;
        subst; simpl in *; eauto 2
      | (* Jump/Jal *)
        apply in_unique_compartment with (c1 := c) in IN_c0; subst;
        try assumption; eauto 2;
        apply in_app_iff in VALID; destruct VALID as [IN_A | IN_J];
        [ left; eapply in_same_compartment; [exact IN_C | exact IN_A]
        | right; exact IN_J ] ].
  (* Syscalls *)
  admit.
  (* I'm not sure what the right behavior here is -- it'll depend on the other
     theorems I end up trying to prove. *)
Qed.
                                       
End WithClasses.

End Abstract.
