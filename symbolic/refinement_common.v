Require Import List NPeano Arith Bool.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Require Import lib.utils lib.Coqlib lib.partial_maps.
Require Import common.common.
Require Import concrete.concrete.
Require Import concrete.exec.
Require Import symbolic.symbolic.
Require Import symbolic.rules.

Open Scope nat_scope.

Set Implicit Arguments.

Import ListNotations.

Hint Constructors restricted_exec.
Hint Unfold exec.
Hint Resolve restricted_exec_trans.

Section Refinement.

Context {mt : machine_types}
        {ops : machine_ops mt}
        {opss : machine_ops_spec ops}
        {ap : @Symbolic.symbolic_params mt}
        {memax : PartMaps.axioms (@Symbolic.sm mt ap)}
        {regax : PartMaps.axioms (@Symbolic.sr mt ap)}
        {cp : Concrete.concrete_params mt}
        {cps : Concrete.params_spec cp}
        {e : @encodable (Symbolic.tag mt) mt ops}.

Definition refine_memory (amem : Symbolic.memory mt) (cmem : Concrete.memory mt) :=
  forall w x t,
    PartMaps.get cmem w = Some x@(encode (USER t)) <->
    PartMaps.get amem w = Some x@t.

Definition refine_registers (areg : Symbolic.registers mt) (creg : Concrete.registers mt) :=
  forall n x t,
    TotalMaps.get creg n = x@(encode (USER t)) <->
    PartMaps.get areg n = Some x@t.

Definition in_kernel st :=
  let pct := common.tag (Concrete.pc st) in
  Concrete.is_kernel_tag _ pct.
Hint Unfold in_kernel.

Definition in_user st :=
  let pct := common.tag (Concrete.pc st) in
  word_lift (fun t => is_user t) pct.
Hint Unfold in_user.

Let handler := handler (fun x => Symbolic.handler x).

Definition cache_correct cache :=
  forall cmvec crvec,
    word_lift (fun x => is_user x) (Concrete.ctpc cmvec) = true ->
    Concrete.cache_lookup ops cache masks cmvec = Some crvec ->
    exists rvec,
      crvec = encode_rvec rvec /\
      handler cmvec = Some rvec.

Definition in_mvec addr := In addr (Concrete.mvec_fields _).

Definition mvec_in_kernel cmem :=
  forall addr,
    in_mvec addr ->
    exists w, PartMaps.get cmem addr = Some w@Concrete.TKernel.

Lemma store_mvec_mvec_in_kernel cmem cmem' mvec :
  Concrete.store_mvec ops cmem mvec = Some cmem' ->
  mvec_in_kernel cmem'.
Proof.
  unfold Concrete.store_mvec, mvec_in_kernel, in_mvec.
  intros H addr IN.
  destruct (PartMaps.get_upd_list_in H IN)
    as (v' & IN' & GET).
  rewrite GET.
  simpl in IN'.
  repeat match goal with
  | H : _ \/ _ |- _ => destruct H as [E | ?]; [inv E|]
  | H : False |- _ => destruct H
  end; eauto.
Qed.

Lemma mvec_in_kernel_store_mvec cmem mvec :
  mvec_in_kernel cmem ->
  exists cmem',
    Concrete.store_mvec ops cmem mvec = Some cmem'.
Proof.
  unfold mvec_in_kernel, in_mvec, Concrete.mvec_fields, Concrete.store_mvec.
  intros DEF.
  eapply PartMaps.upd_list_defined; eauto using Concrete.mem_axioms.
  apply eqType_EqDec.
  simpl map. intros addr IN.
  apply DEF in IN.
  destruct IN.
  eauto.
Qed.

Definition ra_in_user creg :=
  word_lift (fun x => is_user x)
            (common.tag (TotalMaps.get creg ra)).
Hint Unfold ra_in_user.

(* CH: kernel_invariant only holds when kernel starts executing, can
   be broken during kernel execution, but has to be restored before
   returning to user mode. It doesn't necessarily have to hold at all
   intermediate kernel steps. Right? *)
(* CH: I find the way the "kernel invariant" is stated rather
   indirect. Is there no direct way to define this? *)
(* AAA: We need to add the cache as an argument here, since we don't
   assume anything about ground rules right now *)

Record kernel_invariant : Type := {
  kernel_invariant_statement :> Concrete.memory mt ->
                                Concrete.registers mt ->
                                Concrete.rules (word mt) ->
                                Symbolic.internal_state mt -> Prop;

  kernel_invariant_upd_mem :
    forall regs mem1 mem2 cache addr w1 ut w2 int
           (KINV : kernel_invariant_statement mem1 regs cache int)
           (GET : PartMaps.get mem1 addr = Some w1@(encode (USER ut)))
           (UPD : PartMaps.upd mem1 addr w2 = Some mem2),
      kernel_invariant_statement mem2 regs cache int;

  kernel_invariant_upd_reg :
    forall mem regs cache r w1 ut1 w2 ut2 int
           (KINV : kernel_invariant_statement mem regs cache int)
           (GET : TotalMaps.get regs r = w1@(encode (USER ut1))),
      kernel_invariant_statement mem (TotalMaps.upd regs r w2@(encode (USER ut2))) cache int;

  kernel_invariant_store_mvec :
    forall mem mem' mvec regs cache int
           (KINV : kernel_invariant_statement mem regs cache int)
           (MVEC : Concrete.store_mvec ops mem mvec = Some mem'),
      kernel_invariant_statement mem' regs cache int
}.

Hint Resolve kernel_invariant_upd_mem.
Hint Resolve kernel_invariant_upd_reg.
Hint Resolve kernel_invariant_store_mvec.

Variable ki : kernel_invariant.

Lemma is_user_pc_tag_is_kernel_tag tg :
  word_lift (fun x => is_user x) tg = true -> Concrete.is_kernel_tag _ tg = false.
Proof.
  unfold word_lift, is_user, Concrete.is_kernel_tag.
  destruct (decode tg) as [[ut| |]|] eqn:E; try discriminate.
  intros _.
  apply encodeK in E.
  have [E'|//] := eqP.
  simpl in *; subst; eauto.
  erewrite encode_kernel_tag in E'.
  now apply encode_inj in E'.
Qed.

Lemma in_user_in_kernel :
  forall st, in_user st = true -> in_kernel st = false.
Proof.
  unfold in_user, in_kernel, word_lift, Concrete.is_kernel_tag.
  intros st H.
  destruct (decode (common.tag (Concrete.pc st)))
    as [[t| |]|] eqn:DEC; simpl in *; try discriminate;
  apply encodeK in DEC.
  rewrite <- DEC.
  rewrite encode_kernel_tag.
  rewrite eq_tag_eq_word. reflexivity.
Qed.

Variable table : list (Symbolic.syscall mt).

Definition wf_entry_points cmem :=
  forall addr t,
    (exists sc, Symbolic.get_syscall table addr = Some sc /\
                Symbolic.entry_tag sc = t) <->
    match PartMaps.get cmem addr with
    | Some i@it => (i == encode_instr (Nop _)) && (it == encode (ENTRY t))
    | None => false
    end = true.

Lemma wf_entry_points_if cmem addr sc :
  wf_entry_points cmem ->
  Symbolic.get_syscall table addr = Some sc ->
  PartMaps.get cmem addr = Some (encode_instr (Nop _))@(encode (ENTRY (Symbolic.entry_tag sc))).
Proof.
  move => WFENTRYPOINTS GETCALL.
  have: exists sc', Symbolic.get_syscall table addr = Some sc' /\
                    Symbolic.entry_tag sc' = Symbolic.entry_tag sc by eauto.
  move/WFENTRYPOINTS.
  case: (PartMaps.get cmem addr) => [[i it]|] //.
  move/andP => [H1 H2]. move/eqP: H1 => ->. by move/eqP : H2 => ->.
Qed.

Definition refine_state (st : Symbolic.state mt) (st' : Concrete.state mt) :=
  in_user st' = true /\
  let '(Symbolic.State mem regs pc@tpc int) := st in
  let '(Concrete.mkState mem' regs' cache pc'@tpc' epc) := st' in
  pc = pc' /\
  match decode tpc' with
  | Some (USER tpc') => tpc' = tpc
  | _ => False
  end /\
  refine_memory mem mem' /\
  refine_registers regs regs' /\
  cache_correct cache /\
  mvec_in_kernel mem' /\
  ra_in_user regs' /\
  wf_entry_points mem' /\
  ki mem' regs' cache int.

Lemma refine_memory_upd amem cmem cmem' addr v v' t t' :
  refine_memory amem cmem ->
  PartMaps.get cmem addr = Some v@(encode (USER t)) ->
  PartMaps.upd cmem addr v'@(encode (USER t')) = Some cmem' ->
  exists amem',
    PartMaps.upd amem addr v'@t' = Some amem' /\
    refine_memory amem' cmem'.
Proof.
  intros MEM GET UPD.
  assert (GET' := proj1 (MEM _ _ _) GET).
  destruct (PartMaps.upd_defined v'@t' GET') as [amem' UPD'].
  do 2 eexists; eauto.
  intros addr' w'.
  have [EQ|/eqP NEQ] := altP (addr' =P addr); simpl in *; subst.
  - apply MEM in GET.
    rewrite (PartMaps.get_upd_eq UPD).
    rewrite (PartMaps.get_upd_eq UPD').
    intros t''. split; try congruence.
    intros H.
    inv H.
    exploit (fun T => @encode_inj T mt); try eassumption; eauto.
    congruence.
  - rewrite (PartMaps.get_upd_neq NEQ UPD').
    rewrite (PartMaps.get_upd_neq NEQ UPD).
    now apply MEM.
Qed.

Lemma wf_entry_points_user_upd cmem cmem' addr v v' t t' :
  wf_entry_points cmem ->
  PartMaps.get cmem addr = Some v@(encode (USER t)) ->
  PartMaps.upd cmem addr v'@(encode (USER t')) = Some cmem' ->
  wf_entry_points cmem'.
Proof.
  unfold wf_entry_points.
  intros WF GET UPD addr'.
  split; intros H.
  - rewrite ->WF in H.
    destruct (PartMaps.get cmem addr') as [[v'' t'']|] eqn:MEM; try discriminate.
    erewrite PartMaps.get_upd_neq; eauto using Concrete.mem_axioms.
    { now rewrite MEM. }
    intros ?. subst addr'.
    assert (EQ : t'' = encode (USER t)) by congruence. subst.
    move/andP: H => [_ H].
    by move/eqP/encode_inj: H.
  - apply WF. clear WF.
    destruct (PartMaps.get cmem' addr') as [[v'' t'']|] eqn:GET'; try discriminate.
    erewrite PartMaps.get_upd_neq in GET'; eauto using Concrete.mem_axioms.
    { now rewrite GET'. }
    intros ?. subst addr'.
    erewrite PartMaps.get_upd_eq in GET'; eauto using Concrete.mem_axioms.
    assert (EQ : t''= encode (USER t')) by congruence. subst.
    move/andP: H => [_ H].
    by move/eqP/encode_inj: H.
Qed.

Lemma mvec_in_kernel_user_upd cmem cmem' addr v v' t t' :
  mvec_in_kernel cmem ->
  PartMaps.get cmem addr = Some v@(encode (USER t)) ->
  PartMaps.upd cmem addr v'@(encode (USER t')) = Some cmem' ->
  mvec_in_kernel cmem'.
Proof.
  intros MVEC GET UPD.
  intros addr' H.
  specialize (MVEC addr' H). destruct MVEC as [w' KER].
  assert (NEQ : addr' <> addr).
  { intros E. subst addr'.
    assert (CONTRA : Concrete.TKernel = encode (USER t))
      by congruence.
    erewrite encode_kernel_tag in CONTRA.
    now apply encode_inj in CONTRA. }
  rewrite (PartMaps.get_upd_neq NEQ UPD).
  eauto.
Qed.

Lemma mvec_in_kernel_kernel_upd cmem cmem' addr w :
  mvec_in_kernel cmem ->
  PartMaps.upd cmem addr w@Concrete.TKernel = Some cmem' ->
  mvec_in_kernel cmem'.
Proof.
  intros MVEC UPD addr' IN.
  have [?|/eqP NEQ] := altP (addr' =P addr); simpl in *; subst.
  - erewrite PartMaps.get_upd_eq; eauto using Concrete.mem_axioms.
  - erewrite (PartMaps.get_upd_neq NEQ UPD).
    now apply MVEC.
Qed.

Lemma refine_memory_upd' amem amem' cmem addr v t :
  refine_memory amem cmem ->
  PartMaps.upd amem addr v@t = Some amem' ->
  exists cmem',
    PartMaps.upd cmem addr v@(encode (USER t)) = Some cmem' /\
    refine_memory amem' cmem'.
Proof.
  intros MEM UPD.
  destruct (PartMaps.upd_inv UPD) as [[w' t'] GET].
  apply MEM in GET.
  eapply PartMaps.upd_defined in GET; auto using Concrete.mem_axioms.
  destruct GET as [cmem' UPD'].
  eexists. split; eauto.
  intros addr' w'' t''.
  have [EQ|/eqP NEQ] := altP (addr' =P addr); simpl in *; subst.
  - rewrite (PartMaps.get_upd_eq UPD').
    rewrite (PartMaps.get_upd_eq UPD).
    split; try congruence.
    intros ?.
    assert (E : USER t = USER t''); try congruence.
    eapply encode_inj. congruence.
  - rewrite (PartMaps.get_upd_neq NEQ UPD).
    rewrite (PartMaps.get_upd_neq NEQ UPD').
    now apply MEM.
Qed.

Lemma refine_registers_upd areg creg r v v' t t' :
  refine_registers areg creg ->
  TotalMaps.get creg r = v@(encode (USER t)) ->
  exists areg',
    PartMaps.upd areg r v'@t' = Some areg' /\
    refine_registers areg' (TotalMaps.upd creg r v'@(encode (USER t'))).
Proof.
  intros REG GET.
  assert (GET' := proj1 (REG _ _ _) GET).
  assert (NEW := PartMaps.upd_defined v'@t' GET').
  destruct NEW as [areg' UPD].
  eexists. split; eauto.
  intros r' v'' t''.
  have [EQ|/eqP NEQ] := altP (r' =P r); simpl in *; subst.
  - rewrite (TotalMaps.get_upd_eq (Concrete.reg_axioms (t := mt))).
    rewrite (PartMaps.get_upd_eq UPD).
    split; try congruence.
    intros ?.
    assert (USER t' = USER t''); try congruence.
    eapply encode_inj; congruence.
  - rewrite (TotalMaps.get_upd_neq (Concrete.reg_axioms (t := mt))); trivial.
    rewrite (PartMaps.get_upd_neq NEQ UPD).
    now apply REG.
Qed.

Lemma refine_registers_upd' areg areg' creg r v t :
  refine_registers areg creg ->
  PartMaps.upd areg r v@t = Some areg' ->
  refine_registers areg' (TotalMaps.upd creg r v@(encode (USER t))).
Proof.
  intros REF UPD r' v' t'.
  have [EQ|/eqP NEQ] := altP (r' =P r); simpl in *.
  - subst r'.
    rewrite (TotalMaps.get_upd_eq (Concrete.reg_axioms (t := mt))).
    rewrite (PartMaps.get_upd_eq UPD).
    split; try congruence.
    intros ?.
    assert (USER t' = USER t); try congruence.
    eapply encode_inj; try congruence.
  - rewrite (TotalMaps.get_upd_neq (Concrete.reg_axioms (t := mt))); trivial.
    rewrite (PartMaps.get_upd_neq NEQ UPD).
    now apply REF.
Qed.

Lemma ra_in_user_upd creg r v t :
  ra_in_user creg ->
  ra_in_user (TotalMaps.upd creg r v@(encode (USER t))).
Proof.
  unfold ra_in_user.
  have [EQ|/eqP NEQ] := altP (r =P ra); simpl in *; autounfold.
  - subst r.
    rewrite (TotalMaps.get_upd_eq (Concrete.reg_axioms (t := mt))).
    simpl. unfold word_lift. now rewrite decodeK.
  - rewrite (TotalMaps.get_upd_neq (Concrete.reg_axioms (t := mt))); try congruence.
Qed.

Inductive hit_step cst cst' : Prop :=
| hs_intro (USER : in_user cst = true)
           (USER' : in_user cst' = true)
           (STEP : Concrete.step _ masks cst cst').

Definition kernel_exec kst kst' :=
  restricted_exec (Concrete.step _ masks)
                  (fun s => in_kernel s = true)
                  kst kst'.
Hint Unfold kernel_exec.

Definition kernel_user_exec kst st : Prop :=
  exec_until (Concrete.step _ masks)
             (fun s => in_kernel s = true)
             (fun s => in_kernel s = false)
             kst st.

Inductive user_kernel_user_step cst cst' : Prop :=
| ukus_intro kst
             (USER : in_user cst = true)
             (STEP : Concrete.step _ masks cst kst)
             (EXEC : kernel_user_exec kst cst').

Lemma user_kernel_user_step_weaken cst cst' :
  user_kernel_user_step cst cst' ->
  exec (Concrete.step _ masks) cst cst'.
Proof.
  move => [cst'' ? ? ?].
  eapply re_step; trivial; try eassumption.
  eapply exec_until_weaken; eassumption.
Qed.

Definition user_step cst cst' :=
  hit_step cst cst' \/ user_kernel_user_step cst cst'.

Import Vector.VectorNotations.

Lemma analyze_cache cache cmvec crvec op :
  cache_correct cache ->
  Concrete.cache_lookup _ cache masks cmvec = Some crvec ->
  word_lift (fun t => is_user t) (Concrete.ctpc cmvec) = true ->
  Concrete.cop cmvec = op_to_word op ->
  exists tpc, Concrete.ctpc cmvec = encode (USER tpc) /\
  (match Symbolic.nfields op as fs return (_ -> _ -> Symbolic.mvec_operands (@Symbolic.tag mt ap) fs -> _) -> Prop with
   | Some fs => fun mk =>
     exists ti (ts : Vector.t _ (fst fs)) trpc tr,
     Concrete.cti cmvec = encode (USER ti) /\
     crvec = Concrete.mkRVec (encode (USER trpc))
                             (encode (USER tr)) /\
     Symbolic.handler (mk tpc ti ts) = Some (Symbolic.mkRVec trpc tr) /\
     match fst fs as n return Vector.t _ n -> Prop with
     | 0 => fun ts => ts = []
     | 1 => fun ts => exists t1,
                        ts = [t1] /\
                        Concrete.ct1 cmvec = encode (USER t1)
     | 2 => fun ts => exists t1 t2,
                        ts = [t1; t2] /\
                        Concrete.ct1 cmvec = encode (USER t1) /\
                        Concrete.ct2 cmvec = encode (USER t2)
     | 3 => fun ts => exists t1 t2 t3,
                        ts = [t1; t2; t3] /\
                        Concrete.ct1 cmvec = encode (USER t1) /\
                        Concrete.ct2 cmvec = encode (USER t2) /\
                        Concrete.ct3 cmvec = encode (USER t3)
     | _ => fun _ => False
     end ts
   | None => fun _ => False
   end (Symbolic.mkMVec op) \/
   exists t,
     op = NOP /\
     Concrete.cti cmvec = encode (ENTRY t) /\
     crvec = Concrete.mkRVec (encode KERNEL) (encode KERNEL)).
Proof.
  intros CACHE LOOKUP INUSER EQ.
  destruct cmvec as [op' tpc ti t1 t2 t3].
  destruct (CACHE _ crvec INUSER LOOKUP)
    as ([trpc tr] & ? & HIT). subst. simpl in *.
  simpl in HIT.
  destruct (word_to_op op') as [op''|] eqn:E; try discriminate. subst op'.
  rewrite op_to_wordK in E.
  move: E => [E]. subst op''.
  unfold encode_mvec, encode_rvec in *. simpl in *.
  destruct op; simpl in *; match_inv;
  repeat match goal with
  | H : decode ?t = Some _ |- _ =>
    apply encodeK in H; subst t
  end;
  eexists; split; eauto;
  try match goal with
  | rvec : Symbolic.RVec _ |- _ => destruct rvec
  end;
  simpl in *;
  repeat (
    match goal with
    | ts : Vector.t _ 0 |- _ => induction ts using Vector.case0
    | ts : Vector.t _ (S _) |- _ => induction ts using caseS
    | |- context[decode (encode _)] => rewrite decodeK
    end; simpl
  );
  simpl in *; left;
  do 4 eexists; repeat (split; eauto);

  (* match_inv is to brutal with equalities involving dependent types *)
  repeat match goal with
  | H : bind _ ?X = Some _ |- _ =>
    match X with
    | context[match ?a with _ => _ end] =>
      destruct a as [?| |];
      try solve [inversion H];
      simpl in H
    end
  end;
  solve [inv HIT; eauto 7].
Qed.

Let miss_state_not_user st st' mvec :
  Concrete.miss_state ops st mvec = Some st' ->
  in_user st' = true ->
  False.
Proof.
  intros MISS INUSER.
  apply in_user_in_kernel in INUSER.
  unfold Concrete.miss_state in MISS.
  unfold in_kernel, Concrete.is_kernel_tag in INUSER.
  match_inv. simpl in *.
  rewrite eqxx in INUSER; try apply eq_wordP.
  simpl in INUSER. discriminate.
Qed.

Ltac analyze_cache :=
  match goal with
  | LOOKUP : Concrete.cache_lookup _ ?cache _ ?mvec = Some ?rvec,
    PC     : PartMaps.get _ ?pc = Some ?i@_,
    INST   : decode_instr ?i = Some _,
    INUSER : in_user (Concrete.mkState _ _ _ ?pc@_ _) = true,
    CACHE  : cache_correct ?cache |- _ =>
    unfold in_user in INUSER; simpl in INUSER;
    assert (CACHEHIT := analyze_cache mvec _ CACHE LOOKUP INUSER (erefl _));
    simpl in CACHEHIT;
    repeat match type of CACHEHIT with
    | exists _, _ => destruct CACHEHIT as [? CACHEHIT]
    | _ /\ _ => destruct CACHEHIT as [? CACHEHIT]
    | _ \/ _ => destruct CACHEHIT as [CACHEHIT | CACHEHIT]
    | False => destruct CACHEHIT
    end;
    subst mvec; simpl in *; subst;
    try match goal with
    | H : context[decode (encode _)] |- _ =>
      rewrite decodeK in H; simpl in *; subst
    end
  | MISS   : Concrete.miss_state _ _ _ = Some ?st',
    INUSER : in_user ?st' = true |- _ =>
    destruct (miss_state_not_user _ _ MISS INUSER)
  end.

Lemma valid_initial_user_instr_tags cst cst' v ti :
  cache_correct (Concrete.cache cst) ->
  in_user cst = true ->
  in_user cst' = true ->
  Concrete.step _ masks cst cst' ->
  PartMaps.get (Concrete.mem cst) (common.val (Concrete.pc cst)) = Some v@ti ->
  match decode ti with
  | Some (USER _) => true
  | _ => false
  end.
Proof.
  intros CACHE INUSER INUSER' STEP GET;
  inv STEP;
  unfold Concrete.next_state_reg, Concrete.next_state_reg_and_pc,
         Concrete.next_state_pc, Concrete.next_state,
         Concrete.miss_state in *;
  simpl in *;

  match_inv;

  try analyze_cache;

  try match goal with
  | H1 : PartMaps.get ?mem ?pc = Some _@?w1,
    H2 : PartMaps.get ?mem ?pc = Some _@?w2 |- _ =>
    let EQ := fresh "EQ" in
    assert (EQ : w1 = w2) by congruence;
    try (apply encode_inj in EQ; discriminate EQ);
    subst
  end;

  by [
      rewrite decodeK
    | rewrite /in_user /word_lift ?encode_kernel_tag decodeK /= in INUSER'
  ].
Qed.

Lemma valid_pcs st st' :
  Concrete.step _ masks st st' ->
  cache_correct (Concrete.cache st) ->
  in_user st = true ->
  match decode (common.tag (Concrete.pc st')) with
  | Some (USER _) => true
  | Some KERNEL => true
  | _ => false
  end = true.
Proof.
  intros STEP CACHE INUSER. simpl.
  inv STEP;
  unfold Concrete.next_state_reg, Concrete.next_state_reg_and_pc,
         Concrete.next_state_pc, Concrete.next_state,
         Concrete.miss_state in *;
  simpl in *;

  match_inv;

  try analyze_cache;

  simpl in *; try erewrite encode_kernel_tag; now rewrite decodeK.

Qed.

Ltac simpl_word_lift :=
  match goal with
  | H : context[word_lift _ (encode _)] |- _ =>
    unfold word_lift in H;
    rewrite decodeK in H;
    simpl in H
  end.

Hint Unfold Symbolic.next_state.
Hint Unfold Symbolic.next_state_reg_and_pc.
Hint Unfold Symbolic.next_state_pc.
Hint Unfold Symbolic.next_state_reg.

Definition user_mem_unchanged cmem cmem' :=
  forall addr w t,
    PartMaps.get cmem addr = Some w@(encode (USER t)) <->
    PartMaps.get cmem' addr = Some w@(encode (USER t)).

Definition user_regs_unchanged cregs cregs' :=
  forall r w t,
    TotalMaps.get cregs r = w@(encode (USER t)) <->
    TotalMaps.get cregs' r = w@(encode (USER t)).

Import DoNotation.

Definition option_bool_to_bool (ob : option bool) :=
  match ob with
  | Some true => true
  | _ => false
  end.

Definition is_syscall_return (cst cst' : Concrete.state mt) :=
  in_kernel cst && in_user cst' && (option_bool_to_bool (
    do! i <- PartMaps.get (Concrete.mem cst) (common.val (Concrete.pc cst));
    do! di <- decode_instr (common.val i);
    Some (di == Jump _ (@ra mt ops)))).

Definition visible cst cst' :=
  in_user cst && in_user cst'.

(* Returns true iff our machine is at the beginning of a system call
and the cache says it is allowed to execute. To simplify this
definition, we assume that system calls are only allowed to begin with
Nop, which is consistent with how we've defined our symbolic handler
in rules.v. *)
Definition cache_allows_syscall (cst : Concrete.state mt) : bool :=
  match Symbolic.get_syscall table (common.val (Concrete.pc cst)) with
  | Some sc =>
    (* and the cache allows the system call to be executed *)
    let cmvec := Concrete.mkMVec (op_to_word NOP)
                                 (common.tag (Concrete.pc cst)) (encode (ENTRY (Symbolic.entry_tag sc)))
                                 Concrete.TNone Concrete.TNone Concrete.TNone in
    match Concrete.cache_lookup _ (Concrete.cache cst) masks cmvec with
    | Some _ => true
    | None => false
    end
  | None => false
  end.

Class kernel_code_correctness : Prop := {

(* BCP: Added some comments -- please check! *)
  handler_correct_allowed_case :
  forall mem mem' cmvec rvec reg cache old_pc int,
    (* If kernel invariant holds... *)
    ki mem reg cache int ->
    (* and calling the handler on the current m-vector succeeds and returns rvec... *)
    handler cmvec = Some rvec ->
    (* and storing the concrete representation of the m-vector yields new memory mem'... *)
    Concrete.store_mvec ops mem cmvec = Some mem' ->
    (* and the concrete rule cache is correct (in the sense that every
       rule it holds is exactly the concrete representations of
       some (mvec,rvec) pair in the relation defined by the [handler]
       function) ... *)
    cache_correct cache ->
    (* THEN if we start the concrete machine in kernel mode (i.e.,
       with the PC tagged TKernel) at the beginning of the fault
       handler (and with the current memory, and with the current PC
       in the return-addr register epc)) and let it run until it
       reaches a user-mode state st'... *)
    exists st',
      kernel_user_exec
        (Concrete.mkState mem' reg cache
                          (Concrete.fault_handler_start (t := mt) _)@Concrete.TKernel
                          old_pc)
        st' /\
      (* then the new cache is still correct... *)
      cache_correct (Concrete.cache st') /\
      (* and the new cache now contains a rule mapping mvec to rvec... *)
      Concrete.cache_lookup _ (Concrete.cache st') masks cmvec = Some (encode_rvec rvec) /\
      (* and the mvec has been tagged as kernel data (BCP: why is this important??) *)
      mvec_in_kernel (Concrete.mem st') /\
      (* and we've arrived at the return address that was in epc with
         unchanged user memory and registers... *)
      user_mem_unchanged mem (Concrete.mem st') /\
      user_regs_unchanged reg (Concrete.regs st') /\
      Concrete.pc st' = old_pc /\
      (* and the system call entry points are all tagged ENTRY (BCP:
         Why do we care, and if we do then why isn't this part of the
         kernel invariant?  Could user code possibly change it?) *)
      wf_entry_points (Concrete.mem st') /\
      (* and the kernel invariant still holds. *)
      ki (Concrete.mem st') (Concrete.regs st') (Concrete.cache st') int;

  handler_correct_disallowed_case :
  forall mem mem' cmvec reg cache old_pc int st',
    (* If kernel invariant holds... *)
    ki mem reg cache int ->
    (* and calling the handler on mvec FAILS... *)
    handler cmvec = None ->
    (* and storing the concrete representation of the m-vector yields new memory mem'... *)
    Concrete.store_mvec ops mem cmvec = Some mem' ->
    (* then if we start the concrete machine in kernel mode and let it
       run, it will never reach a user-mode state. *)
    in_kernel st' = false ->
    ~ exec (Concrete.step _ masks)
      (Concrete.mkState mem' reg cache
                        (Concrete.fault_handler_start (t := mt) _)@Concrete.TKernel
                        old_pc)
      st';

  syscalls_correct_allowed_case :
  forall amem areg apc tpc int
         amem' areg' apc' tpc' int'
         cmem creg cache epc sc,
    (* and the kernel invariant holds... *)
    ki cmem creg cache int ->
    (* and the USER-tagged portion of the concrete memory cmem
       corresponds to the abstract (symbolic??) memory amem... *)
    refine_memory amem cmem ->
    (* and the USER-tagged concrete registers in creg correspond to
       the abstract register set areg... *)
    refine_registers areg creg ->
    (* and the rule cache is correct... *)
    cache_correct cache ->
    (* and the mvec has been tagged as kernel data (BCP: again, why is this
       important... and why is it now part of the premises whereas
       upstairs it was part of the conclusion??) *)
    mvec_in_kernel cmem ->
    (* and the symbolic system call at addr is the function
       sc... (BCP: This would make more sense after the next
       hypothesis) *)
    Symbolic.get_syscall table apc = Some sc ->
    (* and running sc on the current abstract machine state reaches a
       new state with primes on everything... *)
    Symbolic.run_syscall sc (Symbolic.State amem areg apc@tpc int) = Some (Symbolic.State amem' areg' apc'@tpc' int') ->
    let cst := Concrete.mkState cmem
                                creg
                                cache
                                apc@(encode (USER tpc)) epc in

    cache_allows_syscall cst ->

    (* THEN if we start the concrete machine in kernel mode at the
       beginning of the corresponding system call code and let it run
       until it reaches a user-mode state with primes on everything... *)

    exists cmem' creg' cache' epc',
      user_kernel_user_step cst
                            (Concrete.mkState cmem' creg' cache'
                                              apc'@(encode (USER tpc')) epc') /\
      (* then the new concrete state is in the same relation as before
         with the new abstract state and the same invariants
         hold (BCP: Plus one more about ra!). *)
      refine_memory amem' cmem' /\
      refine_registers areg' creg' /\
      cache_correct cache' /\
      mvec_in_kernel cmem' /\
      ra_in_user creg' /\
      wf_entry_points cmem' /\
      ki cmem' creg' cache' int';

  syscalls_correct_disallowed_case :
  forall amem areg apc tpc int
         cmem creg cache epc sc
         cst',
    ki cmem creg cache int ->
    refine_memory amem cmem ->
    refine_registers areg creg ->
    cache_correct cache ->
    mvec_in_kernel cmem ->
    wf_entry_points cmem ->
    Symbolic.get_syscall table apc = Some sc ->
    Symbolic.run_syscall sc (Symbolic.State amem areg apc@tpc int) = None ->
    let cst := Concrete.mkState cmem
                                creg
                                cache
                                apc@(encode (USER tpc)) epc in
    cache_allows_syscall cst ->
    ~ user_kernel_user_step cst cst'

}.

Context {kcc : kernel_code_correctness}.

Lemma user_regs_unchanged_ra_in_user creg creg' :
  ra_in_user creg ->
  user_regs_unchanged creg creg' ->
  ra_in_user creg'.
Proof.
  unfold ra_in_user, word_lift.
  intros RA H.
  destruct (TotalMaps.get creg ra) as [v t] eqn:E.
  simpl in RA.
  destruct (decode t) as [t'|] eqn:E'; try discriminate.
  unfold is_user in RA. destruct t'; try discriminate.
  apply encodeK in E'. subst.
  apply H in E.
  rewrite E.
  simpl.
  now rewrite decodeK.
Qed.

End Refinement.
