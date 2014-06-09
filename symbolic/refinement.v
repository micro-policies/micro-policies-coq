Require Import List NPeano Arith Bool.
Require Import Coq.Classes.SetoidDec.
Require Import lib.utils lib.Coqlib.
Require Import concrete.common.
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
        {ap : Symbolic.symbolic_params mt}
        {aps : Symbolic.params_spec ap}
        {cp : Concrete.concrete_params mt}
        {cps : Concrete.params_spec cp}
        {e : @encodable (Symbolic.tag mt) mt}.

Ltac match_inv :=
  repeat match goal with
  | H : bind (fun x : _ => _) _ = Some _ |- _ =>
    apply bind_inv in H;
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
  | H : ?O = Some _ |- context[bind _ ?O] => rewrite H; simpl
  | H : True |- _ => clear H
  end.

Definition refine_memory (amem : Symbolic.memory mt) (cmem : Concrete.memory mt) :=
  forall w x t,
    Concrete.get_mem cmem w = Some x@(encode (USER t false)) <->
    Symbolic.get_mem amem w = Some x@t.

Definition refine_registers (areg : Symbolic.registers mt) (creg : Concrete.registers mt) :=
  forall n x t,
    Concrete.get_reg creg n = x@(encode (USER t false)) <->
    Symbolic.get_reg areg n = Some x@t.

Let in_kernel st :=
  let pct := common.tag (Concrete.pc st) in
  let i := Concrete.get_mem (Concrete.mem st) (common.val (Concrete.pc st)) in
  Concrete.is_kernel_tag _ pct
  || word_lift (fun x => is_call x) pct
  && match i with
     | Some _@it => it ==b encode ENTRY
     | None => false
     end.
Hint Unfold in_kernel.
Let user_pc_and_instr pct it :=
  word_lift (fun t =>
               is_user t
               && (negb (is_call t) || negb (it ==b encode ENTRY)))
            pct.

Let in_user st :=
  let pct := common.tag (Concrete.pc st) in
  let i := Concrete.get_mem (Concrete.mem st) (common.val (Concrete.pc st)) in
  word_lift (fun t =>
               is_user t
               && (negb (is_call t)
                   || negb match i with
                           | Some _@it =>
                             it ==b encode ENTRY
                           | None => false
                           end))
            pct.
Hint Unfold in_user.

Let handler := handler (fun x => Symbolic.handler x).

Definition cache_correct cache :=
  forall cmvec crvec,
    word_lift (fun x => is_user x) (Concrete.ctpc cmvec) = true ->
    Concrete.cache_lookup ops cache masks cmvec = Some crvec ->
    exists mvec rvec,
      cmvec = encode_mvec mvec /\
      crvec = encode_rvec rvec /\
      handler mvec = Some rvec.

Definition in_mvec addr := In addr (Concrete.mvec_fields _).

Definition mvec_in_kernel cmem :=
  forall addr,
    in_mvec addr ->
    exists w, Concrete.get_mem cmem addr = Some w@Concrete.TKernel.

Hypothesis kernel_tag_correct :
  Concrete.TKernel = encode KERNEL.

Lemma store_mvec_mvec_in_kernel cmem cmem' mvec :
  Concrete.store_mvec ops cmem mvec = Some cmem' ->
  mvec_in_kernel cmem'.
Proof.
  unfold Concrete.store_mvec, mvec_in_kernel, in_mvec.
  intros H addr IN.
  destruct (PartMaps.get_upd_list_in  _ _ _ H IN)
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
  simpl map. intros addr IN.
  apply DEF in IN.
  destruct IN.
  eauto.
Qed.

Definition ra_in_user creg :=
  word_lift (fun x => is_user_data x)
            (common.tag (Concrete.get_reg creg ra)) = true.
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
    forall regs mem1 mem2 cache addr w1 ut b w2 int
           (KINV : kernel_invariant_statement mem1 regs cache int)
           (GET : Concrete.get_mem mem1 addr = Some w1@(encode (USER ut b)))
           (UPD : Concrete.upd_mem mem1 addr w2 = Some mem2),
      kernel_invariant_statement mem2 regs cache int;

  kernel_invariant_upd_reg :
    forall mem regs cache r w1 ut1 b1 w2 ut2 b2 int
           (KINV : kernel_invariant_statement mem regs cache int)
           (GET : Concrete.get_reg regs r = w1@(encode (USER ut1 b1))),
      kernel_invariant_statement mem (Concrete.upd_reg regs r w2@(encode (USER ut2 b2))) cache int;

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
  destruct (decode tg) as [[ut b| |]|] eqn:E; try discriminate.
  intros _.
  apply encodeK in E.
  unfold equiv_decb.
  destruct (tg == Concrete.TKernel) as [E' | NEQ']; simpl in *; subst; eauto.
  rewrite kernel_tag_correct in E'.
  now apply encode_inj in E'.
Qed.

Lemma in_user_in_kernel :
  forall st, in_user st = true -> in_kernel st = false.
Proof.
  unfold in_user, in_kernel, word_lift, Concrete.is_kernel_tag.
  intros st H.
  destruct (decode (common.tag (Concrete.pc st)))
    as [[t [|]| |]|] eqn:DEC; simpl in *; try discriminate;
  apply encodeK in DEC.
  - rewrite <- DEC.
    rewrite kernel_tag_correct.
    erewrite eq_tag_eq_word. simpl.
    now rewrite negb_true_iff in H.
  - rewrite <- DEC.
    rewrite kernel_tag_correct.
    now erewrite eq_tag_eq_word.
Qed.

Variable table : list (Symbolic.syscall mt).

Definition wf_entry_points cmem :=
  forall addr,
    (exists sc, Symbolic.get_syscall table addr = Some sc) <->
    match Concrete.get_mem cmem addr with
    | Some _@it => it ==b encode ENTRY
    | None => false
    end = true.

Definition refine_state (st : Symbolic.state mt) (st' : Concrete.state mt) :=
  in_user st' = true /\
  let '(Symbolic.State mem regs pc@tpc int) := st in
  let 'Concrete.mkState mem' regs' cache pc'@tpc' epc := st' in
  pc = pc' /\
  match decode tpc' with
  | Some (USER tpc' _) => tpc' = tpc
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
  Concrete.get_mem cmem addr = Some v@(encode (USER t false)) ->
  Concrete.upd_mem cmem addr v'@(encode (USER t' false)) = Some cmem' ->
  exists amem',
    Symbolic.upd_mem amem addr v'@t' = Some amem' /\
    refine_memory amem' cmem'.
Proof.
  intros MEM GET UPD.
  assert (GET' := proj1 (MEM _ _ _) GET).
  destruct (PartMaps.upd_defined v'@t' GET') as [amem' UPD'].
  do 2 eexists; eauto.
  intros addr' w'.
  destruct (addr' == addr) as [EQ | NEQ]; simpl in *; subst.
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
  Concrete.get_mem cmem addr = Some v@(encode (USER t false)) ->
  Concrete.upd_mem cmem addr v'@(encode (USER t' false)) = Some cmem' ->
  wf_entry_points cmem'.
Proof.
  unfold wf_entry_points.
  intros WF GET UPD addr'.
  split; intros H.
  - rewrite WF in H.
    destruct (Concrete.get_mem cmem addr') as [[v'' t'']|] eqn:MEM; try discriminate.
    erewrite PartMaps.get_upd_neq; eauto using Concrete.mem_axioms.
    { now rewrite MEM. }
    intros ?. subst addr'.
    assert (EQ : t'' = encode (USER t false)) by congruence. subst.
    rewrite eqb_true_iff in H.
    now apply encode_inj in H.
  - apply WF. clear WF.
    destruct (Concrete.get_mem cmem' addr') as [[v'' t'']|] eqn:GET'; try discriminate.
    erewrite PartMaps.get_upd_neq in GET'; eauto using Concrete.mem_axioms.
    { now rewrite GET'. }
    intros ?. subst addr'.
    erewrite PartMaps.get_upd_eq in GET'; eauto using Concrete.mem_axioms.
    assert (EQ : t''= encode (USER t' false)) by congruence. subst.
    simpl in H.
    rewrite eqb_true_iff in H.
    now apply encode_inj in H.
Qed.

Lemma mvec_in_kernel_user_upd cmem cmem' addr v v' t t' :
  mvec_in_kernel cmem ->
  Concrete.get_mem cmem addr = Some v@(encode (USER t false)) ->
  Concrete.upd_mem cmem addr v'@(encode (USER t' false)) = Some cmem' ->
  mvec_in_kernel cmem'.
Proof.
  intros MVEC GET UPD.
  intros addr' H.
  specialize (MVEC addr' H). destruct MVEC as [w' KER].
  assert (NEQ : addr' <> addr).
  { intros E. subst addr'.
    assert (CONTRA : Concrete.TKernel = encode (USER t false))
      by congruence.
    rewrite kernel_tag_correct in CONTRA.
    now apply encode_inj in CONTRA. }
  rewrite (PartMaps.get_upd_neq NEQ UPD).
  eauto.
Qed.

Lemma mvec_in_kernel_kernel_upd cmem cmem' addr w :
  mvec_in_kernel cmem ->
  Concrete.upd_mem cmem addr w@Concrete.TKernel = Some cmem' ->
  mvec_in_kernel cmem'.
Proof.
  intros MVEC UPD addr' IN.
  destruct (addr' == addr) as [? | NEQ]; simpl in *; subst.
  - erewrite PartMaps.get_upd_eq; eauto using Concrete.mem_axioms.
  - erewrite (PartMaps.get_upd_neq NEQ UPD).
    now apply MVEC.
Qed.

Lemma refine_memory_upd' amem amem' cmem addr v t :
  refine_memory amem cmem ->
  Symbolic.upd_mem amem addr v@t = Some amem' ->
  exists cmem',
    Concrete.upd_mem cmem addr v@(encode (USER t false)) = Some cmem' /\
    refine_memory amem' cmem'.
Proof.
  intros MEM UPD.
  destruct (PartMaps.upd_inv UPD) as [[w' t'] GET].
  apply MEM in GET.
  eapply PartMaps.upd_defined in GET; auto using Concrete.mem_axioms.
  destruct GET as [cmem' UPD'].
  eexists. split; eauto.
  intros addr' w'' t''.
  destruct (addr' == addr) as [EQ | NEQ]; simpl in *; subst.
  - rewrite (PartMaps.get_upd_eq UPD').
    rewrite (PartMaps.get_upd_eq UPD).
    split; try congruence.
    intros ?.
    assert (E : USER t false = USER t'' false); try congruence.
    eapply encode_inj. congruence.
  - rewrite (PartMaps.get_upd_neq NEQ UPD).
    rewrite (PartMaps.get_upd_neq NEQ UPD').
    now apply MEM.
Qed.

Lemma refine_registers_upd areg creg r v v' t t' :
  refine_registers areg creg ->
  Concrete.get_reg creg r = v@(encode (USER t false)) ->
  exists areg',
    Symbolic.upd_reg areg r v'@t' = Some areg' /\
    refine_registers areg' (Concrete.upd_reg creg r v'@(encode (USER t' false))).
Proof.
  intros REG GET.
  assert (GET' := proj1 (REG _ _ _) GET).
  assert (NEW := PartMaps.upd_defined v'@t' GET').
  destruct NEW as [areg' UPD].
  eexists. split; eauto.
  intros r' v'' t''.
  destruct (r' == r) as [EQ | NEQ]; simpl in *; subst.
  - rewrite (TotalMaps.get_upd_eq (Concrete.reg_axioms (t := mt))).
    rewrite (PartMaps.get_upd_eq UPD).
    split; try congruence.
    intros ?.
    assert (USER t' false = USER t'' false); try congruence.
    eapply encode_inj; congruence.
  - rewrite (TotalMaps.get_upd_neq (Concrete.reg_axioms (t := mt))); trivial.
    rewrite (PartMaps.get_upd_neq NEQ UPD).
    now apply REG.
Qed.

Lemma refine_registers_upd' areg areg' creg r v t :
  refine_registers areg creg ->
  Symbolic.upd_reg areg r v@t = Some areg' ->
  refine_registers areg' (Concrete.upd_reg creg r v@(encode (USER t false))).
Proof.
  intros REF UPD r' v' t'.
  destruct (r' == r) as [|NEQ]; simpl in *.
  - subst r'.
    rewrite (TotalMaps.get_upd_eq (Concrete.reg_axioms (t := mt))).
    rewrite (PartMaps.get_upd_eq UPD).
    split; try congruence.
    intros ?.
    assert (USER t' false = USER t false); try congruence.
    eapply encode_inj; try congruence.
  - rewrite (TotalMaps.get_upd_neq (Concrete.reg_axioms (t := mt))); trivial.
    rewrite (PartMaps.get_upd_neq NEQ UPD).
    now apply REF.
Qed.

Lemma ra_in_user_upd creg r v t :
  ra_in_user creg ->
  ra_in_user (Concrete.upd_reg creg r v@(encode (USER t false))).
Proof.
  unfold ra_in_user.
  destruct (r == ra) as [|NEQ]; simpl in *; autounfold.
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

Inductive miss_step cst cst' : Prop :=
| ks_intro kst
           (USER : in_user cst = true)
           (STEP : Concrete.step _ masks cst kst)
           (EXEC : kernel_user_exec kst cst').

Definition user_step cst cst' :=
  hit_step cst cst' \/ miss_step cst cst'.

Import Vector.VectorNotations.

Lemma analyze_cache cache cmvec crvec op :
  cache_correct cache ->
  Concrete.cache_lookup _ cache masks cmvec = Some crvec ->
  user_pc_and_instr (Concrete.ctpc cmvec) (Concrete.cti cmvec) = true ->
  Concrete.cop cmvec = op_to_word op ->
  match nfields op as fs return (_ -> _ -> mvec_fields _ fs -> _) -> Prop with
  | Some fs => fun mk =>
    exists tpc ic ti (ts : Vector.t _ (fst fs)) trpc tr,
    Concrete.ctpc cmvec = encode (USER tpc ic) /\
    Concrete.cti  cmvec = encode (USER ti false) /\
    crvec = Concrete.mkRVec (encode (USER trpc (match op with JAL => true | _ => false end)))
                            (encode (USER tr false)) /\
    Symbolic.handler (mk tpc ti ts) = Some (mkRVec trpc tr) /\
    match fst fs as n return Vector.t _ n -> Prop with
    | 0 => fun ts => ts = []
    | 1 => fun ts => exists t1,
                       ts = [t1] /\
                       Concrete.ct1 cmvec = encode (USER t1 false)
    | 2 => fun ts => exists t1 t2,
                       ts = [t1; t2] /\
                       Concrete.ct1 cmvec = encode (USER t1 false) /\
                       Concrete.ct2 cmvec = encode (USER t2 false)
    | 3 => fun ts => exists t1 t2 t3,
                       ts = [t1; t2; t3] /\
                       Concrete.ct1 cmvec = encode (USER t1 false) /\
                       Concrete.ct2 cmvec = encode (USER t2 false) /\
                       Concrete.ct3 cmvec = encode (USER t3 false)
    | _ => fun _ => False
    end ts
  | None => fun _ => False
  end (mkMVec op).
Proof.
  intros CACHE LOOKUP INUSER EQ.
  assert (USERPC := word_lift_impl _ _ _ (fun t H => proj1 (andb_prop _ _ H)) INUSER).
  destruct (CACHE cmvec crvec USERPC LOOKUP)
    as ([op' tpc ti ts] & [trpc tr] & ? & ? & HIT). subst.
  unfold encode_mvec, encode_rvec in *. simpl in *.
  apply op_to_word_inj in EQ. subst op'.
  destruct op; simpl in *; match_inv;
  try solve [
    unfold user_pc_and_instr, word_lift in INUSER;
    rewrite eqb_refl in INUSER;
    now rewrite decodeK in INUSER
  ];
  try match goal with
  | rvec : RVec _ |- _ => destruct rvec
  end;
  simpl in *;
  repeat (
    match goal with
    | ts : Vector.t _ 0 |- _ => induction ts using Vector.case0
    | ts : Vector.t _ (S _) |- _ => induction ts using caseS
    | |- context[decode (encode _)] => rewrite decodeK
    end; simpl
  );
  simpl in *;
  do 9 eexists; repeat (split; eauto); simpl; eauto;
  try solve [match_inv; trivial];

  (* match_inv is to brutal with equalities involving dependent types *)
  repeat match goal with
  | H : bind _ ?X = Some _ |- _ =>
    match X with
    | context[match ?a with _ => _ end] =>
      destruct a as [? [|]| |];
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
  rewrite eqb_refl in INUSER; try apply eq_wordP.
  simpl in INUSER. discriminate.
Qed.

Ltac analyze_cache :=
  match goal with
  | LOOKUP : Concrete.cache_lookup _ ?cache _ ?mvec = Some ?rvec,
    PC     : Concrete.get_mem _ ?pc = Some ?i@_,
    INST   : decode_instr ?i = Some _,
    INUSER : in_user (Concrete.mkState _ _ _ ?pc@_ _) = true,
    CACHE  : cache_correct ?cache |- _ =>
    unfold in_user, in_kernel in INUSER; simpl in INUSER; rewrite PC in INUSER;
    assert (CACHEHIT := analyze_cache mvec _ CACHE LOOKUP INUSER eq_refl);
    simpl in CACHEHIT;
    repeat match type of CACHEHIT with
    | exists _, _ => destruct CACHEHIT as [? CACHEHIT]
    | _ /\ _ => destruct CACHEHIT as [? CACHEHIT]
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

Lemma valid_pcs st st' :
  Concrete.step _ masks st st' ->
  cache_correct (Concrete.cache st) ->
  in_user st = true ->
  match decode (common.tag (Concrete.pc st')) with
  | Some (USER _ _) => true
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

  simpl in *; try rewrite kernel_tag_correct; now rewrite decodeK.

Qed.


Ltac current_instr_opcode :=
  match goal with
  | H : decode_instr _ = Some ?instr |- _ =>
    let op := (eval compute in (opcode_of instr)) in
    op
  end.

Lemma in_user_no_system_call st t :
  in_user st = true ->
  common.tag (Concrete.pc st) = encode (USER t true) ->
  wf_entry_points (Concrete.mem st) ->
  Symbolic.get_syscall table (common.val (Concrete.pc st)) = None.
Proof.
  unfold in_user, word_lift.
  intros INUSER ISCALL WF.
  rewrite ISCALL in INUSER.
  rewrite decodeK in INUSER. simpl in *.
  destruct (Symbolic.get_syscall table (common.val (Concrete.pc st)))
    as [sc|] eqn:EQ; trivial.
  assert (H := proj1 (WF (common.val (Concrete.pc st))) (ex_intro _ _ EQ)).
  destruct (Concrete.get_mem (Concrete.mem st) (val (Concrete.pc st)))
    as [[v t']|] eqn:EQ'; try discriminate.
  rewrite eqb_true_iff in H. subst.
  rewrite eqb_refl in INUSER.
  now simpl in *.
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

Lemma hit_simulation ast cst cst' :
  refine_state ast cst ->
  hit_step cst cst' ->
  exists ast',
    Symbolic.step table ast ast' /\
    refine_state ast' cst'.
Proof.
  intros REF [INUSER INUSER' STEP].
  destruct ast as [amem areg [apc tapc] int].
  inv STEP; simpl in REF;
  destruct REF
    as (_ & ? & ? & REFM & REFR & CACHE & MVEC & RA & WFENTRYPOINTS & KINV);
  subst apc;
  unfold Concrete.next_state_reg, Concrete.next_state_reg_and_pc,
         Concrete.next_state_pc, Concrete.next_state in *;
  simpl in *;
  try rewrite KER in NEXT; simpl in *;

  match_inv;

  analyze_cache;

  repeat match goal with
  | MEM : Concrete.get_mem ?cmem ?addr = Some _ |- _ =>
    match goal with
    | _ : Symbolic.get_mem _ addr = Some _ |- _ => fail 1
    | |- _ => idtac
    end;
    pose proof (proj1 (REFM _ _ _) MEM)
  end;

  try match goal with
  | OLD : Concrete.get_reg ?reg ?r = _
    |- context[Concrete.upd_reg ?reg ?r ?v@(encode (USER ?t false))] =>
    (destruct (refine_registers_upd _ v _ t REFR OLD) as (? & ? & ?);
     pose proof (kernel_invariant_upd_reg ki _ _ _ _ _ _ v t false _ KINV OLD))
    || let op := current_instr_opcode in fail 3 op
  end;

  try match goal with
  | GET : Concrete.get_mem _ ?addr = Some _,
    UPD : Concrete.upd_mem _ ?addr _ = Some _ |- _ =>
    (destruct (refine_memory_upd _ _ _ _ REFM GET UPD) as (? & ? & ?);
     pose proof (wf_entry_points_user_upd _ _ _ _ WFENTRYPOINTS GET UPD);
     pose proof (mvec_in_kernel_user_upd _ _ _ _ MVEC GET UPD))
    || let op := current_instr_opcode in fail 3 op
  end;

  repeat match goal with
  | creg : Concrete.registers mt,
    H : Concrete.get_reg ?creg ?r = _ |- _ =>
    apply REFR in H
  end;

  try match goal with
  | INST : decode_instr _ = Some (Jal _ _) |- _ =>
    pose proof (in_user_no_system_call _ _ INUSER' eq_refl WFENTRYPOINTS)
  end;

  solve [eexists; split;
         (try econstructor (
                solve [eauto;
                       repeat autounfold;
                       repeat match goal with
                       | H : ?x = _ |- context[?x] =>
                         rewrite H; simpl; clear H
                       end; reflexivity]));
         repeat (split; eauto using ra_in_user_upd); now rewrite decodeK].
Qed.

Lemma initial_handler_state cst kst :
  forall (ISUSER : in_user cst = true)
         (NUSER : word_lift (fun t => is_user t)
                            (common.tag (Concrete.pc kst)) = false)
         (CACHE : cache_correct (Concrete.cache cst))
         (STEP : Concrete.step _ masks cst kst),
    exists cmem' mvec,
      Concrete.store_mvec ops (Concrete.mem cst) mvec = Some cmem' /\
      kst = Concrete.mkState cmem'
                             (Concrete.regs cst)
                             (Concrete.cache cst)
                             (Concrete.fault_handler_start (t := mt))@Concrete.TKernel
                             (Concrete.pc cst).
Proof.
  intros.
  inv STEP;
  unfold Concrete.next_state_reg, Concrete.next_state_reg_and_pc,
         Concrete.next_state_pc, Concrete.next_state,
         Concrete.miss_state in *;
  match_inv;
  try analyze_cache;
  simpl in *;
  try solve [repeat simpl_word_lift; simpl in *; discriminate | eauto].
Qed.

Definition user_mem_unchanged cmem cmem' :=
  forall addr w t,
    Concrete.get_mem cmem addr = Some w@(encode (USER t false)) <->
    Concrete.get_mem cmem' addr = Some w@(encode (USER t false)).

Definition user_regs_unchanged cregs cregs' :=
  forall r w t,
    Concrete.get_reg cregs r = w@(encode (USER t false)) <->
    Concrete.get_reg cregs' r = w@(encode (USER t false)).

(* XXX: a bit of a lie now, given that the kernel can now return to a system call *)
Hypothesis handler_correct_allowed_case :
  forall mem mem' cmvec rvec reg cache old_pc int,
    ki mem reg cache int ->
    match decode_mvec cmvec with
    | Some mvec => handler mvec
    | None => None
    end = Some rvec ->
    Concrete.store_mvec ops mem cmvec = Some mem' ->
    cache_correct cache ->
    exists st',
      kernel_user_exec
        (Concrete.mkState mem' reg cache
                          (Concrete.fault_handler_start (t := mt))@Concrete.TKernel
                          old_pc)
        st' /\
      cache_correct (Concrete.cache st') /\
      Concrete.cache_lookup _ (Concrete.cache st') masks cmvec = Some (encode_rvec rvec) /\
      mvec_in_kernel (Concrete.mem st') /\
      user_mem_unchanged mem (Concrete.mem st') /\
      user_regs_unchanged reg (Concrete.regs st') /\
      Concrete.pc st' = old_pc /\
      wf_entry_points (Concrete.mem st') /\
      ki (Concrete.mem st') (Concrete.regs st') (Concrete.cache st') int.

Hypothesis handler_correct_disallowed_case :
  forall mem mem' cmvec reg cache old_pc int st',
    ki mem reg cache int ->
    match decode_mvec cmvec with
    | Some mvec => handler mvec
    | None => None
    end = None ->
    Concrete.store_mvec ops mem cmvec = Some mem' ->
    in_kernel st' = false ->
    ~ exec (Concrete.step _ masks)
      (Concrete.mkState mem' reg cache
                        (Concrete.fault_handler_start (t := mt))@Concrete.TKernel
                        old_pc)
      st'.

Hypothesis syscalls_correct_allowed_case :
  forall amem areg apc tpc amem' areg' apc' tpc' cmem creg cache old_pc epc addr sc
         tpc'' tpc''' ic int int', (* XXX: Maybe quantifying over tpcs and ic is asking too much? *)
    ki cmem creg cache int ->
    refine_memory amem cmem ->
    refine_registers areg creg ->
    cache_correct cache ->
    mvec_in_kernel cmem ->
    wf_entry_points cmem ->
    Symbolic.get_syscall table addr = Some sc ->
    Symbolic.sem sc (Symbolic.State amem areg apc@tpc int) = Some (Symbolic.State amem' areg' apc'@tpc' int') ->
    exists cmem' creg' cache' epc',
      kernel_user_exec (Concrete.mkState cmem
                                         (Concrete.upd_reg creg ra
                                                           (old_pc + Z_to_word 1)%w@(encode (USER tpc'' ic)))
                                         cache
                                         addr@(encode (USER tpc''' true)) epc)
                       (Concrete.mkState cmem' creg' cache'
                                         apc'@(encode (USER tpc' false))
                                         epc') /\
      refine_memory amem' cmem' /\
      refine_registers areg' creg' /\
      cache_correct cache' /\
      mvec_in_kernel cmem' /\
      ra_in_user creg' /\
      wf_entry_points cmem' /\
      ki cmem' creg' cache' int'.

Hypothesis syscalls_correct_disallowed_case :
  forall ast cst cst' cst'' addr sc,
    refine_state ast cst ->
    Symbolic.get_syscall table addr = Some sc ->
    Symbolic.sem sc ast = None ->
    Concrete.step _ masks cst cst' ->
    common.val (Concrete.pc cst') = addr ->
    ~ kernel_user_exec cst' cst''.

Lemma user_regs_unchanged_ra_in_user creg creg' :
  ra_in_user creg ->
  user_regs_unchanged creg creg' ->
  ra_in_user creg'.
Proof.
  unfold ra_in_user, word_lift.
  intros RA H.
  destruct (Concrete.get_reg creg ra) as [v t] eqn:E.
  simpl in RA.
  destruct (decode t) as [t'|] eqn:E'; try discriminate.
  unfold is_user in RA. destruct t'; try discriminate.
  apply encodeK in E'. subst. simpl in RA.
  rewrite negb_true_iff in RA. subst.
  apply H in E.
  rewrite E.
  simpl.
  now rewrite decodeK.
Qed.

Lemma kernel_user_exec_determ k s1 s2 :
  kernel_user_exec k s1 ->
  kernel_user_exec k s2 ->
  s1 = s2.
Proof.
  unfold kernel_user_exec. intros EXEC1 EXEC2.
  eapply exec_until_determ; eauto.
  - clear. intros s s1 s2.
    do 2 rewrite <- stepP in *. congruence.
  - clear. intros s H1 H2. simpl in *. congruence.
  - clear. intros s H1 H2. simpl in *. congruence.
Qed.

Lemma state_on_syscalls st st' :
  forall (ISUSER : in_user st = true)
         (CACHE : cache_correct (Concrete.cache st))
         (ISCALL : word_lift (fun t => is_call t) (common.tag (Concrete.pc st')) = true)
         (STEP : Concrete.step _ masks st st'),
    Concrete.mem st' = Concrete.mem st /\
    Concrete.cache st' = Concrete.cache st /\
    exists r i tpc ic ti t1 old told trpc tr,
      Concrete.regs st' =
      Concrete.upd_reg (Concrete.regs st) ra
                       (common.val (Concrete.pc st) + Z_to_word 1)%w@(encode (USER tr false)) /\
      common.tag (Concrete.pc st') = encode (USER trpc true) /\
      common.tag (Concrete.pc st) = encode (USER tpc ic) /\
      Concrete.get_mem (Concrete.mem st) (common.val (Concrete.pc st)) =
      Some i@(encode (USER ti false)) /\
      decode_instr i = Some (Jal _ r) /\
      Concrete.get_reg (Concrete.regs st) r = (common.val (Concrete.pc st'))@(encode (USER t1 false)) /\
      Concrete.get_reg (Concrete.regs st) ra = old@(encode (USER told false)) /\
      Concrete.cache_lookup _ (Concrete.cache st) masks
                            (encode_mvec (mvec_of_umvec ic (mkMVec JAL tpc ti [t1; told]))) =
      Some (encode_rvec (rvec_of_urvec JAL (mkRVec trpc tr))).
Proof.
  intros.
  inv STEP;
  unfold Concrete.next_state_reg, Concrete.next_state_reg_and_pc,
         Concrete.next_state_pc, Concrete.next_state,
         Concrete.miss_state in *;
  match_inv;
  try analyze_cache;
  simpl in *;
  try rewrite kernel_tag_correct in *;
  try solve [repeat simpl_word_lift; simpl in *; discriminate].
  repeat (split; eauto).
  unfold encode_mvec, encode_rvec, mvec_of_umvec, rvec_of_urvec. simpl.
  do 10 eexists.
  repeat (split; eauto).
Qed.

Lemma miss_simulation ast cst cst' :
  refine_state ast cst ->
  miss_step cst cst' ->
  refine_state ast cst' \/
  exists ast', Symbolic.step table ast ast' /\
               refine_state ast' cst'.
Proof.
  intros REF [kst ISUSER STEP KEXEC].
  assert (KER : in_kernel kst = true).
  { destruct KEXEC as [? EXEC]. exact (restricted_exec_fst EXEC). }
  destruct ast as [amem areg [apc tapc] int], cst as [cmem cregs cache [cpc cpct] cepc].
  assert (REF' := REF).
  destruct REF' as (_ & ? & Ht & REFM & REFR & CACHE & MVEC & RA & WFENTRYPOINTS & KINV).
  destruct (decode cpct) as [[tpc' ? | | ]|] eqn:TAG; try solve [intuition].
  subst cpc tpc'.
  unfold in_kernel in KER.
  apply orb_true_iff in KER.
  destruct KER as [FAULT | SYSCALL].
  - left.
    assert (NUSER : word_lift (fun t => is_user t) (common.tag (Concrete.pc kst)) = false).
    { destruct (word_lift (fun t => is_user t) (common.tag (Concrete.pc kst))) eqn:EQ; trivial.
      apply is_user_pc_tag_is_kernel_tag in EQ. congruence. }
    destruct (initial_handler_state ISUSER NUSER CACHE STEP)
      as (cmem' & mvec & STORE & ?). subst. simpl in *.
    destruct (match decode_mvec mvec with
              | Some mvec => handler mvec
              | None => None
              end) as [rvec|] eqn:HANDLER.
    + destruct (handler_correct_allowed_case cmem mvec cregs apc@cpct int KINV HANDLER STORE CACHE)
        as (cst'' & KEXEC' & CACHE' & LOOKUP & MVEC' &
            HMEM & HREGS & HPC & WFENTRYPOINTS' & KINV').
      assert (EQ := kernel_user_exec_determ KEXEC' KEXEC). subst cst''.
      destruct cst' as [cmem'' cregs'' cache' ? ?]. simpl in *. subst.
      unfold refine_state.
      repeat match goal with
      | |- _ /\ _ => split; eauto using user_regs_unchanged_ra_in_user
      end.
      * unfold in_user, word_lift in *. simpl in *.
        rewrite TAG in ISUSER. rewrite TAG.
        apply andb_true_iff in ISUSER.
        destruct ISUSER as [H ISUSER]. rewrite H. clear H. simpl.
        rewrite orb_true_iff in ISUSER.
        destruct ISUSER as [ISUSER | ISUSER].
        { simpl in ISUSER. now rewrite ISUSER. }
        destruct (Concrete.get_mem cmem'' apc) as [[i it]|] eqn:GET;
          [|apply orb_true_r].
        unfold equiv_decb.
        destruct (equiv_dec it (encode ENTRY)); [|apply orb_true_r]; simpl in *; subst.
        generalize (proj2 (WFENTRYPOINTS' apc)).
        rewrite GET. rewrite eqb_refl. intros DEF.
        specialize (DEF eq_refl).
        apply WFENTRYPOINTS in DEF.
        now rewrite DEF in ISUSER.
      * now rewrite TAG.
      * clear - ISUSER MVEC STORE REFM HMEM.
        intros addr w t. unfold user_mem_unchanged in *.
        rewrite <- HMEM. apply REFM.
      * clear - REFR HREGS.
        intros r w t. unfold user_regs_unchanged in *.
        rewrite <- HREGS.
        apply REFR.
    + assert (EXEC : forall st st',
                       kernel_user_exec st st' ->
                       exec (Concrete.step _ masks) st st').
      { clear. intros st st' EXEC. destruct EXEC as [kst' EXEC].
        apply restricted_exec_weaken in EXEC.
        apply restricted_exec_trans with kst'; eauto. }
      assert (ISUSER' : in_kernel cst' = false).
      { destruct KEXEC. eauto. }
      apply EXEC in KEXEC.
      destruct (handler_correct_disallowed_case cmem mvec int KINV HANDLER STORE ISUSER' KEXEC).
  - right. rewrite andb_true_iff in SYSCALL. destruct SYSCALL as [S1 S2].
    destruct (Concrete.get_mem (Concrete.mem kst) (common.val (Concrete.pc kst)))
      as [[i it]|] eqn:GET; try discriminate.
    rewrite eqb_true_iff in S2. subst.
    exploit state_on_syscalls; eauto. simpl.
    intros (EM & ER & r & w & tpc & ic & ti & t1 & old & told & trpc & tr &
            EC & MEM & ? & INST & DEC & PC' & RA' & LOOKUP').
    rewrite EM in GET. subst.
    assert (SYSCALL : exists sc, Symbolic.get_syscall table (common.val (Concrete.pc kst)) = Some sc).
    { unfold wf_entry_points in WFENTRYPOINTS. rewrite WFENTRYPOINTS.
      rewrite GET. apply eqb_refl. }
    destruct SYSCALL as [sc GETSC].
    destruct (Symbolic.sem sc (Symbolic.State amem areg apc@tapc int)) as [ast'|] eqn:SCEXEC.
    + destruct ast' as [amem' areg' [apc' tapc'] int'].
      destruct kst as [kmem kregs kcache [kpc kpct] kepc]. subst. simpl in *.
      rewrite decodeK in TAG. simpl in TAG. inv TAG.
      exploit syscalls_correct_allowed_case; eauto.
      intros (cmem' & creg' & cache' & pct' & EXEC' &
              REFM' & REFR' & CACHE' & MVEC' & RA'' & WFENTRYPOINTS' & KINV').
      generalize (kernel_user_exec_determ KEXEC EXEC'). intros ?. subst.
      exploit CACHE; try eassumption.
      { simpl.
        unfold word_lift.
        now rewrite decodeK. }
      intros (mvec & rvec & E1 & E2 & HANDLER).
      apply encode_mvec_inj in E1; eauto. subst.
      unfold handler in HANDLER. simpl in HANDLER.
      match_inv.
      exists (Symbolic.State amem' areg' apc'@tapc' int'). split; eauto.
      eapply Symbolic.step_syscall; eauto.
      * apply REFM in INST; eauto.
      * apply REFR. apply PC'.
      * apply REFR. eauto.
      * unfold refine_state, in_user, word_lift. simpl.
        rewrite decodeK. simpl.
        repeat (split; eauto).
    + destruct (syscalls_correct_disallowed_case REF GETSC SCEXEC STEP eq_refl KEXEC).
Qed.

Lemma user_step_simulation ast cst cst' :
  refine_state ast cst ->
  user_step cst cst' ->
  exists ast',
    exec (Symbolic.step table) ast ast' /\
    refine_state ast' cst'.
Proof.
  intros REF [HIT | MISS].
  - exploit hit_simulation; eauto.
    intros (ast' & STEP & REF').
    autounfold; eauto.
  - exploit miss_simulation; eauto.
    intros [H | H]; eauto.
    destruct H as (ast' & H1 & H2).
    eauto using exec_one.
Qed.

Lemma user_exec_refinement ast cst cst' :
  refine_state ast cst ->
  exec user_step cst cst' ->
  exists ast',
    exec (Symbolic.step table) ast ast' /\
    refine_state ast' cst'.
Proof.
  intros REF EXEC.
  gdep ast. induction EXEC as [|? ? ? _ STEP EXEC IH]; autounfold; eauto.
  intros.
  exploit user_step_simulation; eauto. intros (? & ? & ?).
  exploit IH; eauto. intros (ast' & ? & ?).
  eexists ast'. split; eauto.
Qed.

Lemma user_into_kernel ast cst cst' :
  refine_state ast cst ->
  Concrete.step _ masks cst cst' ->
  in_user cst' = false ->
  in_kernel cst' = true.
Proof.
  destruct ast as [? ? [? ?]], cst as [? ? ? [? ?] ?].
  intros REF STEP NUSER.
  destruct (in_kernel cst') eqn:NKERNEL; trivial.
  unfold in_user in NUSER.
  unfold in_kernel, Concrete.is_kernel_tag in NKERNEL.
  rewrite kernel_tag_correct in NKERNEL.
  destruct REF as (INUSER & ? & ? & ? & ? & CACHE & ?).
  assert (PCS := valid_pcs STEP CACHE INUSER).
  unfold word_lift in *.
  destruct (decode (common.tag (Concrete.pc cst'))) as [[t [|]| |]|] eqn:DEC;
  try discriminate; simpl in *;
  apply encodeK in DEC.
  - rewrite <- DEC in NKERNEL.
    erewrite eq_tag_eq_word in NKERNEL.
    simpl in NKERNEL.
    rewrite negb_false_iff in NUSER.
    congruence.
  - rewrite DEC in NKERNEL.
    now rewrite eqb_refl in NKERNEL.
Qed.

Lemma backwards_refinement_aux cst cst' (EXEC : exec (Concrete.step _ masks) cst cst') :
  in_user cst' = true ->
  (in_user cst = true ->
   forall ast,
     refine_state ast cst ->
     exists ast',
       exec (Symbolic.step table) ast ast' /\
       refine_state ast' cst') /\
  (in_kernel cst = true ->
   forall ast cst0 kst,
     refine_state ast cst0 ->
     Concrete.step _ masks cst0 kst ->
     kernel_exec kst cst ->
     exists ast',
       exec (Symbolic.step table) ast ast' /\
       refine_state ast' cst').
Proof.
  induction EXEC as [cst _|cst cst'' cst' _ STEP EXEC IH];
  intros USER'.
  - split; eauto.
    intros KERNEL.
    apply in_user_in_kernel in USER'. congruence.
  - specialize (IH USER').
    split.
    + intros USER ast REF.
      destruct (in_user cst'') eqn:USER''.
      { assert (USTEP := hs_intro USER USER'' STEP).
        eapply hit_simulation in USTEP; eauto.
        destruct USTEP as (ast' & ASTEP & REF').
        destruct IH as [IH _]; eauto.
        specialize (IH eq_refl _ REF').
        destruct IH as (ast'' & AEXEC & REF'').
        now eauto. }
      exploit user_into_kernel; eauto. intros KERNEL''.
      destruct IH as [_ IH].
      specialize (IH KERNEL'' ast cst cst'' REF STEP (re_refl _ _ _ KERNEL'')).
      destruct IH as (ast' & AEXEC & REF').
      eauto.
    + intros KERNEL ast cst0 kst REF STEP0 KEXEC.
      destruct (in_kernel cst'') eqn:KERNEL''.
      { assert (KEXEC'' : kernel_exec kst cst'').
        { apply restricted_exec_trans with cst; eauto. }
        destruct IH as [_ IH].
        specialize (IH eq_refl ast cst0 kst REF STEP0 KEXEC'').
        destruct IH as (ast' & AEXEC & REF').
        eexists ast'.
        split; eauto. }
      assert (USER0 : in_user cst0 = true) by (destruct REF; eauto).
      assert (KUEXEC := eu_intro (fun s => in_kernel s = false) _ KEXEC KERNEL'' STEP).
      assert (MSTEP := ks_intro USER0 STEP0 KUEXEC).
      eapply miss_simulation in MSTEP; eauto.
      destruct MSTEP as [MSTEP | MSTEP].
      * assert (USER'' : in_user cst'' = true) by now destruct MSTEP.
        destruct IH as [IH _].
        specialize (IH USER'' ast MSTEP).
        destruct IH as (ast' & AEXEC & REF').
        eexists ast'.
        split; eauto.
      * destruct MSTEP as (ast' & ASTEP & REF').
        assert (USER'' : in_user cst'' = true) by now destruct REF'.
        destruct IH as [IH _].
        specialize (IH USER'' _ REF').
        destruct IH as (ast'' & AEXEC & REF'').
        eauto.
Qed.

Theorem backwards_refinement ast cst cst' :
  refine_state ast cst ->
  exec (Concrete.step _ masks) cst cst' ->
  in_user cst' = true ->
  exists ast',
    exec (Symbolic.step table) ast ast' /\
    refine_state ast' cst'.
Proof.
  intros REF EXEC USER'.
  assert (USER : in_user cst = true) by (destruct REF; trivial).
  exploit backwards_refinement_aux; eauto.
  intros [H _]. eauto.
Qed.

Hint Unfold Concrete.next_state_reg.
Hint Unfold Concrete.next_state_reg_and_pc.
Hint Unfold Concrete.next_state_pc.
Hint Unfold Concrete.next_state.
Hint Unfold Concrete.miss_state.

Let in_kernel_user t ic : Concrete.is_kernel_tag ops (encode (USER t ic)) = false.
Proof.
  unfold Concrete.is_kernel_tag.
  rewrite kernel_tag_correct.
  now erewrite eq_tag_eq_word.
Qed.

Lemma user_mem_unchanged_refine_memory amem cmem cmem' :
  refine_memory amem cmem ->
  user_mem_unchanged cmem cmem' ->
  refine_memory amem cmem'.
Proof.
  intros REF USERMEM addr x t.
  rewrite <- (USERMEM addr).
  apply REF.
Qed.

Lemma user_regs_unchanged_refine_registers areg creg creg' :
  refine_registers areg creg ->
  user_regs_unchanged creg creg' ->
  refine_registers areg creg'.
Proof.
  intros REF USERREG r x t.
  rewrite <- (USERREG r).
  apply REF.
Qed.

Ltac match_data :=
  repeat match goal with
  | H : Symbolic.get_mem ?amem ?addr = Some ?w,
    REFM : refine_memory ?amem ?cmem |- _ =>
    match goal with
    | _ : Concrete.get_mem cmem addr = _ |- _ => fail 1
    | |- _ => idtac
    end;
    apply REFM in H

  | GET : Concrete.get_mem ?mem1 ?addr = Some ?x@(encode (USER ?t false)),
    USERMEM : user_mem_unchanged ?mem1 ?mem2 |- _ =>
    match goal with
    | _ : Concrete.get_mem mem2 addr = _ |- _ => fail 1
    | |- _ => idtac
    end;
    assert (Concrete.get_mem mem2 addr = Some x@(encode (USER t false)));
    try solve [eapply USERMEM; assumption]

  | H : Symbolic.upd_mem ?amem ?addr _ = _,
    REFM : refine_memory ?amem ?cmem |- _ =>
    match goal with
      | _ : Concrete.upd_mem cmem addr _ = _ |- _ => fail 1
      | |- _ => idtac
    end;
    let old := fresh "old" in
    let Hold := fresh "Hold" in
    let cmem' := fresh "cmem'" in
    let UPD' := fresh "UPD'" in
    let REFM' := fresh "REFM'" in
    destruct (refine_memory_upd' _ _ _ REFM H) as (cmem' & UPD' & REFM')

  | H : Symbolic.get_reg ?aregs ?r = Some _,
    REFR : refine_registers ?aregs ?cregs |- _ =>
    apply REFR in H

  | UPD : Symbolic.upd_reg ?aregs ?r _ = Some _,
    REFR : refine_registers ?aregs ?cregs |- _ =>
    match goal with
    | _ : Concrete.get_reg cregs r = _ |- _ => fail 1
    | |- _ => idtac
    end;
    let old := fresh "old" in
    let Hold := fresh "Hold" in
    let UPD' := fresh "UPD'" in
    destruct (PartMaps.upd_inv (Symbolic.reg_axioms (t := mt)) _ _ _ UPD) as [old Hold];
    apply REFR in Hold;
    assert (UPD' := refine_registers_upd' _ _ REFR UPD)
  end.

Ltac user_data_unchanged :=
  match goal with
  | GET : Concrete.get_mem _ ?addr = Some _,
    USERMEM : user_mem_unchanged _ _
    |- Concrete.get_mem _ ?addr = Some _ =>
    simpl in GET, USERMEM;
    rewrite <- (USERMEM addr); eassumption

  | GET : Concrete.get_reg _ ?r = _,
    USERREGS : user_regs_unchanged _ _
    |- Concrete.get_reg _ ?r = _ =>
    simpl in GET, USERREGS;
    rewrite <- (USERREGS r); eauto
  end.

Lemma no_syscall_no_entry_point mem addr :
  wf_entry_points mem ->
  Symbolic.get_syscall table addr = None ->
  negb match Concrete.get_mem mem addr with
       | Some _@it => it ==b encode ENTRY
       | None => false
       end = true.
Proof.
  intros WF GETSC.
  destruct (match Concrete.get_mem mem addr with
            | Some _@it => it ==b encode ENTRY
            | None => false
            end) eqn:E; trivial.
  apply WF in E.
  destruct E. congruence.
Qed.

(* Just for automation *)
Let kernel_invariant_ra_upd mem regs cache int w t:
  ki mem regs cache int ->
  ra_in_user regs ->
  ki mem (Concrete.upd_reg regs ra w@(encode (USER t false))) cache int.
Proof.
  intros KINV RA.
  unfold ra_in_user, word_lift in RA.
  destruct (Concrete.get_reg regs ra) as [v t'] eqn:E.
  simpl in *.
  destruct (decode t') as [[t'' [|]| |]|] eqn:DEC; try discriminate.
  apply encodeK in DEC. subst.
  eapply kernel_invariant_upd_reg; eauto.
Qed.

Ltac solve_concrete_step :=
  match goal with
  | LOOKUP : Concrete.cache_lookup _ _ _ _ = _ |- _ =>
    econstructor (solve [eauto; try solve [user_data_unchanged];
                         repeat autounfold; simpl;
                         simpl in LOOKUP; rewrite LOOKUP;
                         match goal with
                         | STORE : Concrete.store_mvec _ _ _ = Some _ |- _ =>
                           rewrite STORE
                         | |- _ => idtac
                         end;
                         simpl in *; match_inv; eauto])
  end.

Ltac destruct_mvec_fields :=
  repeat match goal with
  | ts : Vector.t _ 0 |- _ => induction ts using Vector.case0
  | ts : Vector.t _ (S _) |- _ => induction ts using caseS
  | ts : Empty_set |- _ => destruct ts
  end.

Let symbolic_handler_concrete_cache cache umvec ic urvec rvec :
  cache_correct cache ->
  Symbolic.handler umvec = Some urvec ->
  Concrete.cache_lookup _ cache masks (encode_mvec (mvec_of_umvec ic umvec)) = Some rvec ->
  rvec = encode_rvec (rvec_of_urvec (op umvec) urvec).
Proof.
  intros CACHE HANDLER LOOKUP.
  assert (INUSER : word_lift (fun t => is_user t)
                             (Concrete.ctpc (encode_mvec (mvec_of_umvec ic umvec))) = true).
  { destruct umvec as [op tpc ti ts].
    simpl.
    unfold word_lift.
    rewrite decodeK.
    reflexivity. }
  specialize (CACHE _ _ INUSER LOOKUP).
  destruct CACHE as (mvec & rvec' & E1 & E2 & E3). subst.
  apply encode_mvec_inj in E1; eauto. subst.
  unfold handler, rules.handler in E3; eauto.
  destruct umvec as [op tpc ti ts].
  simpl in E3.
  destruct op; simpl in *;
  destruct_mvec_fields; simpl in *;
  rewrite HANDLER in E3; simpl in E3; congruence.
Qed.

Let symbolic_handler_concrete_handler mvec rvec ic :
  Symbolic.handler mvec = Some rvec ->
  match decode_mvec (encode_mvec (mvec_of_umvec ic mvec)) with
  | Some mvec => handler mvec
  | None => None
  end = Some (rvec_of_urvec (op mvec) rvec).
Proof.
  intros H.
  rewrite decode_mvecK; eauto.
  destruct mvec as [op tpc ti ts].
  unfold handler, rules.handler. simpl.
  destruct op; simpl in *;
  destruct_mvec_fields; simpl in *; now rewrite H.
Qed.

Lemma forward_simulation ast ast' cst :
  refine_state ast cst ->
  Symbolic.step table ast ast' ->
  exists cst',
    exec (Concrete.step _ masks) cst cst' /\
    refine_state ast' cst'.
Proof.
  destruct ast as [amem aregs [apc tapc] int], cst as [cmem cregs cache [cpc cpct] epc].
  unfold refine_state. simpl.
  intros REF STEP.
  destruct REF as (KER & ? & ? & REFM & REFR & CACHE & MVEC & RA & WFENTRYPOINTS & KINV).
  destruct (decode cpct) as [[t ic| |]|] eqn:DEC; try solve [intuition].
  apply encodeK in DEC.
  subst cpc tapc cpct.
  inv STEP;
  try match goal with
  | H : Symbolic.State _ _ _ _ = Symbolic.State _ _ _ _ |- _ =>
    inv H
  end;
  match_data;
  repeat autounfold in NEXT;
  match_inv;

  try match goal with
  | HANDLER : Symbolic.handler ?mvec = Some ?rvec |- _ =>
    destruct rvec;
    let cmvec := constr:(encode_mvec (mvec_of_umvec ic mvec)) in
    destruct (Concrete.cache_lookup _ cache masks cmvec) as [rvec' | ] eqn:LOOKUP;

    [
      (* Cache hit case *)
      generalize (symbolic_handler_concrete_cache _ _ CACHE HANDLER LOOKUP);
      intros; subst rvec';
      unfold encode_mvec, encode_rvec, rvec_of_urvec in LOOKUP; simpl in *;
      match_data;
      try match op with
      | JAL =>
        destruct ast' as [amem' aregs' apc'];
        exploit syscalls_correct_allowed_case; eauto;
        intros; clear tnone_correct;
        repeat match goal with
        | H : exists _, _ |- _ => destruct H
        | H : _ /\ _ |- _ => destruct H
        end
      end;
      try solve [eexists; split;
      [apply exec_one; solve_concrete_step|
       unfold in_user, word_lift in *; simpl in *;
       repeat rewrite decodeK; simpl in *;
       repeat match goal with
       | |- _ /\ _ =>
         split; eauto using mvec_in_kernel_user_upd, ra_in_user_upd,
                            wf_entry_points_user_upd, no_syscall_no_entry_point,
                            refine_registers_upd'
       end]]
        (* || let op := current_instr_opcode in fail 3 "failed hit case" op *)
    |
      (* Cache miss case, fault handler will execute *)
      let STORE := fresh "STORE" in
      destruct (mvec_in_kernel_store_mvec cmvec MVEC) as [? STORE];
      pose proof (store_mvec_mvec_in_kernel _ _ STORE);
      pose proof (kernel_invariant_store_mvec ki _ _ _ _ _ KINV STORE);
      let HANDLER' := constr:(symbolic_handler_concrete_handler _ ic HANDLER) in
      destruct (handler_correct_allowed_case _ cmvec _ pc@(encode (USER tpc ic)) _ KINV HANDLER' STORE CACHE)
        as ([? ? ? [? ?] ?] &
            KEXEC & CACHE' & LOOKUP' & MVEC' & USERMEM & USERREGS & PC' & WFENTRYPOINTS' & KINV'');
      simpl in PC'; inv PC';
      generalize (user_mem_unchanged_refine_memory REFM USERMEM); intros; match_data;
      unfold encode_mvec, encode_rvec, rvec_of_urvec in *; simpl in *;
      try solve [eexists; split;
      [
        eapply re_step; trivial; [solve_concrete_step|];
        try (
          eapply restricted_exec_trans;
          try solve [eapply exec_until_weaken; eapply KEXEC];
          try solve [eapply exec_one; solve_concrete_step]
        )
      |
        unfold in_user, word_lift in *; simpl in *;
        repeat rewrite decodeK; simpl in *;
        try match goal with
        | USERREGS : user_regs_unchanged ?cregs _,
          H : Concrete.get_reg ?cregs ?r = _ |- _ =>
          simpl in USERREGS; rewrite (USERREGS r) in H
        end;
        try solve [
          repeat match goal with
          | |- _ /\ _ =>
            split;
            eauto using user_mem_unchanged_refine_memory,
                        refine_registers_upd', user_regs_unchanged_refine_registers,
                        user_regs_unchanged_ra_in_user, ra_in_user_upd,
                        mvec_in_kernel_user_upd, wf_entry_points_user_upd,
                        no_syscall_no_entry_point, kernel_invariant_ra_upd
          end
        ]
      ]] (* || let op := current_instr_opcode in fail 3 "failed miss case" op *)
    ]
  end.

  admit.

  admit.

Qed.

End Refinement.
