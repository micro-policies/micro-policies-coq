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
        {ap : Symbolic.symbolic_params}
        {memax : PartMaps.axioms (@Symbolic.sm mt ap)}
        {regax : PartMaps.axioms (@Symbolic.sr mt ap)}
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
    PartMaps.get cmem w = Some x@(encode (USER t false)) <->
    PartMaps.get amem w = Some x@t.

Definition refine_registers (areg : Symbolic.registers mt) (creg : Concrete.registers mt) :=
  forall n x t,
    TotalMaps.get creg n = x@(encode (USER t false)) <->
    PartMaps.get areg n = Some x@t.

Definition in_kernel st :=
  let pct := common.tag (Concrete.pc st) in
  let i := PartMaps.get (Concrete.mem st) (common.val (Concrete.pc st)) in
  Concrete.is_kernel_tag _ pct
  || word_lift (fun x => is_call x) pct
  && match i with
     | Some _@it => it ==b encode ENTRY
     | None => false
     end.
Hint Unfold in_kernel.

Definition user_pc_and_instr pct it :=
  word_lift (fun t =>
               is_user t
               && (negb (is_call t) || negb (it ==b encode ENTRY)))
            pct.

Definition in_user st :=
  let pct := common.tag (Concrete.pc st) in
  let i := PartMaps.get (Concrete.mem st) (common.val (Concrete.pc st)) in
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
    exists w, PartMaps.get cmem addr = Some w@Concrete.TKernel.

Hypothesis kernel_tag_correct :
  Concrete.TKernel = encode KERNEL.

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
  eapply PartMaps.upd_list_defined; eauto using Concrete.mem_axioms, eq_word.
  simpl map. intros addr IN.
  apply DEF in IN.
  destruct IN.
  eauto.
Qed.

Definition ra_in_user creg :=
  word_lift (fun x => is_user_data x)
            (common.tag (TotalMaps.get creg ra)) = true.
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
           (GET : PartMaps.get mem1 addr = Some w1@(encode (USER ut b)))
           (UPD : PartMaps.upd mem1 addr w2 = Some mem2),
      kernel_invariant_statement mem2 regs cache int;

  kernel_invariant_upd_reg :
    forall mem regs cache r w1 ut1 b1 w2 ut2 b2 int
           (KINV : kernel_invariant_statement mem regs cache int)
           (GET : TotalMaps.get regs r = w1@(encode (USER ut1 b1))),
      kernel_invariant_statement mem (TotalMaps.upd regs r w2@(encode (USER ut2 b2))) cache int;

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
    match PartMaps.get cmem addr with
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
  PartMaps.get cmem addr = Some v@(encode (USER t false)) ->
  PartMaps.upd cmem addr v'@(encode (USER t' false)) = Some cmem' ->
  exists amem',
    PartMaps.upd amem addr v'@t' = Some amem' /\
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
  PartMaps.get cmem addr = Some v@(encode (USER t false)) ->
  PartMaps.upd cmem addr v'@(encode (USER t' false)) = Some cmem' ->
  wf_entry_points cmem'.
Proof.
  unfold wf_entry_points.
  intros WF GET UPD addr'.
  split; intros H.
  - rewrite WF in H.
    destruct (PartMaps.get cmem addr') as [[v'' t'']|] eqn:MEM; try discriminate.
    erewrite PartMaps.get_upd_neq; eauto using Concrete.mem_axioms.
    { now rewrite MEM. }
    intros ?. subst addr'.
    assert (EQ : t'' = encode (USER t false)) by congruence. subst.
    rewrite eqb_true_iff in H.
    now apply encode_inj in H.
  - apply WF. clear WF.
    destruct (PartMaps.get cmem' addr') as [[v'' t'']|] eqn:GET'; try discriminate.
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
  PartMaps.get cmem addr = Some v@(encode (USER t false)) ->
  PartMaps.upd cmem addr v'@(encode (USER t' false)) = Some cmem' ->
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
  PartMaps.upd cmem addr w@Concrete.TKernel = Some cmem' ->
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
  PartMaps.upd amem addr v@t = Some amem' ->
  exists cmem',
    PartMaps.upd cmem addr v@(encode (USER t false)) = Some cmem' /\
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
  TotalMaps.get creg r = v@(encode (USER t false)) ->
  exists areg',
    PartMaps.upd areg r v'@t' = Some areg' /\
    refine_registers areg' (TotalMaps.upd creg r v'@(encode (USER t' false))).
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
  PartMaps.upd areg r v@t = Some areg' ->
  refine_registers areg' (TotalMaps.upd creg r v@(encode (USER t false))).
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
  ra_in_user (TotalMaps.upd creg r v@(encode (USER t false))).
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
    PC     : PartMaps.get _ ?pc = Some ?i@_,
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
  destruct (PartMaps.get (Concrete.mem st) (val (Concrete.pc st)))
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

Definition user_mem_unchanged cmem cmem' :=
  forall addr w t,
    PartMaps.get cmem addr = Some w@(encode (USER t false)) <->
    PartMaps.get cmem' addr = Some w@(encode (USER t false)).

Definition user_regs_unchanged cregs cregs' :=
  forall r w t,
    TotalMaps.get cregs r = w@(encode (USER t false)) <->
    TotalMaps.get cregs' r = w@(encode (USER t false)).

Class kernel_code_correctness : Prop := {

(* XXX: a bit of a lie now, given that the kernel can now return to a system call (BCP: ?) *)
(* BCP: Added some comments -- please check! *)
  handler_correct_allowed_case :
  forall mem mem' cmvec rvec reg cache old_pc int,
    (* If kernel invariant holds... *)
    ki mem reg cache int ->
    (* and calling the handler on the current m-vector succeeds and returns rvec... *)
    match decode_mvec cmvec with
    | Some mvec => handler mvec
    | None => None
    end = Some rvec ->
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
                          (Concrete.fault_handler_start (t := mt))@Concrete.TKernel
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
    match decode_mvec cmvec with
    | Some mvec => handler mvec
    | None => None
    end = None ->
    (* and storing the concrete representation of the m-vector yields new memory mem'... *)
    Concrete.store_mvec ops mem cmvec = Some mem' ->
    (* then if we start the concrete machine in kernel mode and let it
       run, it will never reach a user-mode state. *)
    in_kernel st' = false ->
    ~ exec (Concrete.step _ masks)
      (Concrete.mkState mem' reg cache
                        (Concrete.fault_handler_start (t := mt))@Concrete.TKernel
                        old_pc)
      st';

(* BCP: I think if we choose variant (2) of system calls that we've
   been discussing, then these properties (at least, the mvec part)
   will need to change... *)

  syscalls_correct_allowed_case :
  forall amem areg apc tpc int
         amem' areg' apc' tpc' int'
         cmem creg cache epc addr sc
         t1 ti told rvec ic,
    (* If [mvec] is an m-vector describing a JAL to address tpc with
       instruction tag ti and argument tags t1 and told...  *)
    (* (Could be strengthened to ensure that t1 and told do occur in the machine state.) *)
    let mvec := mkMVec JAL tpc ti [t1; told] in
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
    Symbolic.get_syscall table addr = Some sc ->
    (* and calling the handler on the current m-vector succeeds and returns rvec...
       (BCP: Why is it Symbolic.handler here and just handler above?) *)
    Symbolic.handler mvec = Some rvec ->
    (* and running sc on the current abstract machine state reaches a
       new state with primes on everything... *)
    Symbolic.sem sc (Symbolic.State amem areg apc@tpc int) = Some (Symbolic.State amem' areg' apc'@tpc' int') ->
    (* THEN if we start the concrete machine in kernel mode at the
       beginning of the corresponding system call code and let it run
       until it reaches a user-mode state with primes on everything... *)
    exists cmem' creg' cache' epc',
      (* CH: this doesn't quite agree with what's happening in symbolic.v;
             should bring the step_syscall rule back in sync *)
      kernel_user_exec (Concrete.mkState cmem
                                         (TotalMaps.upd creg ra
                                                           (apc + Z_to_word 1)%w@(encode (USER (tr rvec) ic)))
                                         cache
                                         addr@(encode (USER (trpc rvec) true)) epc)
                       (Concrete.mkState cmem' creg' cache'
                                         apc'@(encode (USER tpc' false))
                                         epc') /\
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
         cmem creg cache epc addr sc
         cst'
         t1 ti told rvec ic,
    (* Could be strengthened to ensure that t1 and told do occur in the machine state *)
    let mvec := mkMVec JAL tpc ti [t1; told] in
    ki cmem creg cache int ->
    refine_memory amem cmem ->
    refine_registers areg creg ->
    cache_correct cache ->
    mvec_in_kernel cmem ->
    wf_entry_points cmem ->
    Symbolic.get_syscall table addr = Some sc ->
    Symbolic.handler mvec = Some rvec ->
    Symbolic.sem sc (Symbolic.State amem areg apc@tpc int) = None ->
    (* CH: could write handler_correct_disallowed_case in the same way *)
    ~ kernel_user_exec (Concrete.mkState cmem
                                         (TotalMaps.upd creg ra
                                                           (apc + Z_to_word 1)%w@(encode (USER (tr rvec) ic)))
                                         cache
                                         addr@(encode (USER (trpc rvec) true)) epc)
                       cst'

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
  apply encodeK in E'. subst. simpl in RA.
  rewrite negb_true_iff in RA. subst.
  apply H in E.
  rewrite E.
  simpl.
  now rewrite decodeK.
Qed.

End Refinement.
