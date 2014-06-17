Require Import List NPeano Arith Bool.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Require Import lib.utils lib.partial_maps lib.Coqlib.
Require Import common.common.
Require Import concrete.concrete.
Require Import concrete.exec.
Require Import symbolic.symbolic.
Require Import symbolic.rules.
Require Import symbolic.refinement_common.

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
        {e : @encodable (Symbolic.tag mt) mt ops}
        {ki : kernel_invariant}
        {table : list (Symbolic.syscall mt)}
        {kcc : kernel_code_correctness ki table}.

Hint Unfold Symbolic.next_state.
Hint Unfold Symbolic.next_state_reg_and_pc.
Hint Unfold Symbolic.next_state_pc.
Hint Unfold Symbolic.next_state_reg.

Hint Resolve kernel_invariant_upd_mem.
Hint Resolve kernel_invariant_upd_reg.
Hint Resolve kernel_invariant_store_mvec.

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

Let miss_state_not_user st st' mvec :
  Concrete.miss_state ops st mvec = Some st' ->
  in_user st' = true ->
  False.
Proof.
  intros MISS INUSER.
  apply in_user_in_kernel in INUSER; eauto.
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
    unfold in_user, in_kernel in INUSER; simpl in INUSER; rewrite PC in INUSER;
    assert (CACHEHIT := analyze_cache mvec _ CACHE LOOKUP INUSER (erefl _));
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

Ltac current_instr_opcode :=
  match goal with
  | H : decode_instr _ = Some ?instr |- _ =>
    let op := (eval compute in (opcode_of instr)) in
    op
  end.

Lemma hit_simulation ast cst cst' :
  refine_state ki table ast cst ->
  hit_step cst cst' ->
  exists ast',
    Symbolic.step table ast ast' /\
    refine_state ki table ast' cst'.
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
  | MEM : PartMaps.get ?cmem ?addr = Some _ |- _ =>
    match goal with
    | _ : PartMaps.get ?amem addr = Some _ |- _ =>
      match type of amem with
      | Symbolic.memory mt => fail 2
      end
    | |- _ => idtac
    end;
    pose proof (proj1 (REFM _ _ _) MEM)
  end;

  try match goal with
  | OLD : TotalMaps.get ?reg ?r = _
    |- context[TotalMaps.upd ?reg ?r ?v@(encode (USER ?t false))] =>
    (destruct (refine_registers_upd _ v _ t REFR OLD) as (? & ? & ?);
     pose proof (kernel_invariant_upd_reg ki _ _ _ _ _ _ v t false _ KINV OLD))
    || let op := current_instr_opcode in fail 3 op
  end;

  try match goal with
  | GET : PartMaps.get ?cmem ?addr = Some _,
    UPD : PartMaps.upd ?cmem ?addr _ = Some _ |- _ =>
    (destruct (refine_memory_upd _ _ _ _ REFM GET UPD) as (? & ? & ?);
     pose proof (wf_entry_points_user_upd _ _ _ _ WFENTRYPOINTS GET UPD);
     pose proof (mvec_in_kernel_user_upd _ _ _ _ MVEC GET UPD))
    || let op := current_instr_opcode in fail 3 op
  end;

  repeat match goal with
  | creg : Concrete.registers mt,
    H : TotalMaps.get ?creg ?r = _ |- _ =>
    apply REFR in H
  end;

  try match goal with
  | INST : decode_instr _ = Some (Jal _ _) |- _ =>
    pose proof (in_user_no_system_call _ _ INUSER' (erefl _) WFENTRYPOINTS)
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

Ltac simpl_word_lift :=
  match goal with
  | H : context[word_lift _ (encode _)] |- _ =>
    unfold word_lift in H;
    rewrite decodeK in H;
    simpl in H
  end.

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
                             (Concrete.fault_handler_start _ (t := mt))@Concrete.TKernel
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

Import Vector.VectorNotations.

Lemma state_on_syscalls st st' :
  forall (ISUSER : in_user st = true)
         (CACHE : cache_correct (Concrete.cache st))
         (ISCALL : word_lift (fun t => is_call t) (common.tag (Concrete.pc st')) = true)
         (STEP : Concrete.step _ masks st st'),
    Concrete.mem st' = Concrete.mem st /\
    Concrete.cache st' = Concrete.cache st /\
    exists r i tpc ic ti t1 old told trpc tr,
      Concrete.regs st' =
      TotalMaps.upd (Concrete.regs st) ra
                       (common.val (Concrete.pc st) + Z_to_word 1)%w@(encode (USER tr false)) /\
      common.tag (Concrete.pc st') = encode (USER trpc true) /\
      common.tag (Concrete.pc st) = encode (USER tpc ic) /\
      PartMaps.get (Concrete.mem st) (common.val (Concrete.pc st)) =
      Some i@(encode (USER ti false)) /\
      decode_instr i = Some (Jal _ r) /\
      TotalMaps.get (Concrete.regs st) r = (common.val (Concrete.pc st'))@(encode (USER t1 false)) /\
      TotalMaps.get (Concrete.regs st) ra = old@(encode (USER told false)) /\
      Concrete.cache_lookup _ (Concrete.cache st) masks
                            (encode_mvec (mvec_of_umvec ic (Symbolic.mkMVec JAL tpc ti [t1; told]))) =
      Some (encode_rvec (rvec_of_urvec JAL (Symbolic.mkRVec trpc tr))).
Proof.
  intros.
  inv STEP;
  unfold Concrete.next_state_reg, Concrete.next_state_reg_and_pc,
         Concrete.next_state_pc, Concrete.next_state,
         Concrete.miss_state in *;
  match_inv;
  try analyze_cache;
  simpl in *;
  try erewrite encode_kernel_tag in *;
  try solve [repeat simpl_word_lift; simpl in *; discriminate].
  repeat (split; eauto).
  unfold encode_mvec, encode_rvec, mvec_of_umvec, rvec_of_urvec. simpl.
  do 10 eexists.
  repeat (split; eauto).
Qed.

Lemma miss_simulation ast cst cst' :
  refine_state ki table ast cst ->
  miss_step cst cst' ->
  refine_state ki table ast cst' \/
  exists ast', Symbolic.step table ast ast' /\
               refine_state ki table ast' cst'.
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
      apply is_user_pc_tag_is_kernel_tag in EQ; auto. congruence. }
    destruct (initial_handler_state ISUSER NUSER CACHE STEP)
      as (cmem' & mvec & STORE & ?). subst. simpl in *.
    destruct (match decode_mvec mvec with
              | Some mvec => handler (fun m => Symbolic.handler m) mvec
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
        case/orP: ISUSER => ISUSER.
        { simpl in ISUSER. now rewrite ISUSER. }
        destruct (PartMaps.get cmem'' apc) as [[i it]|] eqn:GET;
          [|apply orb_true_r].
        have [eq_it|neq_it] := altP (it =P (encode ENTRY)); [|apply orb_true_r]; simpl in *; subst.
        generalize (proj2 (WFENTRYPOINTS' apc)).
        rewrite GET. rewrite eqxx. intros DEF.
        specialize (DEF (erefl _)).
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
  - right. case/andP: SYSCALL => S1 S2.
    destruct (PartMaps.get (Concrete.mem kst) (common.val (Concrete.pc kst)))
      as [[i it]|] eqn:GET; try discriminate.
    move/eqP: S2=> S2. subst.
    exploit state_on_syscalls; eauto. simpl.
    intros (EM & ER & r & w & tpc & ic & ti & t1 & old & told & trpc & tr &
            EC & MEM & ? & INST & DEC & PC' & RA' & LOOKUP').
    rewrite EM in GET. subst.
    assert (SYSCALL : exists sc, Symbolic.get_syscall table (common.val (Concrete.pc kst)) = Some sc).
    { unfold wf_entry_points in WFENTRYPOINTS. rewrite WFENTRYPOINTS.
      rewrite GET. apply eqxx. }
    destruct SYSCALL as [sc GETSC].
    assert (HANDLER := fun H => CACHE _ _ H LOOKUP').
    unfold word_lift in HANDLER. simpl in HANDLER. rewrite decodeK in HANDLER.
    specialize (HANDLER (erefl _)).
    destruct HANDLER as (mvec & rvec & E1 & E2 & HANDLER).
    apply encode_mvec_inj in E1; eauto. apply encode_rvec_inj in E2. subst.
    unfold handler, rules.handler in HANDLER. simpl in HANDLER.
    destruct (Symbolic.handler (Symbolic.mkMVec JAL tpc ti [t1; told])) as [[trpc' tr']|] eqn:HANDLER';
      try discriminate.
    unfold rvec_of_urvec in HANDLER. simpl in HANDLER. inv HANDLER.
    destruct kst as [kmem kregs kcache [kpc kpct] kepc]. subst. simpl in *.
    rewrite decodeK in TAG. simpl in TAG. inv TAG.
    destruct (Symbolic.sem sc (Symbolic.State amem areg apc@tapc int)) as [ast'|] eqn:SCEXEC.
    + destruct ast' as [amem' areg' [apc' tapc'] int'].
      exploit syscalls_correct_allowed_case; eauto.
      intros (cmem' & creg' & cache' & pct' & EXEC' &
              REFM' & REFR' & CACHE' & MVEC' & RA'' & WFENTRYPOINTS' & KINV').
      generalize (kernel_user_exec_determ KEXEC EXEC'). intros ?. subst.
      { exists (Symbolic.State amem' areg' apc'@tapc' int'). split.
        - eapply Symbolic.step_syscall; eauto.
          + apply REFM in INST; eauto.
          + apply REFR. apply PC'.
          + apply REFR. eauto.
        - unfold refine_state, in_user, word_lift. simpl.
          rewrite decodeK. simpl.
          repeat (split; eauto). }
    + destruct (syscalls_correct_disallowed_case _ _ _ _ _ _ _ KINV REFM REFR CACHE MVEC
                                                 WFENTRYPOINTS GETSC HANDLER' SCEXEC KEXEC).
Qed.

Lemma user_step_simulation ast cst cst' :
  refine_state ki table ast cst ->
  user_step cst cst' ->
  exists ast',
    exec (Symbolic.step table) ast ast' /\
    refine_state ki table ast' cst'.
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
  refine_state ki table ast cst ->
  exec user_step cst cst' ->
  exists ast',
    exec (Symbolic.step table) ast ast' /\
    refine_state ki table ast' cst'.
Proof.
  intros REF EXEC.
  gdep ast. induction EXEC as [|? ? ? _ STEP EXEC IH]; autounfold; eauto.
  intros.
  exploit user_step_simulation; eauto. intros (? & ? & ?).
  exploit IH; eauto. intros (ast' & ? & ?).
  eexists ast'. split; eauto.
Qed.

Lemma user_into_kernel ast cst cst' :
  refine_state ki table ast cst ->
  Concrete.step _ masks cst cst' ->
  in_user cst' = false ->
  in_kernel cst' = true.
Proof.
  destruct ast as [? ? [? ?]], cst as [? ? ? [? ?] ?].
  intros REF STEP NUSER.
  destruct (in_kernel cst') eqn:NKERNEL; trivial.
  unfold in_user in NUSER.
  unfold in_kernel, Concrete.is_kernel_tag in NKERNEL.
  erewrite encode_kernel_tag in NKERNEL.
  destruct REF as (INUSER & ? & ? & ? & ? & CACHE & ?).
  assert (PCS := valid_pcs STEP CACHE INUSER).
  unfold word_lift in *.
  destruct (decode (common.tag (Concrete.pc cst'))) as [[t [|]| |]|] eqn:DEC;
  try discriminate; simpl in *;
  apply encodeK in DEC.
  - rewrite <- DEC in NKERNEL.
    erewrite eq_tag_eq_word in NKERNEL.
    simpl in NKERNEL.
    by rewrite NKERNEL in NUSER.
  - rewrite DEC in NKERNEL.
    by rewrite eqxx in NKERNEL.
Qed.

Lemma backwards_refinement_aux cst cst' (EXEC : exec (Concrete.step _ masks) cst cst') :
  in_user cst' = true ->
  (in_user cst = true ->
   forall ast,
     refine_state ki table ast cst ->
     exists ast',
       exec (Symbolic.step table) ast ast' /\
       refine_state ki table ast' cst') /\
  (in_kernel cst = true ->
   forall ast cst0 kst,
     refine_state ki table ast cst0 ->
     Concrete.step _ masks cst0 kst ->
     kernel_exec kst cst ->
     exists ast',
       exec (Symbolic.step table) ast ast' /\
       refine_state ki table ast' cst').
Proof.
  induction EXEC as [cst _|cst cst'' cst' _ STEP EXEC IH];
  intros USER'.
  - split; eauto.
    intros KERNEL.
    apply in_user_in_kernel in USER'; auto. congruence.
  - specialize (IH USER').
    split.
    + intros USER ast REF.
      destruct (in_user cst'') eqn:USER''.
      { assert (USTEP := hs_intro USER USER'' STEP).
        eapply hit_simulation in USTEP; eauto.
        destruct USTEP as (ast' & ASTEP & REF').
        destruct IH as [IH _]; eauto.
        specialize (IH (erefl _) _ REF').
        destruct IH as (ast'' & AEXEC & REF'').
        now eauto. }
      exploit user_into_kernel; eauto. intros KERNEL''.
      destruct IH as [_ IH].
      specialize (IH KERNEL'' ast cst cst'' REF STEP (re_refl _ KERNEL'')).
      destruct IH as (ast' & AEXEC & REF').
      eauto.
    + intros KERNEL ast cst0 kst REF STEP0 KEXEC.
      destruct (in_kernel cst'') eqn:KERNEL''.
      { assert (KEXEC'' : kernel_exec kst cst'').
        { apply restricted_exec_trans with cst; eauto. }
        destruct IH as [_ IH].
        specialize (IH (erefl _) ast cst0 kst REF STEP0 KEXEC'').
        destruct IH as (ast' & AEXEC & REF').
        eexists ast'.
        split; eauto. }
      assert (USER0 : in_user cst0 = true) by (destruct REF; eauto).
      assert (KUEXEC := eu_intro (Q := fun s => in_kernel s = false) KEXEC KERNEL'' STEP).
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
  refine_state ki table ast cst ->
  exec (Concrete.step _ masks) cst cst' ->
  in_user cst' = true ->
  exists ast',
    exec (Symbolic.step table) ast ast' /\
    refine_state ki table ast' cst'.
Proof.
  intros REF EXEC USER'.
  assert (USER : in_user cst = true) by (destruct REF; trivial).
  exploit backwards_refinement_aux; eauto.
  intros [H _]. eauto.
Qed.

End Refinement.
