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

  try solve [rewrite /in_user /word_lift /= decodeK //= in INUSER'];

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
    |- context[TotalMaps.upd ?reg ?r ?v@(encode (USER ?t))] =>
    (destruct (refine_registers_upd _ v _ t REFR OLD) as (? & ? & ?);
     pose proof (kernel_invariant_upd_reg ki _ _ _ _ _ v t _ KINV OLD))
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

Let at_call (cst : Concrete.state mt) : bool :=
  match PartMaps.get (Concrete.mem cst) (common.val (Concrete.pc cst)) with
  | Some _@it => word_lift [eta @is_entry_tag _] it
  | None => false
  end.

Lemma initial_handler_state cst kst :
  forall (ISUSER : in_user cst = true)
         (NCALL : ~~ at_call cst)
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
  try solve [repeat simpl_word_lift; simpl in *; discriminate | eauto |
             rewrite /at_call PC /word_lift decodeK // in NCALL ].
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

Lemma user_kernel_user_step_determ s s1 s2 :
  user_kernel_user_step s s1 ->
  user_kernel_user_step s s2 ->
  s1 = s2.
Proof.
  move => [s' USER1 STEP1 EXEC1] [s'' USER2 STEP2 EXEC2].
  have E: (s' = s'') by rewrite <- stepP in *; congruence. subst s''.
  eauto using kernel_user_exec_determ.
Qed.

Import Vector.VectorNotations.

(* TODO: split this between syscall vs fault *)
Lemma user_kernel_user_simulation ast cst cst' :
  refine_state ki table ast cst ->
  user_kernel_user_step cst cst' ->
  refine_state ki table ast cst' \/
  exists ast', Symbolic.step table ast ast' /\
               refine_state ki table ast' cst'.
Proof.
  intros REF STEP.
  case ATCALL: (at_call cst).
  - destruct
      ast as [amem aregs [apc atpc] int],
      cst as [cmem cregs cache [pc tpc] epc],
             REF as (_ & ? & Ht & REFM & REFR & CACHE & MVEC & RA & WFENTRYPOINTS & KINV).
    subst apc.
    destruct (decode tpc) as [[tpc'| |]|] eqn:DEC => //. subst tpc'.
    apply encodeK in DEC. subst tpc.
    rewrite /at_call /= in ATCALL.
    case GET: (PartMaps.get cmem pc) => [[? it]|];
    rewrite GET /word_lift /is_entry_tag // in ATCALL.
    case DEC: (decode it) => [[ | | t]|];
    rewrite DEC // in ATCALL. apply encodeK in DEC. subst it.
    have SC : exists sc, Symbolic.get_syscall table pc = Some sc /\
                         Symbolic.entry_tag sc = t.
    { apply/WFENTRYPOINTS. rewrite GET eq_tag_eq_word eqxx //. }
    move: SC => [sc [GETSC ?]].
    case SCEXEC: (Symbolic.run_syscall sc (Symbolic.State amem aregs pc@atpc int))
      => [[amem' aregs' [pc' atpc'] int']|].
    + exploit syscalls_correct_allowed_case; eauto.
      intros (cmem' & creg' & cache' & pct' & EXEC' &
              REFM' & REFR' & CACHE' & MVEC' & RA'' & WFENTRYPOINTS' & KINV').
      generalize (user_kernel_user_step_determ STEP EXEC'). intros ?. subst.
      right.
      { exists (Symbolic.State amem' aregs' pc'@atpc' int'). split.
        - eapply Symbolic.step_syscall; eauto.
          case GET': (PartMaps.get amem pc) => [[? ?]|] //.
          move/REFM: GET' => GET'.
          rewrite GET in GET'.
          move: GET' => [[? H]].
          by apply encode_inj in H.
        - unfold refine_state, in_user, word_lift. simpl.
          rewrite decodeK. simpl.
          repeat (split; eauto). }
    + destruct (syscalls_correct_disallowed_case _ _ KINV REFM REFR CACHE MVEC
                                                 WFENTRYPOINTS GETSC SCEXEC STEP).
  - left.
    move: STEP => [kst ISUSER STEP KEXEC].
    have KER : in_kernel kst = true.
    { destruct KEXEC as [? EXEC]. exact (restricted_exec_fst EXEC). }
    destruct ast as [amem areg [apc tapc] int], cst as [cmem cregs cache [cpc cpct] cepc].
    destruct REF as (_ & ? & Ht & REFM & REFR & CACHE & MVEC & RA & WFENTRYPOINTS & KINV).
    destruct (decode cpct) as [[tpc' | | ]|] eqn:TAG; try solve [intuition].
    subst cpc tpc'.
    assert (NUSER : word_lift (fun t => is_user t) (common.tag (Concrete.pc kst)) = false).
    { destruct (word_lift (fun t => is_user t) (common.tag (Concrete.pc kst))) eqn:EQ; trivial.
      rewrite /in_kernel in KER.
      apply is_user_pc_tag_is_kernel_tag in EQ; auto. congruence. }
    rewrite <- negb_true_iff in ATCALL.
    destruct (initial_handler_state ISUSER ATCALL NUSER CACHE STEP)
      as (cmem' & mvec & STORE & ?). subst. simpl in *.
    case HANDLER: (handler [eta Symbolic.handler] mvec) => [rvec|].
    + destruct (handler_correct_allowed_case cmem mvec cregs apc@cpct int KINV HANDLER STORE CACHE)
        as (cst'' & KEXEC' & CACHE' & LOOKUP & MVEC' &
            HMEM & HREGS & HPC & WFENTRYPOINTS' & KINV').
      assert (EQ := kernel_user_exec_determ KEXEC' KEXEC). subst cst''.
      destruct cst' as [cmem'' cregs'' cache' ? ?]. simpl in *. subst.
      unfold refine_state.
      repeat match goal with
      | |- _ /\ _ => split; eauto using user_regs_unchanged_ra_in_user
      end.
      * rewrite TAG //.
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
  - exploit user_kernel_user_simulation; eauto.
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
  destruct (decode (common.tag (Concrete.pc cst'))) as [[t| |]|] eqn:DEC;
  try discriminate; simpl in *;
  apply encodeK in DEC.
  rewrite <- DEC in NKERNEL.
  rewrite eq_tag_eq_word // in NKERNEL.
Qed.

Definition refine_state_weak ast cst :=
  refine_state ki table ast cst \/
  exists cst0 kst,
    refine_state ki table ast cst0 /\
    Concrete.step _ masks cst0 kst /\
    kernel_exec kst cst.

(* This should be useful for proving backwards_simulation,
   and for CFI *)
Lemma kernel_simulation_strong ast cst cst' :
  refine_state_weak ast cst ->
  Concrete.step _ masks cst cst' ->
  visible cst cst' = false ->
  refine_state_weak ast cst'.
Admitted.

Lemma backwards_simulation ast cst cst' :
  refine_state_weak ast cst ->
  Concrete.step _ masks cst cst' ->
  refine_state_weak ast cst' \/
  exists ast',
    Symbolic.step table ast ast' /\
    refine_state ki table ast' cst'.
Proof.
  intros [REF | (cst0 & kst & REF & KSTEP & EXEC)] STEP.
  - assert (USER : in_user cst = true) by (destruct cst, ast, REF; eauto).
    destruct (in_user cst') eqn:USER'.
    + right.
      eapply hit_simulation; eauto.
      constructor; auto.
    + left. right. do 2 eexists. do 2 (split; eauto).
      constructor.
      eapply user_into_kernel; eauto.
  - assert (USER : in_user cst0 = true) by (destruct cst0, ast, REF; eauto).
    destruct (in_kernel cst') eqn:KER'.
    + left. right.
      do 2 eexists. do 2 (split; eauto).
      eapply restricted_exec_trans; eauto.
      have KER : in_kernel cst = true by eapply restricted_exec_snd in EXEC.
      eapply re_step; by eauto using user_into_kernel.
    + assert (EXEC' : user_kernel_user_step cst0 cst').
      { econstructor; eauto.
        econstructor; eauto using in_user_in_kernel. }
      eapply user_kernel_user_simulation in EXEC'; eauto.
      destruct EXEC' as [REF' | ?]; eauto.
      by do 2 left.
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
  have {REF} REF: refine_state_weak ast cst by left.
  move: ast REF.
  induction EXEC as [cst _|cst cst'' cst' _ STEP EXEC IH].
  - move => ast [? | REF]; first by eauto.
    destruct REF as (? & ? & ? & ? & EXEC).
    apply restricted_exec_snd in EXEC.
    apply in_user_in_kernel in USER'. congruence.
  - move => ast REF.
    exploit backwards_simulation; eauto.
    intros [REF' | (ast' & ASTEP & REF')]; first by auto.
    have {REF'} REF': refine_state_weak ast' cst'' by left.
    move: (IH USER' _ REF') => {IH USER' REF'} [ast'' [EXEC' REF']].
    eexists. split; last by eauto.
    eapply re_step; trivial; eauto.
Qed.

End Refinement.
