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
        {sp : Symbolic.params}
        {e : forall k, encodable mt (Symbolic.ttypes k)}
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
  Concrete.miss_state st mvec = Some st' ->
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

Ltac simpl_encode :=
  match goal with
  | H : context[decode (encode _)] |- _ =>
    rewrite decodeK in H; simpl in *; subst
  | H : encode _ = encode _ |- _ =>
    apply encode_inj in H; simpl in H; try inv H; subst
  end.

Ltac analyze_cache :=
  match goal with
  | LOOKUP : Concrete.cache_lookup ?cache _ ?mvec = Some ?rvec,
    PC     : PartMaps.get _ ?pc = Some ?i@_,
    INST   : decode_instr ?i = Some _,
    INUSER : in_user (Concrete.mkState _ _ _ ?pc@_ _) = true,
    CACHE  : cache_correct ?cache |- _ =>
    unfold in_user in INUSER; simpl in INUSER;
    assert (CACHEHIT := analyze_cache mvec CACHE LOOKUP INUSER (erefl _));
    simpl in CACHEHIT;
    repeat match type of CACHEHIT with
    | exists _, _ => destruct CACHEHIT as [? CACHEHIT]
    | _ /\ _ => destruct CACHEHIT as [? CACHEHIT]
    | _ \/ _ => destruct CACHEHIT as [CACHEHIT | CACHEHIT]
    | False => destruct CACHEHIT
    end;
    try subst mvec; simpl in *; subst;
    try match goal with
    | H : context[decode (encode _)] |- _ =>
      rewrite decodeK in H; simpl in *; subst
    end
  | MISS   : Concrete.miss_state _ _ = Some ?st',
    INUSER : in_user ?st' = true |- _ =>
    destruct (miss_state_not_user _ _ MISS INUSER)
  end.

Lemma cache_hit_simulation sst cst cst' :
  refine_state ki table sst cst ->
  hit_step cst cst' ->
  exists sst',
    Symbolic.step table sst sst' /\
    refine_state ki table sst' cst'.
Proof.
  move => [smem sregs int ? ? ? ? pc tpc ? ? REFM REFR ? MVEC WFENTRYPOINTS KINV] [INUSER INUSER' STEP].
  subst sst cst.
  inv STEP; subst mvec;
  try match goal with
  | EQ : Concrete.mkState _ _ _ _ _ = Concrete.mkState _ _ _ _ _ |- _ => inv EQ
  end;
  unfold Concrete.next_state_reg, Concrete.next_state_reg_and_pc,
         Concrete.next_state_pc, Concrete.next_state in *;
  simpl in *;
  try rewrite KER in NEXT; simpl in *;

  match_inv;

  analyze_cache; simpl in *;

  try solve [rewrite /in_user /word_lift /= (@encode_kernel_tag _ _ (e Symbolic.P)) decodeK //= in INUSER'];

  repeat match goal with
  | H : encode _ = encode _ |- _ =>
    apply encode_inj in H;
    move: H => [H]; subst
  end;

  repeat match goal with
  | MEM : PartMaps.get ?cmem ?addr = Some _,
    REFM : refine_memory ?smem ?cmem |- _ =>
    match goal with
    | _ : PartMaps.get smem addr = Some _ |- _ => fail 1
    | |- _ => idtac
    end;
    pose proof (proj1 (REFM _ _ _) MEM)
  end;

  try match goal with
  | GET : PartMaps.get ?reg ?r = Some _,
    UPD : PartMaps.upd ?reg ?r ?v@(encode (USER ?t)) = Some ?reg',
    REFR : refine_registers _ ?reg |- _ =>
    (destruct (refine_registers_upd _ v _ t REFR OLD UPD) as (? & ? & ?);
     pose proof (kernel_invariant_upd_reg ki _ _ _ _ _ v t _ KINV OLD UPD))
    || let op := current_instr_opcode in fail 3 op reg
  end;

  try match goal with
  | GET : PartMaps.get ?cmem ?addr = Some _,
    UPD : PartMaps.upd ?cmem ?addr _ = Some _,
    REFM : refine_memory _ ?cmem  |- _ =>
    (destruct (refine_memory_upd _ _ _ _ REFM GET UPD) as (? & ? & ?);
     pose proof (wf_entry_points_user_upd _ _ _ _ WFENTRYPOINTS GET UPD);
     pose proof (mvec_in_kernel_user_upd _ _ _ _ MVEC GET UPD))
    || let op := current_instr_opcode in fail 3 op
  end;

  repeat match goal with
  | REFR : refine_registers _ ?creg,
    H : PartMaps.get ?creg ?r = _ |- _ =>
    apply REFR in H
  end;

  try match goal with
  | INST : decode_instr _ = Some (Jal _ _) |- _ =>
    pose proof (in_user_no_system_call _ _ INUSER' (erefl _) WFENTRYPOINTS)
  end;

  solve [
        eexists; split;
        [ econstructor (
              solve [eauto;
                     repeat autounfold;
                     repeat match goal with
                     | H : ?x = _ |- context[?x] =>
                       rewrite H; simpl; clear H
                     end; reflexivity]
            )
        | econstructor; eauto; now rewrite decodeK ]
  ].

Qed.

Ltac simpl_word_lift :=
  match goal with
  | H : context[word_lift _ (encode _)] |- _ =>
    unfold word_lift in H;
    rewrite decodeK in H;
    simpl in H
  end.

Lemma initial_handler_state cst kst cmvec cmem' :
  forall (ISUSER : in_user cst = true)
         (CMVEC : build_cmvec _ cst = Some cmvec)
         (MEM : Concrete.store_mvec (Concrete.mem cst) cmvec = Some cmem')
         (MISS : Concrete.cache_lookup (Concrete.cache cst) masks cmvec = None)
         (STEP : Concrete.step _ masks cst kst),
      kst = Concrete.mkState cmem'
                             (Concrete.regs cst)
                             (Concrete.cache cst)
                             (Concrete.fault_handler_start mt)@Concrete.TKernel
                             (Concrete.pc cst).
Proof.
  intros.
  rewrite (lock build_cmvec) in CMVEC.
  inv STEP; try subst mvec;
  unfold Concrete.next_state_reg, Concrete.next_state_reg_and_pc,
         Concrete.next_state_pc, Concrete.next_state,
         Concrete.miss_state in *;
  match_inv; simpl in *;
  try analyze_cache; simpl in *;

  solve [
    repeat simpl_word_lift; simpl in *; discriminate |
    move: CMVEC;
    rewrite -(lock build_cmvec) /=;
    repeat match goal with
           | E : ?X = _ |- context [?X] => rewrite E; simpl
           end;
    congruence
  ].
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

Lemma build_cmvec_cache_lookup_pc cst cst' cmvec crvec :
  Concrete.step _ masks cst cst' ->
  build_cmvec _ cst = Some cmvec ->
  Concrete.cache_lookup (Concrete.cache cst) masks cmvec = Some crvec ->
  common.tag (Concrete.pc cst') = Concrete.ctrpc crvec.
Proof.
  move/stepP.
  case: cst => mem regs cache [pc tpc] epc /= STEP BUILD LOOKUP.
  move: BUILD STEP.
  case: (PartMaps.get mem pc) => [[w ti]|] //=.
  case: (decode_instr w) => [i|] //=.
  destruct i => BUILD STEP; repeat match_inv;
  unfold Concrete.next_state_pc, Concrete.next_state_reg,
         Concrete.next_state_reg_and_pc, Concrete.next_state in *;
  simpl in *;
  repeat match goal with
  | E1 : ?x = ?y1, E2 : ?x = ?y2 |- _ =>
   rewrite E1 in E2; inv E2
  end;
  try match goal with
  | LOOKUP : Concrete.cache_lookup _ _ _ = Some _,
    STEP : context[Concrete.cache_lookup _ _ _] |- _ =>
    rewrite LOOKUP in STEP
  end;
  match_inv; simpl; trivial.
  discriminate.
Qed.

Lemma kernel_cache_lookup_fail (cst cst' : Concrete.state mt) cmvec :
  in_user cst ->
  in_kernel cst' ->
  Concrete.step _ masks cst cst' ->
  ~~ cache_allows_syscall table cst ->
  wf_entry_points table (Concrete.mem cst) ->
  cache_correct (Concrete.cache cst) ->
  build_cmvec _ cst = Some cmvec ->
  Concrete.cache_lookup (Concrete.cache cst) masks cmvec = None.
Proof.
  case: cst => mem regs cache [pc tpc] epc.
  move=> INUSER INKERNEL STEP NOTALLOWED WFENTRYPOINTS CACHECORRECT BUILD.
  move: NOTALLOWED.
  rewrite /cache_allows_syscall /=.
  case GETSC: (Symbolic.get_syscall table pc) => [sc|] //=.
    case LOOKUP: (Concrete.cache_lookup cache masks _) => [res|] //= _.
    rewrite <- LOOKUP. apply f_equal.
    move: BUILD.
    rewrite /build_cmvec.
    have [i [-> /is_nopP -> //=]] := wf_entry_points_if _ WFENTRYPOINTS GETSC.
    congruence.
  case LOOKUP: (Concrete.cache_lookup cache masks _) => [crvec|] //= _.
  have E: Concrete.ctrpc crvec = Concrete.TKernel.
    move: INKERNEL.
    rewrite -(build_cmvec_cache_lookup_pc STEP BUILD LOOKUP)
             /in_kernel /Concrete.is_kernel_tag.
    by move/eqP.
  move/(_ cmvec crvec): CACHECORRECT. move: INUSER.
  rewrite (build_cmvec_ctpc _ _ _ BUILD) /= /in_user /=
          => INUSER /(_ INUSER LOOKUP) {INUSER} [ivec [ovec [? [? _]]]].
  subst cmvec crvec.
  suff: false by done.
  move: E.
  rewrite /encode_ovec /ovec_of_uovec /=.
  have [E _|NE /=] := Symbolic.op ivec =P SERVICE; last first.
    rewrite (@encode_kernel_tag _ (Symbolic.ttypes Symbolic.P) _).
    by move=> /encode_inj.
  move=> {LOOKUP}.
  have [//= i [instr [Hi Hinstr /op_to_word_inj Hinstr']]] := build_cmvec_cop_cti _ _ _ BUILD.
  have [ISNOP [t Ht]] : opcode_of instr = NOP /\ exists t, Symbolic.ti (ivec_of_uivec ivec) = ENTRY t.
    rewrite {}Hinstr'.
    move: E {BUILD Hi ovec}.
    case: ivec => op tpc' ti ts /= H.
    move: ts.
    by rewrite {}H=> _ /=; eauto.
  rewrite {}Ht in Hi.
  move: ISNOP {Hinstr'} Hinstr.
  case: instr => //= _ Hinstr.
  move: (WFENTRYPOINTS pc t) => /=.
  rewrite Hi eqxx /is_nop Hinstr /= => {E} E.
  move/E: (erefl true) => [? [? ?]].
  congruence.
Qed.

Lemma cache_miss_simulation sst cst cst' :
  refine_state ki table sst cst ->
  ~~ cache_allows_syscall table cst ->
  user_kernel_user_step cst cst' ->
  refine_state ki table sst cst'.
Proof.
  move => REF NOTALLOWED [kst ISUSER STEP KEXEC].
  have KER : in_kernel kst = true.
  { destruct KEXEC as [? EXEC]. exact (restricted_exec_fst EXEC). }
  destruct REF as [smem sregs int cmem cregs cache epc pc tpc
                   ? ? REFM REFR CACHECORRECT  MVEC WFENTRYPOINTS KINV].
  subst sst cst.
  assert (NUSER : @word_lift _ _ (e Symbolic.P) (fun t => is_user t) (common.tag (Concrete.pc kst)) = false).
  { destruct (@word_lift _ _ (e Symbolic.P) (fun t => is_user t) (common.tag (Concrete.pc kst))) eqn:EQ; trivial.
    rewrite /in_kernel in KER.
    apply is_user_pc_tag_is_kernel_tag in EQ; auto. congruence. }
  have [cmvec Hcmvec] := step_build_cmvec _ _ _ _ STEP.
  have [cmem' Hcmem'] := mvec_in_kernel_store_mvec cmvec MVEC.
  have LOOKUP := kernel_cache_lookup_fail ISUSER KER STEP NOTALLOWED WFENTRYPOINTS CACHECORRECT Hcmvec.
  have H := initial_handler_state ISUSER Hcmvec Hcmem' LOOKUP STEP.
  subst. simpl in *.
  case HANDLER: (handler _ (fun m => Symbolic.transfer m) cmvec) => [rvec|].
  - destruct (handler_correct_allowed_case cmem cmvec cregs pc@(encode (USER tpc)) int
                                           KINV HANDLER Hcmem' CACHECORRECT)
      as (cst'' & KEXEC' & CACHE' & LOOKUP' & MVEC' &
          HMEM & HREGS & HPC & WFENTRYPOINTS' & KINV').
    assert (EQ := kernel_user_exec_determ KEXEC' KEXEC). subst cst''.
    destruct cst' as [cmem'' cregs'' cache' ? ?]. simpl in *. subst.
    econstructor; eauto.
    + clear - ISUSER MVEC Hcmem' REFM HMEM.
      intros addr w t. unfold user_mem_unchanged in *.
      rewrite <- HMEM. apply REFM.
    + clear - REFR HREGS.
      intros r w t. unfold user_regs_unchanged in *.
      rewrite <- HREGS.
      apply REFR.
  - assert (EXEC : forall st st',
                     kernel_user_exec st st' ->
                     exec (Concrete.step _ masks) st st').
    { clear. intros st st' EXEC. destruct EXEC as [kst' EXEC].
      apply restricted_exec_weaken in EXEC.
      apply restricted_exec_trans with kst'; eauto. }
    assert (ISUSER' : in_kernel cst' = false).
    { destruct KEXEC. eauto. }
    apply EXEC in KEXEC.
    destruct (handler_correct_disallowed_case cmem cmvec int KINV HANDLER Hcmem' ISUSER' KEXEC).
Qed.

Lemma syscall_simulation sst cst cst' :
  refine_state ki table sst cst ->
  cache_allows_syscall table cst ->
  user_kernel_user_step cst cst' ->
  exists sst', Symbolic.step table sst sst' /\
               refine_state ki table sst' cst'.
Proof.
  intros REF ALLOWED STEP.
  destruct REF as [smem sregs int cmem cregs cache epc pc tpc
                   ? ? REFM REFR CACHE MVEC WFENTRYPOINTS KINV].
  subst sst cst.
  have [sc GETCALL]: (exists sc, Symbolic.get_syscall table pc = Some sc).
  { rewrite /cache_allows_syscall in ALLOWED.
    case GETCALL: (Symbolic.get_syscall table pc) ALLOWED => [sc|//] ALLOWED.
    by eauto. }
  case SCEXEC: (Symbolic.run_syscall sc (Symbolic.State smem sregs pc@tpc int))
    => [[smem' sregs' [pc' tpc'] int']|].
  - exploit syscalls_correct_allowed_case; eauto.
    intros (cmem' & creg' & cache' & pct' & EXEC' &
            REFM' & REFR' & CACHE' & MVEC' & WFENTRYPOINTS' & KINV').
    generalize (user_kernel_user_step_determ STEP EXEC'). intros ?. subst.
    { exists (Symbolic.State smem' sregs' pc'@tpc' int'). split.
      - eapply Symbolic.step_syscall; eauto.
        eapply wf_entry_points_if in GETCALL; last by exact WFENTRYPOINTS.
        move: GETCALL => [i [GETPC ISNOP]].
        case GET': (PartMaps.get smem pc) => [[? ?]|] //.
        move/REFM: GET' => GET'.
        rewrite GETPC in GET'.
        move: GET' => [? H].
        by apply encode_inj in H.
      - econstructor; eauto. }
  - destruct (syscalls_correct_disallowed_case _ _ KINV REFM REFR CACHE MVEC
                                               WFENTRYPOINTS GETCALL SCEXEC ALLOWED STEP).
Qed.

Lemma user_into_kernel sst cst cst' :
  refine_state ki table sst cst ->
  Concrete.step _ masks cst cst' ->
  in_user cst' = false ->
  in_kernel cst' = true.
Proof.
  intros REF STEP NUSER.
  move: (refine_state_in_user REF) => INUSER.
  destruct (in_kernel cst') eqn:NKERNEL; trivial.
  unfold in_user in NUSER.
  unfold in_kernel, Concrete.is_kernel_tag in NKERNEL.
  rewrite (@encode_kernel_tag _ _ (e Symbolic.P)) in NKERNEL.
  destruct REF as [? ? ? ? ? ? ? ? ? ? ? ? ? CACHE ? ? ?].
  subst sst cst.
  assert (PCS := valid_pcs STEP CACHE INUSER).
  rewrite /word_lift in NUSER.
  destruct (decode (common.tag (Concrete.pc cst'))) as [[t| |]|] eqn:DEC;
  try discriminate; simpl in *;
  apply encodeK in DEC.
  rewrite <- DEC in NKERNEL.
  rewrite eq_tag_eq_word // in NKERNEL.
Qed.

Definition refine_state_weak sst cst :=
  refine_state ki table sst cst \/
  exists cst0 kst,
    refine_state ki table sst cst0 /\
    Concrete.step _ masks cst0 kst /\
    kernel_exec kst cst.

Lemma backwards_simulation sst cst cst' :
  refine_state_weak sst cst ->
  Concrete.step _ masks cst cst' ->
  refine_state_weak sst cst' \/
  exists sst',
    Symbolic.step table sst sst' /\
    refine_state ki table sst' cst'.
Proof.
  intros [REF | (cst0 & kst & REF & KSTEP & EXEC)] STEP.
  - assert (USER : in_user cst = true) by (eapply refine_state_in_user; eauto).
    destruct (in_user cst') eqn:USER'.
    + right.
      eapply cache_hit_simulation; eauto.
      by constructor; auto.
    + left. right. do 2 eexists. do 2 (split; eauto).
      constructor.
      by eapply user_into_kernel; eauto.
  - assert (USER : in_user cst0 = true) by (eapply refine_state_in_user; eauto).
    destruct (in_kernel cst') eqn:KER'.
    + left. right.
      do 2 eexists. do 2 (split; eauto).
      eapply restricted_exec_trans; eauto.
      have KER : in_kernel cst = true by eapply restricted_exec_snd in EXEC.
      eapply re_step; by eauto using user_into_kernel.
    + assert (EXEC' : user_kernel_user_step cst0 cst').
      { econstructor; eauto.
        econstructor; eauto using in_user_in_kernel. }
      case: (boolP (cache_allows_syscall table cst0)) => [ALLOWED | NOTALLOWED].
      * right. by eapply syscall_simulation; eauto.
      * left. left. by eapply cache_miss_simulation; eauto.
Qed.

Theorem backwards_refinement sst cst cst' :
  refine_state ki table sst cst ->
  exec (Concrete.step _ masks) cst cst' ->
  in_user cst' = true ->
  exists sst',
    exec (Symbolic.step table) sst sst' /\
    refine_state ki table sst' cst'.
Proof.
  intros REF EXEC USER'.
  have {REF} REF: refine_state_weak sst cst by left.
  move: sst REF.
  induction EXEC as [cst _|cst cst'' cst' _ STEP EXEC IH].
  - move => sst [? | REF]; first by eauto.
    destruct REF as (? & ? & ? & ? & EXEC).
    apply restricted_exec_snd in EXEC.
    apply in_user_in_kernel in USER'. congruence.
  - move => sst REF.
    exploit backwards_simulation; eauto.
    intros [REF' | (sst' & SSTEP & REF')]; first by auto.
    have {REF'} REF': refine_state_weak sst' cst'' by left.
    move: (IH USER' _ REF') => {IH USER' REF'} [sst'' [EXEC' REF']].
    eexists. split; last by eauto.
    eapply re_step; trivial; eauto.
Qed.

End Refinement.
