Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq.
Require Import CoqUtils.hseq CoqUtils.word CoqUtils.partmap.

Require Import lib.utils.
Require Import common.types.
Require Import concrete.concrete.
Require Import concrete.exec.
Require Import symbolic.symbolic.
Require Import symbolic.exec.
Require Import symbolic.rules.
Require Import symbolic.refinement_common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Hint Constructors restricted_exec.
Hint Unfold exec.
Hint Resolve restricted_exec_trans.

Section Refinement.

Context {mt : machine_types}
        {ops : machine_ops mt}
        {opss : machine_ops_spec ops}
        {sp : Symbolic.params}
        {e : encodable mt Symbolic.ttypes}
        {mi : monitor_invariant}
        {table : seq (Symbolic.syscall mt)}
        {mcc : monitor_code_bwd_correctness mi table}.

Hint Unfold Symbolic.next_state.
Hint Unfold Symbolic.next_state_reg_and_pc.
Hint Unfold Symbolic.next_state_pc.
Hint Unfold Symbolic.next_state_reg.

Hint Resolve monitor_invariant_upd_mem.
Hint Resolve monitor_invariant_upd_reg.
Hint Resolve monitor_invariant_store_mvec.

Ltac check_conv t1 t2 :=
  let e := constr:(erefl t1 : t1 = t2) in idtac.

Ltac contradict_in_user :=
  match goal with
  | INUSER : is_true (in_user ?st),
    ISMONITOR : ?t = Concrete.TMonitor |- _ =>
    check_conv (Concrete.pct st) t;
    first [ rewrite ISMONITOR /in_user /= decode_monitor_tag in INUSER; done |
            failwith "contradict_in_user" ]
  end.

Ltac destruct_hseq :=
  repeat match goal with
  | x : hseq _ _ |- _ => simpl in x
  | x : hseq_nil |- _ => destruct x
  | x : hseq_cons _ _ |- _ => destruct x
  end.

Ltac analyze_cache :=
  match goal with
  | LOOKUP : Concrete.cache_lookup ?cache _ ?mvec = Some ?rvec,
    PC     : getm _ ?pc = Some ?i@_,
    INST   : decode_instr ?i = Some _,
    INUSER : is_true (in_user (Concrete.State _ _ _ ?pc@_ _)),
    CACHE  : cache_correct ?cache ?cmem |- _ =>
    first [
        assert (CACHEHIT := analyze_cache CACHE LOOKUP INUSER);
        simpl in CACHEHIT;
        repeat match type of CACHEHIT with
        | exists _, _ => destruct CACHEHIT as [? CACHEHIT]
        | _ /\ _ => destruct CACHEHIT as [? CACHEHIT]
        | _ \/ _ => destruct CACHEHIT as [CACHEHIT | CACHEHIT]
        | and3 _ _ _ => destruct CACHEHIT
        | and4 _ _ _ _ => destruct CACHEHIT
        | False => destruct CACHEHIT
        end;
        try contradict_in_user; destruct_hseq; match_inv; simpl in *
      | failwith "analyze_cache hit" ]
  | INUSER : is_true (in_user (Concrete.miss_state ?st ?mvec)) |- _ =>
    first [ destruct (negP (miss_state_not_user st mvec) INUSER) |
            failwith "analyze_cache miss" ]
  end.

Ltac relate_register_get :=
  match goal with
  | REFR : refine_registers ?areg ?creg ?cmem,
    GET : getm ?creg ?r = Some _@?t,
    DEC : decode Symbolic.R ?cmem ?t = Some _ |- _ =>
    match goal with
    | GET' : getm areg r = Some _ |- _ => fail 1
    | |- _ => first [ pose proof (proj1 REFR _ _ _ _ DEC GET) |
                      failwith "relate_register_get" ]
    end
  end.

Ltac relate_memory_get :=
  match goal with
  | MEM : getm ?cmem ?addr = Some _@?t,
    REFM : refine_memory ?smem ?cmem,
    DEC : decode Symbolic.M ?cmem ?t = Some (User _) |- _ =>
    match goal with
    | _ : getm smem addr = Some _ |- _ => fail 1
    | |- _ => idtac
    end;
    first [ pose proof (proj1 REFM _ _ _ _ DEC MEM) |
            failwith "relate_memory_get" ]
  end.

Ltac relate_register_upd :=
  match goal with
  | GET : getm ?reg ?r = Some _@?t,
    DEC : decode Symbolic.R ?cmem ?t = Some _,
    UPD : updm ?reg ?r ?v@?t' = Some ?reg',
    DEC' : decode Symbolic.R ?cmem ?t' = Some _,
    REFR : refine_registers _ ?reg ?cmem,
    MINV : monitor_invariant_statement ?mi ?cmem _ _ _ |- _ =>
    first [ destruct (refine_registers_upd REFR GET DEC UPD DEC') as [? ? ?];
            pose proof (monitor_invariant_upd_reg MINV GET DEC UPD DEC')
          | failwith "relate_register_upd" ]
  end.

Ltac relate_memory_upd :=
  match goal with
  | GET : getm ?cmem ?addr = Some _@?t,
    DEC : decode Symbolic.M ?cmem ?t = Some (User _),
    UPD : updm ?cmem ?addr _@?t' = Some _,
    DEC' : decode Symbolic.M ?cmem ?t' = Some (User _),
    CACHE : cache_correct _ ?cmem,
    REFR : refine_registers _ _ ?cmem,
    REFM : refine_memory _ ?cmem,
    WFENTRYPOINTS : wf_entry_points _ ?cmem,
    MVEC : mvec_in_monitor ?cmem |- _ =>
    first [ destruct (refine_memory_upd CACHE REFR REFM GET DEC UPD DEC') as [? [? ? ?]];
            pose proof (wf_entry_points_user_upd WFENTRYPOINTS GET DEC UPD DEC');
            pose proof (mvec_in_monitor_user_upd MVEC GET DEC UPD DEC')
          | failwith "relate_memory_upd" ]
  end.

Ltac update_decodings :=
  match goal with
  | DEC : decode ?k ?cmem ?ct = Some ?ut,
    UPD : updm ?cmem _ _ = Some ?cmem' |-
    decode ?k ?cmem' ?ct = Some ?ut =>
    first [ solve [ rewrite /= -DEC (updm_set UPD);
                    erewrite decode_monotonic; eauto ] |
            failwith "update_decodings" ]
  end.

Ltac find_and_rewrite :=
  match goal with
  | H : ?x = _ |- context[?x] =>
    rewrite H; clear H; simpl
  end.

Ltac simplify_eqs :=
  match goal with
  | E1 : ?x = ?y1,
    E2 : ?x = ?y2 |- _ =>
    rewrite E1 in E2;
    inversion E2; subst; clear E2
  end.

Ltac solve_step :=
  solve [
      s_econstructor (
          solve [eauto;
                 repeat autounfold;
                 repeat simplify_eqs;
                 repeat (find_and_rewrite; simpl);
                 reflexivity])
    | failwith "solve_step" ].

Ltac solve_refine_state :=
  solve [ econstructor; eauto; try update_decodings
        | failwith "solve_refine_state" ].

Lemma refine_ivec_inv sst cst cmvec ivec :
  refine_state mi table sst cst ->
  build_cmvec cst = Some cmvec ->
  decode_ivec e (Concrete.mem cst) cmvec = Some ivec ->
  build_ivec table sst = Some ivec.
Proof.
  move=> Href Hbuild /decode_ivec_inv /=.
  case: ivec => [[op|] tpc ti ts]; last first.
    case=> [Hop Hdec_tpc Hdec_ti].
    rewrite (build_cmvec_ctpc Hbuild) in Hdec_tpc.
    have [i [instr [Hget Hdec_i Hop']]] := build_cmvec_cop_cti Hbuild.
    move: Hop. rewrite -{}Hop'.
    case: instr Hdec_i => // /is_nopP Hdec_i _.
    have [sc Hget_sc Hsct] := wf_entry_points_only_if (rs_entry_points Href)
                                                      Hget Hdec_ti Hdec_i.
    rewrite /build_ivec (rs_pc Href).
    case Hget': (getm _ _) => [[i' ti']|] //=.
      have [cti] := proj2 (rs_refm Href) _ _ _ Hget'.
      rewrite Hget => Hdec_ti' [? ?]. subst i' cti.
      by rewrite Hdec_ti' in Hdec_ti.
    rewrite (rs_pct Href) in Hdec_tpc.
    case: Hdec_tpc => ->. rewrite Hget_sc Hsct.
    by rewrite [in RHS]hseq0.
  case=> [Hop Hpriv Hdec_tpc Hdec_ti Hdec_ts].
  move: ti ts Hdec_ti Hdec_ts; rewrite {}Hop => ti ts Hdec_ti Hdec_ts.
  rewrite (build_cmvec_ctpc Hbuild) (rs_pct Href) in Hdec_tpc.
  case: Hdec_tpc => ?. subst tpc.
  have [i [instr [Hget_i Hdec_i Hop']]] := build_cmvec_cop_cti Hbuild.
  move: ts Hdec_ts; rewrite -{}Hop'=> ts Hdec_ts.
  move: Hbuild.
  rewrite /build_cmvec /build_ivec (rs_pc Href) Hget_i Hdec_i.
  rewrite (proj1 (rs_refm Href) _ _ _ _ Hdec_ti Hget_i) Hdec_i /=.
  destruct Href, instr, cmvec; move=> Hbuild; simpl in *; match_inv;
  repeat match goal with
  | x : hseq_nil |- _ => destruct x
  | x : hseq_cons _ _ |- _ => destruct x
  | x : atom _ _ |- _ => destruct x
  | H : Some _ = Some _ |- _ => inv H
  end; simpl in *; match_inv;
  repeat relate_register_get;
  repeat relate_memory_get;
  trivial; repeat find_and_rewrite; by trivial.
Qed.

Lemma cache_hit_simulation sst cst cst' :
  refine_state mi table sst cst ->
  hit_step cst cst' ->
  exists2 sst',
    Symbolic.step table sst sst' &
    refine_state mi table sst' cst'.
Proof.
  case: sst => smem sregs [pc atpc] int.
  move => [/= PC DEC REFM REFR CACHE MVEC WFENTRYPOINTS MINV] [INUSER INUSER' STEP].
  rewrite /Symbolic.pcv /= in PC. subst pc.
  inv STEP; subst mv;
  unfold Concrete.next_state_reg, Concrete.next_state_reg_and_pc,
         Concrete.next_state_pc, Concrete.next_state in *;
  simpl in *;
  try rewrite KER in NEXT; simpl in *;

  match_inv;

  analyze_cache;

  repeat relate_register_get;

  repeat relate_memory_get;

  try relate_register_upd;

  try relate_memory_upd;

  (eexists; [ solve_step | solve_refine_state ]).

Qed.

Lemma initial_handler_state cst kst cmvec :
  forall (CMVEC : build_cmvec cst = Some cmvec)
         (MISS : Concrete.cache_lookup (Concrete.cache cst) masks cmvec = None)
         (STEP : Concrete.step _ masks cst kst),
      kst = Concrete.State (Concrete.store_mvec (Concrete.mem cst) cmvec)
                             (Concrete.regs cst)
                             (Concrete.cache cst)
                             (Concrete.fault_handler_start mt)@Concrete.TMonitor
                             (Concrete.pc cst).
Proof.
  move=> BUILD LOOKUP /step_lookup_success_or_fault.
  rewrite BUILD.
  case=> [cmvec' [[<-]]] {cmvec'}.
  by rewrite LOOKUP.
Qed.

Lemma monitor_user_exec_determ k s1 s2 :
  monitor_user_exec k s1 ->
  monitor_user_exec k s2 ->
  s1 = s2.
Proof.
  unfold monitor_user_exec. intros EXEC1 EXEC2.
  eapply exec_until_determ; eauto.
  - clear. intros s s1 s2.
    do 2 rewrite <- concrete.exec.stepP in *. congruence.
  - clear. by move=> s /= ->.
  - clear. by move=> s /= ->.
Qed.

Lemma user_monitor_user_step_determ s s1 s2 :
  user_monitor_user_step s s1 ->
  user_monitor_user_step s s2 ->
  s1 = s2.
Proof.
  move => [s' USER1 STEP1 EXEC1] [s'' USER2 STEP2 EXEC2].
  have E: (s' = s'') by rewrite <- concrete.exec.stepP in *; congruence. subst s''.
  eauto using monitor_user_exec_determ.
Qed.

Lemma build_cmvec_cache_lookup_pc cst cst' cmvec crvec :
  Concrete.step _ masks cst cst' ->
  build_cmvec cst = Some cmvec ->
  Concrete.cache_lookup (Concrete.cache cst) masks cmvec = Some crvec ->
  taga (Concrete.pc cst') = Concrete.ctrpc crvec.
Proof.
  move=> STEP BUILD LOOKUP.
  move/step_lookup_success_or_fault: STEP.
  rewrite BUILD.
  case=> cmvec' [[<-]] {cmvec'}.
  by rewrite LOOKUP.
Qed.

Lemma monitor_cache_lookup_fail (cst cst' : Concrete.state mt) cmvec :
  in_user cst ->
  in_monitor cst' ->
  Concrete.step _ masks cst cst' ->
  ~~ cache_allows_syscall table cst ->
  wf_entry_points table (Concrete.mem cst) ->
  cache_correct (Concrete.cache cst) (Concrete.mem cst) ->
  build_cmvec cst = Some cmvec ->
  Concrete.cache_lookup (Concrete.cache cst) masks cmvec = None.
Proof.
  move=> INUSER INMONITOR STEP NOTALLOWED WFENTRYPOINTS CACHECORRECT BUILD.
  move/step_lookup_success_or_fault: STEP NOTALLOWED.
  rewrite /cache_allows_syscall BUILD.
  case=> cmvec' [[<-]] {cmvec'}.
  case LOOKUP: (Concrete.cache_lookup _ _ _) => [[ctrpc ctr]|] //= E. subst ctrpc.
  case GETSC: (Symbolic.get_syscall _ _) => [sc|] //=.
  move: INMONITOR LOOKUP.
  rewrite /in_monitor /Concrete.is_monitor_tag => /eqP -> LOOKUP _.
  rewrite /in_user /= -(build_cmvec_ctpc BUILD) in INUSER.
  case/(_ cmvec _ LOOKUP INUSER): CACHECORRECT => ivec [ovec [/decode_ivec_inv DECi DECo _]].
  case: ivec DECi ovec DECo => [[op|] tpc ti ts] /= => [[E Hpriv _ _ _]|[DECop _ DECti]].
    by rewrite {}E /decode_ovec /= decode_monitor_tag /= => ovec.
  suff : false by done.
  move: (build_cmvec_cop_cti BUILD) DECop => [i [instr [GETPC DECi <-]]] DECop.
  have {DECi} ISNOP : is_nop i by rewrite /is_nop {}DECi; case: instr DECop.
  move: (wf_entry_points_only_if WFENTRYPOINTS GETPC DECti ISNOP).
  by rewrite GETSC; case.
Qed.

Lemma cache_miss_simulation sst cst cst' :
  refine_state mi table sst cst ->
  ~~ cache_allows_syscall table cst ->
  user_monitor_user_step cst cst' ->
  refine_state mi table sst cst'.
Proof.
  case: sst => smem sregs [pc tpc] int.
  case: cst => cmem cregs cache [pc' ctpc] epc.
  move => REF NOTALLOWED [kst ISUSER STEP KEXEC].
  have KER : in_monitor kst = true.
  { destruct KEXEC as [? EXEC]. exact (restricted_exec_fst EXEC). }
  case: REF=> [//= PC DEC REFM REFR CACHECORRECT MVEC WFENTRYPOINTS MINV].
  rewrite /Concrete.pcv /= in PC. subst pc'.
  have ISUSER' : ~~ in_monitor cst' by case: KEXEC.
  have [cmvec Hcmvec] := step_build_cmvec STEP.
  have LOOKUP := monitor_cache_lookup_fail ISUSER KER STEP NOTALLOWED WFENTRYPOINTS CACHECORRECT Hcmvec.
  have H := initial_handler_state Hcmvec LOOKUP STEP.
  have EXEC : exec (Concrete.step _ masks) kst cst'.
    case: KEXEC => kst' EXEC _ STEP'.
    apply restricted_exec_weaken in EXEC.
    by apply restricted_exec_trans with kst'; eauto.
  subst kst. rewrite /= in STEP KEXEC EXEC KER LOOKUP.
  destruct (handler_correct_allowed_case_bwd MINV CACHECORRECT KEXEC)
      as (ivec & ovec & DECivec & TRANS & CACHE' & MVEC' &
          HPCT & HMEM & HREGS & HPC & WFENTRYPOINTS' & MINV').
  case: cst' {KEXEC EXEC} HPC CACHE'
             ISUSER' MVEC' HPCT HMEM HREGS WFENTRYPOINTS' MINV' =>
        cmem'' cregs'' cache' pc' ? /= -> {pc'} CACHE' ISUSER' MVEC' HPCT HMEM HREGS WFENTRYPOINTS' MINV'.
  econstructor; eauto.
  - by apply/HPCT.
  - split.
    + move=> w x ctg atg {DECivec DEC} /HPCT DEC GET.
      move: (HMEM w x ctg _ DEC) GET => H /H {H} ?.
      by eapply (proj1 REFM); eauto.
    + move=> w x atg /(proj2 REFM) {DEC} [ctg DEC GET].
      move: DEC (HMEM w x ctg _ DEC) GET => /HPCT DEC H /H {H} ? /=.
      by eauto.
  - split.
    + move=> r x ctg atg {DECivec DEC} /HPCT DEC GET.
      move: (HREGS r x ctg _ DEC) GET => H /H {H} ?.
      by eapply (proj1 REFR); eauto.
    + move=> r x atg /(proj2 REFR) {DEC} [ctg DEC GET].
      move: DEC (HREGS r x ctg _ DEC) GET => /HPCT DEC H /H {H} ? /=.
      by eauto.
Qed.

Lemma syscall_simulation sst cst cst' :
  refine_state mi table sst cst ->
  cache_allows_syscall table cst ->
  user_monitor_user_step cst cst' ->
  exists2 sst', Symbolic.step table sst sst' &
                refine_state mi table sst' cst'.
Proof.
  case: sst=> smem sregs [pc tpc] int.
  case: cst=> cmem cregs cache [pc' ctpc] epc.
  intros REF ALLOWED STEP.
  case: REF=> [//= PC DEC REFM REFR CACHE MVEC WFENTRYPOINTS MINV].
  rewrite /Concrete.pcv /= in PC. subst pc'.
  have [sc GETCALL]: (exists sc, Symbolic.get_syscall table pc = Some sc).
  { rewrite /cache_allows_syscall in ALLOWED.
    case GETCALL: (Symbolic.get_syscall table pc) ALLOWED => [sc|//] ALLOWED.
    by eauto. }
  destruct cst' as [cmem' creg' cache' [cpc' ctpc'] epc'].
  have := syscalls_correct_allowed_case_bwd MINV REFM REFR CACHE MVEC GETCALL
                                            DEC ALLOWED STEP.
  move/(_ mcc).
  intros (smem' & sregs' & stpc' & sint' & RUNSC &
          HPCT & REFM' & REFR' & CACHE' & MVEC' & WFENTRYPOINTS' & MINV').
  exists (Symbolic.State smem' sregs' cpc'@stpc' sint').
  - eapply Symbolic.step_syscall; eauto.
    eapply wf_entry_points_if in GETCALL; last by exact WFENTRYPOINTS.
    move: GETCALL => [i [ti [GETPC DECti ISNOP]]].
    case GET': (getm smem pc) => [[? ?]|] //.
    move: (proj2 REFM _ _ _ GET') => {GET' DEC} [ctg' DEC GET'].
    rewrite GETPC in GET'.
    move: GET' => [? H]. subst i ti.
    by rewrite DEC in DECti.
  - by econstructor; eauto.
Qed.

Lemma user_into_monitor sst cst cst' :
  refine_state mi table sst cst ->
  Concrete.step _ masks cst cst' ->
  ~~ in_user cst'->
  in_monitor cst'.
Proof.
  move=> REF STEP NUSER.
  move: (refine_state_in_user REF) => INUSER.
  case: REF => [? ? ? ? CACHE ? ? ?]. subst.
  move : (valid_pcs STEP CACHE INUSER) NUSER.
  rewrite /in_monitor /Concrete.is_monitor_tag /in_user.
  move => [[t ->]|->] //=.
Qed.

Definition refine_state_weak sst cst :=
  refine_state mi table sst cst \/
  exists cst0 kst,
    refine_state mi table sst cst0 /\
    Concrete.step _ masks cst0 kst /\
    monitor_exec kst cst.

Lemma backwards_simulation sst cst cst' :
  refine_state_weak sst cst ->
  Concrete.step _ masks cst cst' ->
  refine_state_weak sst cst' \/
  exists2 sst',
    Symbolic.step table sst sst' &
    refine_state mi table sst' cst'.
Proof.
  intros [REF | (cst0 & kst & REF & KSTEP & EXEC)] STEP.
  - have USER : in_user cst by eapply refine_state_in_user; eauto.
    have [USER'|USER'] := boolP (in_user cst').
    + right.
      eapply cache_hit_simulation; eauto.
      by constructor; auto.
    + left. right. do 2 eexists. do 2 (split; eauto).
      constructor.
      by eapply user_into_monitor; eauto.
  - have USER : in_user cst0 by eapply refine_state_in_user; eauto.
    have [KER'|KER'] := boolP (in_monitor cst').
    + left. right.
      do 2 eexists. do 2 (split; eauto).
      eapply restricted_exec_trans; eauto.
      have KER : in_monitor cst by eapply restricted_exec_snd in EXEC.
      eapply re_step; by eauto using user_into_monitor.
    + assert (EXEC' : user_monitor_user_step cst0 cst').
      { econstructor; eauto.
        econstructor; eauto using in_user_in_monitor. }
      case: (boolP (cache_allows_syscall table cst0)) => [ALLOWED | NOTALLOWED].
      * right. by eapply syscall_simulation; eauto.
      * left. left. by eapply cache_miss_simulation; eauto.
Qed.

Lemma monitor_step cst cst' ast kst cst0 :
  refine_state mi table ast cst0 ->
  Concrete.step ops rules.masks cst0 kst ->
  monitor_exec kst cst ->
  Concrete.step _ masks cst cst' ->
  in_monitor cst ->
  ~~ in_user cst' ->
  in_monitor cst'.
Proof.
  intros REF STEP EXEC STEP' INMONITOR INUSER.
  assert (REFW: refine_state_weak ast cst).
  { right. eauto. }
  generalize (backwards_simulation REFW STEP').
  intros [[REF' | (? & ? & ? & ? & KEXEC')] | [? _ REF']].
  - apply @refine_state_in_user in REF'. by rewrite REF' in INUSER.
  - by apply restricted_exec_snd in KEXEC'.
  - apply @refine_state_in_user in REF'. by rewrite REF' in INUSER.
Qed.

Theorem backwards_refinement sst cst cst' :
  refine_state mi table sst cst ->
  exec (Concrete.step _ masks) cst cst' ->
  in_user cst' ->
  exists2 sst',
    exec (Symbolic.step table) sst sst' &
    refine_state mi table sst' cst'.
Proof.
  intros REF EXEC USER'.
  have {REF} REF: refine_state_weak sst cst by left.
  move: sst REF.
  induction EXEC as [cst _|cst cst'' cst' _ STEP EXEC IH].
  - move => sst [? | REF]; first by eauto.
    destruct REF as (? & ? & ? & ? & EXEC).
    apply restricted_exec_snd in EXEC.
    apply in_user_in_monitor in USER'.
    by rewrite EXEC in USER'.
  - move => sst REF.
    have [REF' | [sst' SSTEP REF']] := backwards_simulation REF STEP;
      first by auto.
    have {REF'} REF': refine_state_weak sst' cst'' by left.
    move: (IH USER' _ REF') => {IH USER' REF'} [sst'' EXEC' REF'].
    eexists; last by eauto.
    eapply re_step; trivial; eauto.
Qed.

End Refinement.
