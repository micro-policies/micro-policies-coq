Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.ssrnat Ssreflect.seq.

Require Import lib.utils.
Require Import common.types.
Require Import concrete.concrete.
Require Import concrete.exec.
Require Import symbolic.symbolic.
Require Import symbolic.exec.
Require Import symbolic.rules.
Require Import symbolic.refinement_common.

Require Import CoqUtils.word CoqUtils.partmap.

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
        {ki : kernel_invariant}
        {table : seq (Symbolic.syscall mt)}
        {kcc : kernel_code_fwd_correctness ki table}.

Hint Unfold Symbolic.next_state.
Hint Unfold Symbolic.next_state_reg_and_pc.
Hint Unfold Symbolic.next_state_pc.
Hint Unfold Symbolic.next_state_reg.

Hint Resolve kernel_invariant_upd_mem.
Hint Resolve kernel_invariant_upd_reg.
Hint Resolve kernel_invariant_store_mvec.

Hint Unfold Concrete.next_state_reg.
Hint Unfold Concrete.next_state_reg_and_pc.
Hint Unfold Concrete.next_state_pc.
Hint Unfold Concrete.next_state.
Hint Unfold Concrete.miss_state.

Lemma user_mem_unchanged_refine_memory amem cmem cmem' :
  refine_memory amem cmem ->
  user_tags_unchanged cmem cmem' ->
  user_mem_unchanged cmem cmem' ->
  refine_memory amem cmem'.
Proof.
  move=> [REF1 REF2] Htags USERMEM.
  split.
  - move=> w x ctg atg /Htags DEC GET.
    move: (USERMEM w x ctg _ DEC) GET => H /H {H} GET.
    by eauto.
  - move=> w x atg /REF2 [ctg DEC GET].
    move: (USERMEM w x ctg _ DEC) GET => H /H {H} GET.
    move/Htags in DEC.
    by eauto.
Qed.

Lemma user_regs_unchanged_refine_registers areg creg creg' cmem cmem' :
  refine_registers areg creg cmem ->
  user_tags_unchanged cmem cmem' ->
  user_regs_unchanged creg creg' cmem ->
  refine_registers areg creg' cmem'.
Proof.
  move=> [REF1 REF2] Htags USERREGS.
  split.
  - move=> r x ctg atg /Htags DEC GET.
    move: (USERREGS r x ctg _ DEC) GET => H /H {USERREGS H} GET.
    by eauto.
  - move=> r x atg /REF2 [ctg DEC GET].
    move: (USERREGS r x ctg _ DEC) GET => H /H {USERREGS H} GET.
    move/Htags in DEC.
    by eauto.
Qed.

Ltac check_conv t1 t2 :=
  let e := constr:(erefl t1 : t1 = t2) in idtac.

Ltac match_mem_get REF sst cst :=
  match goal with
  | GET : getm ?smem ?addr = Some ?w@?t |- _ =>
    check_conv smem (Symbolic.mem sst);
    match goal with
    | _ : getm ?cmem addr = _ |- _ => check_conv cmem (Concrete.mem cst); fail 1
    | |- _ => idtac
    end;
    first [ have [? ? ?] := proj2 (rs_refm REF) _ _ _ GET
          | failwith "match_mem" ]
  end.

Ltac match_mem_upd REF sst cst :=
  match goal with
  | UPD : updm ?smem ?addr ?w@?t = Some ?smem',
    DEC : decode Symbolic.M ?cmem ?ct = Some (USER ?t) |- _ =>
    check_conv smem (Symbolic.mem sst);
    match goal with
    | _ : refine_memory smem' ?cmem',
      _ : updm cmem ?addr _ = Some ?cmem' |- _ => fail 1
    | |- _ => idtac
    end;
    first [ let cmem' := fresh "cmem'" in
            let UPD' := fresh "UPD'" in
            let REFR' := fresh "REFR'" in
            let REFM' := fresh "REFM'" in
            let CACHE' := fresh "CACHE'" in
            destruct (refine_memory_upd' (rs_cache REF) (rs_refr REF) (rs_refm REF) UPD DEC)
              as (cmem' & [UPD' CACHE' REFR' REFM'])
          | failwith "match_mem_upd" ]
  end.

Ltac match_mem_unchanged REF sst cst :=
  match goal with
  | USERMEM : user_mem_unchanged ?cmem ?cmem' |- _ =>
    check_conv cmem (Concrete.mem cst);
    match goal with
    | _ : refine_memory ?smem cmem' |- _ => check_conv smem (Symbolic.mem sst); fail 1
    | |- _ => idtac
    end;
    first [ pose proof (user_mem_unchanged_refine_memory (rs_refm REF) USERMEM)
          | failwith "match_mem_unchanged" ]
  end.

Ltac match_mem_unchanged_tags :=
  match goal with
  | GET : getm ?mem1 ?addr = Some ?x@?ct,
    DEC : decode Symbolic.M ?mem1 ?ct = Some (USER ?t),
    USERMEM : user_mem_unchanged ?mem1 ?mem2 |- _ =>
    match goal with
    | _ : getm mem2 addr = _ |- _ => fail 1
    | |- _ => idtac
    end;
    first [ let GET' := fresh "GET'" in
            have GET' := proj1 (USERMEM _ _ _ _ DEC) GET
          | failwith "match_mem_unchanged_tags" ]
  end.

Ltac match_reg_get REF sst cst :=
  match goal with
  | GET : getm ?sregs ?r = Some ?w@?t |- _ =>
    check_conv sregs (Symbolic.regs sst);
    match goal with
    | _ : getm ?cregs r = Some _ |- _ => check_conv cregs (Concrete.regs cst); fail 1
    | |- _ => idtac
    end;
    first [ destruct (proj2 (rs_refr REF) _ _ _ GET) as [? ? ?]
          | failwith "match_reg_get" ]
  end.

Ltac match_reg_upd REF sst cst :=
  match goal with
  | UPD : updm ?sregs ?r ?w@?t = Some ?sregs',
    DEC : decode Symbolic.R ?cmem ?ct = Some (USER ?t) |- _ =>
    check_conv sregs (Symbolic.regs sst);
    match goal with
    | _ : refine_registers sregs' ?cregs' cmem,
      _ : updm _ r _ = Some ?cregs' |- _ => fail 1
    | |- _ => idtac
    end;
    let cregs' := fresh "cregs'" in
    let UPD' := fresh "UPD'" in
    let REFR' := fresh "REFR'" in
    first [ destruct (refine_registers_upd' (rs_refr REF) UPD DEC) as [cregs' UPD' REFR']
          | failwith "match_reg_upd" ]
  end.

Ltac match_reg_unchanged REF sst cst :=
  match goal with
  | USERREGS : user_regs_unchanged ?cregs ?cregs' |- _ =>
    check_conv cregs (Concrete.regs cst);
    match goal with
    | _ : refine_registers ?sregs cregs' |- _ => check_conv sregs (Symbolic.regs sst); fail 1
    | |- _ => idtac
    end;
    first [ pose proof (user_regs_unchanged_refine_registers (rs_refr REF) USERREGS)
          | failwith "match_reg_unchanged" ]

  end.

Ltac match_pc_tag :=
  match goal with
  | GET : getm ?cmem ?addr = Some ?w@?ct,
    DEC : decode Symbolic.M ?cmem ?ct = Some (USER ?st),
    UPD : updm ?cmem ?addr ?w'@?ct' = Some ?cmem',
    DEC' : decode Symbolic.M ?cmem ?ct' = Some (USER ?st'),
    DECPC : decode Symbolic.P ?cmem ?cpct = Some (USER ?spct) |- _ =>
    match goal with
    | _ : decode Symbolic.P cmem' cpct = Some (USER spct) |- _ => fail 1
    | |- _ => idtac
    end;
    let DECPC' := fresh "DECPC'" in
    first [ have DECPC' : decode Symbolic.P cmem' cpct = Some (USER spct)
            by rewrite (updm_set UPD) /=; erewrite decode_monotonic; eauto |
            failwith "match_pc_tag" ]
  end.

Ltac match_data :=
  match goal with
  | REF : refine_state _ _ ?sst ?cst |- _ =>
    repeat first [ match_mem_get REF sst cst
                 | match_mem_upd REF sst cst
                 | match_mem_unchanged REF sst cst
                 | match_mem_unchanged_tags
                 | match_reg_get REF sst cst
                 | match_reg_upd REF sst cst
                 | match_reg_unchanged REF sst cst
                 | match_pc_tag ]
  end.

Ltac user_data_unchanged_mem cmem1 cmem2 :=
  match goal with
  | GET : getm cmem1 ?addr = Some ?w@?ct,
    DEC : decode Symbolic.M cmem1 ?ct = Some (USER ?t),
    USERMEM : user_mem_unchanged cmem1 cmem2 |- _ =>
    match goal with
    | _ : getm cmem2 addr = Some _ |- _ => fail 1
    | |- _ => idtac
    end;
    first [ pose proof (proj1 (USERMEM _ _ _ _ DEC) GET)
          | failwith "user_data_unchanged_mem" ]
  end.

Ltac user_data_unchanged_regs cmem1 cmem2 :=
  match goal with
  | GET : getm ?regs1 ?r = Some ?w@?ct,
    DEC : decode Symbolic.R cmem1 ?ct = Some (USER ?t),
    USERREGS : user_regs_unchanged ?regs1 ?regs2 cmem1 |- _ =>
    match goal with
    | _ : getm regs2 r = Some _ |- _ => fail 1
    | |- _ => idtac
    end;
    first [ pose proof (proj1 (USERREGS _ _ _ _ DEC) GET)
          | failwith "user_data_unchanged_regs" ]
  end.

Ltac user_data_unchanged :=
  match goal with
  | Htags : user_tags_unchanged ?cmem1 ?cmem2 |- _ =>
    repeat first [ user_data_unchanged_mem cmem1 cmem2
                 | user_data_unchanged_regs cmem1 cmem2 ]
  end.

Lemma no_syscall_no_entry_point mem addr t :
  wf_entry_points table mem ->
  Symbolic.get_syscall table addr = None ->
  ~~ match getm mem addr with
     | Some i@it => (is_nop i) && (decode Symbolic.M mem it == Some (ENTRY t))
     | None => false
     end.
Proof.
  intros WF GETSC.
  apply/negP=> E.
  move: (proj2 (WF addr t) E) => [? ? ?].
  congruence.
Qed.

Ltac find_and_rewrite :=
  repeat match goal with
  | H : ?x = _ |- context[?x] =>
    rewrite H /=
  end.

Ltac solve_concrete_step :=
  match goal with
  | LOOKUP : Concrete.cache_lookup _ _ _ = _ |- _ =>
    repeat ([> once (
    econstructor; solve [eauto;
                         try solve [ eapply Concrete.state_eta
                                   | user_data_unchanged ];
                         repeat autounfold; simpl;
                         simpl in LOOKUP; rewrite LOOKUP;
                         match goal with
                         | STORE : Concrete.store_mvec _ _ = Some _ |- _ =>
                           rewrite STORE
                         | |- _ => idtac
                         end;
                         simpl in *;
                         find_and_rewrite; match_inv; eauto])
     | .. ])
  end.

Ltac solve_refine_state :=
  match goal with
  | REF : refine_state _ _ _ _ |- _ =>
    destruct REF; constructor; simpl in *;
    eauto using user_mem_unchanged_refine_memory,
                refine_registers_upd', user_regs_unchanged_refine_registers,
                mvec_in_kernel_user_upd, wf_entry_points_user_upd,
                no_syscall_no_entry_point
  end.

Ltac analyze_cache_miss :=
  match goal with
  | PC : getm ?cmem ?pc = Some ?i@_,
    INST : decode_instr ?i = Some _,
    MVEC : mvec_in_kernel ?cmem,
    KINV : kernel_invariant_statement _ ?cmem _ ?cache _,
    CACHE : cache_correct ?cache,
    LOOKUP : Concrete.cache_lookup ?cache _ _ = None,
    HANDLER : Symbolic.transfer ?mvec = Some _ |- _ =>
    let STORE := fresh "STORE" in
    pose proof (store_mvec_mvec_in_kernel cmem mvec);
    pose proof (kernel_invariant_store_mvec ki _ _ _ _ KINV);
    destruct (handler_correct_allowed_case_fwd _ _ _ pc@(Concrete.ctpc _) _ KINV _ STORE)
      as ([? ? ? [? ?] ?] &
          KEXEC & CACHE' & LOOKUP' & MVEC' & USERMEM & USERREGS & PC' & WFENTRYPOINTS' & KINV'');
    simpl in PC'; inv PC';
    match_data
  end.

Lemma build_cmvec_preserve cst cst' cmvec ivec :
  Concrete.pc cst = Concrete.pc cst' ->
  user_tags_unchanged (Concrete.mem cst) (Concrete.mem cst') ->
  user_mem_unchanged (Concrete.mem cst) (Concrete.mem cst') ->
  user_regs_unchanged (Concrete.regs cst) (Concrete.regs cst')
                      (Concrete.mem cst) ->
  wf_entry_points table (Concrete.mem cst) ->
  wf_entry_points table (Concrete.mem cst') ->
  build_cmvec cst = Some cmvec ->
  decode_ivec e (Concrete.mem cst) cmvec = Some ivec ->
  build_cmvec cst' = Some cmvec.
Proof.
  move=> Hpc Htags Hmem Hregs Hentry Hentry' Hbuild
         /decode_ivec_inv [Hdec | Hdec]; last first.
    case: Hdec => Hop _ Hdec_pc Hdec_ti.
    have Hctpc := build_cmvec_ctpc Hbuild.
    have [i [instr [Hget_i Hdec_i Hop']]] := build_cmvec_cop_cti Hbuild.
    have Hinstr : instr = Nop _.
      rewrite -{}Hop' in Hop.
      by case: instr Hdec_i Hop.
    rewrite {}Hinstr {instr} in Hdec_i Hop'.
    have [sc Hget_sc Hsc_t] :=
      wf_entry_points_only_if Hentry Hget_i Hdec_ti (proj2 (is_nopP _) Hdec_i).
    move/(Hmem _ _ _ _ Hdec_ti): (Hget_i) => Hget_i'.
    move: Hbuild.
    by rewrite /build_cmvec /Concrete.pcv -Hpc Hget_i Hget_i' Hdec_i /Concrete.pct Hpc.
  case: cmvec Hbuild ivec Hdec
        => [cop ctpc cti ct1 ct2 ct3] /= Hbuild
           [op' tpc ti ts] /= [Hop Hpriv Hdec_tpc Hdec_ti Hdec_ts].
  move: ts Hdec_ts. rewrite {}Hop {op'} => ts Hdec_ts.
  have [i [instr [//= Hget_i Hdec_i Hop']]] := build_cmvec_cop_cti Hbuild.
  subst cop.
  move: Hbuild ts Hdec_ts.
  move/(Hmem _ _ _ _ Hdec_ti): (Hget_i) => Hget_i'.
  rewrite /build_cmvec /Concrete.pcv /Concrete.pct -Hpc Hget_i Hget_i' /= {}Hdec_i.
  destruct instr; simpl; move => Hbuild ts Hdec_ts;
  match_inv; trivial;
  repeat match goal with
  | a : atom _ _ |- _ => destruct a
  | H : Some _ = Some _ |- _ => inv H
  end;
  simpl in *;
  user_data_unchanged; try match_mem_unchanged_tags; find_and_rewrite; trivial.
  done.
Qed.

Lemma refine_ivec sst cst ivec :
  refine_state ki table sst cst ->
  build_ivec table sst = Some ivec ->
  exists2 cmvec,
    build_cmvec cst = Some cmvec &
    decode_ivec e (Concrete.mem cst) cmvec = Some ivec.
Proof.
  move=> Href Hbuild.
  suff : match @build_cmvec _ ops cst return Prop with
         | Some cmvec => decode_ivec e (Concrete.mem cst) cmvec = Some ivec
         | None => False
         end by case: (build_cmvec cst); eauto.
  move: Hbuild.
  rewrite /build_ivec /build_cmvec /decode_ivec (rs_pc Href).
  case Hget: (getm _ _) => [[i ti]|] //=; last first.
    case Hget_sc: (Symbolic.get_syscall _ _) => [sc|] //= [<-] {ivec}.
    have [i' [cti [Hget' Hdec_cti /is_nopP Hi]]] :=
      wf_entry_points_if (rs_entry_points Href) Hget_sc.
    rewrite Hget' Hi /=.
    by rewrite /decode_ivec /= (rs_pct Href) Hdec_cti.
  have [cti Hdec_cti Hget'] := proj2 (rs_refm Href) _ _ _ Hget.
  rewrite Hget' /=.
  case Hdec_i: (decode_instr i) => [instr|] //=.
  rewrite /decode_fields.
  destruct instr; move=> Hivec;
  match_inv;
  repeat match goal with
  | x : atom _ _ |- _ => destruct x
  end;
  match_data; find_and_rewrite; rewrite ?mword_of_opK /= ?(rs_pct Href) //;
  find_and_rewrite; done.
Qed.

Lemma forward_simulation_miss sst cst ivec ovec cmvec :
  refine_state ki table sst cst ->
  build_ivec table sst = Some ivec ->
  build_cmvec cst = Some cmvec ->
  Symbolic.transfer ivec = Some ovec ->
  Concrete.cache_lookup (Concrete.cache cst) masks cmvec = None ->
  exists cst' crvec,
    [/\ exec (Concrete.step _ masks) cst cst',
        refine_state ki table sst cst',
        decode_ovec e _ (Concrete.mem cst') crvec = Some ovec,
        Concrete.cache_lookup (Concrete.cache cst') masks cmvec = Some crvec &
        build_cmvec cst' = Some cmvec ].
Proof.
  move=> REF IVEC CMVEC TRANS LOOKUP.
  have FAULT := lookup_none_step CMVEC LOOKUP.
  have [cmvec'] := refine_ivec REF IVEC.
  rewrite CMVEC. move => [<-] {cmvec'} DEC.
  have := handler_correct_allowed_case_fwd (Concrete.pc cst) (rs_kinv REF) DEC TRANS
                                           (rs_cache REF) => /(_ _ _ kcc).
  case=> cst' [crvec [EXEC [CACHE [LOOKUP' [DEC' [MVEC [USERPCTAG [USERMEM [USERREGS [PC [ENTRYPOINTS KINV]]]]]]]]]]].
  exists cst', crvec.
  split=> //.
    eapply re_step; trivial; try eassumption.
    eapply exec_until_weaken; eauto.
  constructor=> //.
  - by rewrite /Concrete.pcv PC (rs_pc REF).
  - apply USERPCTAG.
    rewrite /Concrete.pct PC.
    by apply (rs_pct REF).
  - by eauto using user_mem_unchanged_refine_memory, rs_refm.
  - by eauto using user_regs_unchanged_refine_registers, rs_refr.
  - eapply build_cmvec_preserve; try eassumption.
    + by rewrite PC.
    + by eauto using rs_entry_points.
Qed.

Lemma transfer_lookup sst cst ivec ovec cmvec crvec :
  refine_state ki table sst cst ->
  build_ivec table sst = Some ivec ->
  build_cmvec cst = Some cmvec ->
  Symbolic.transfer ivec = Some ovec ->
  Concrete.cache_lookup (Concrete.cache cst) masks cmvec = Some crvec ->
  decode_ovec e _ (Concrete.mem cst) crvec = Some ovec.
Proof.
  move=> REF IVEC CMVEC TRANS LOOKUP.
  have [cmvec'] := refine_ivec REF IVEC.
  rewrite CMVEC. move=> [<-] {cmvec'} DEC.
  have [ |ivec' [ovec' [DEC' DECo TRANS']]] := rs_cache REF LOOKUP _.
    by case/decode_ivec_inv: DEC => [[? ? ->]|[? ? ->]].
  move: DEC' ovec' DECo TRANS'.
  rewrite DEC. move=> [<-]. rewrite TRANS.
  by move=> ? -> [<-].
Qed.

Lemma forward_simulation_hit sst sst' cst ivec ovec cmvec crvec :
  refine_state ki table sst cst ->
  build_ivec table sst = Some ivec ->
  build_cmvec cst = Some cmvec ->
  Symbolic.transfer ivec = Some ovec ->
  Concrete.cache_lookup (Concrete.cache cst) masks cmvec = Some crvec ->
  Symbolic.step table sst sst' ->
  exists2 cst',
    exec (Concrete.step _ masks) cst cst' &
    refine_state ki table sst' cst'.
Proof.
  move=> REF IVEC CMVEC TRANS LOOKUP /stepP STEP.
  case GETi: (getm (Symbolic.mem sst) (Symbolic.pcv sst)) => [[i ti]|]; last first.
    move: STEP ivec ovec TRANS IVEC CMVEC.
    rewrite {1}(Symbolic.state_eta sst) /build_ivec /= GETi.
    case GETSC: (Symbolic.get_syscall _ _) => [sc|] //=.
    move=> RUN ivec ovec TRANS [E]. subst ivec.
    have [i [cti [GETi' DECti /is_nopP ISNOP]]] := wf_entry_points_if (rs_entry_points REF) GETSC.
    rewrite (rs_pc REF) in GETi'.
    rewrite /build_cmvec GETi' /= ISNOP /= (Symbolic.state_eta sst'). move => [E]. subst cmvec.
    rewrite (Symbolic.state_eta sst') in RUN.
    have := syscalls_correct_allowed_case_fwd (rs_kinv REF) (rs_refm REF)
                                              (rs_refr REF) (rs_cache REF)
                                              (rs_mvec REF) GETSC RUN (rs_pct REF)
            => /(_ _ kcc (Concrete.epc cst)) /=.
    rewrite /cache_allows_syscall /= GETSC
            /build_cmvec (rs_pc REF) GETi' ISNOP LOOKUP.
    case/(_ erefl) => cmem [creg [cache [ctpc [epc]]]].
    case=> [[kst INUSER STEP EXEC] [DEC [REFM [REFR [CACHE [MVEC [ENTRYPOINTS KINV]]]]]]].
    eexists.
      rewrite (Concrete.state_eta cst).
      eapply re_step; trivial; try eassumption.
      by eapply exec_until_weaken; eauto.
    by constructor=> //.
  suff : match @step masks _ ops cst return Prop with
         | Some cst' => @refine_state _ ops _ _ ki table sst' cst'
         | None => False
         end.
    case STEP': (step _ _) => [cst'|] //= REF'.
    move/concrete.exec.stepP in STEP'.
    by eauto.
  move: STEP.
  rewrite /stepf /step (Concrete.state_eta cst) (Symbolic.state_eta sst) /=.
  move: ivec ovec TRANS IVEC CMVEC (transfer_lookup REF IVEC CMVEC TRANS LOOKUP).
  rewrite /build_ivec /build_cmvec GETi.
  have [cti DECti GETi'] := proj2 (rs_refm REF) _ _ _ GETi.
  rewrite (rs_pc REF) in GETi'.
  rewrite GETi' /=.
  case: (decode_instr i) => [instr|] //=.
  repeat autounfold; simpl.
  rewrite /decode_ovec.
  destruct instr; move=> ivec ovec TRANS IVEC;
  match_inv;
  repeat match goal with
  | x : atom _ _ |- _ => destruct x
  end;
  match_data; find_and_rewrite; rewrite ?(rs_pct REF);
  move=> ? // DECo STEP; match_inv; match_data;
  rewrite ?LOOKUP; find_and_rewrite; try rewrite (rs_pc REF);
  try solve [solve_refine_state].

  (* Jal *)
  rewrite -(rs_pc REF) UPD' /=.
  by solve_refine_state.
Qed.

Lemma forward_simulation sst sst' cst :
  refine_state ki table sst cst ->
  Symbolic.step table sst sst' ->
  exists2 cst',
    exec (Concrete.step _ masks) cst cst' &
    refine_state ki table sst' cst'.
Proof.
  move=> Href Hstep.
  have [ivec [ovec [Hbuildi Htrans]]] := step_build_ivec Hstep.
  have [cmvec Hbuildc Hdeci] := refine_ivec Href Hbuildi.
  case Hlookup : (Concrete.cache_lookup (Concrete.cache cst) masks cmvec) => [crvec|].
    by eauto using forward_simulation_hit.
  have [cst' [crvec [Hexec Href' Hdeco Hlookup' Hbuildc']]] :=
    forward_simulation_miss Href Hbuildi Hbuildc Htrans Hlookup.
  have [cst'' Hexec' Href''] :=
    forward_simulation_hit Href' Hbuildi Hbuildc' Htrans Hlookup' Hstep.
  exists cst''=> //.
  by eauto.
Qed.

End Refinement.
