Require Import List NPeano Arith Bool.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Require Import lib.Integers lib.utils lib.partial_maps lib.Coqlib.
Require Import common.common.
Require Import concrete.concrete.
Require Import concrete.exec.
Require Import symbolic.symbolic.
Require Import symbolic.exec.
Require Import symbolic.rules.
Require Import symbolic.refinement_common.

Open Scope nat_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import ListNotations.

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
        {table : list (Symbolic.syscall mt)}
        {kcc : kernel_code_correctness ki table}.

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
  user_mem_unchanged cmem cmem' ->
  refine_memory amem cmem'.
Proof.
  move=> [REF1 REF2] USERMEM.
  split.
  - move=> w x ctg atg DEC GET.
    move: (USERMEM w x ctg atg) (conj GET DEC) => H /H {H} {GET DEC} [GET DEC].
    by eauto.
  - move=> w x atg /REF2 [ctg DEC GET].
    move: (USERMEM w x ctg atg) (conj GET DEC) => H /H {H} {GET DEC} [GET DEC].
    by eauto.
Qed.

Lemma user_regs_unchanged_refine_registers areg creg creg' cmem cmem' :
  refine_registers areg creg cmem ->
  user_regs_unchanged creg creg' cmem cmem' ->
  refine_registers areg creg' cmem'.
Proof.
  move=> [REF1 REF2] USERREGS.
  split.
  - move=> r x ctg atg DEC GET.
    move: (USERREGS r x ctg atg) (conj GET DEC) => H /H {USERREGS H GET DEC} [GET DEC].
    by eauto.
  - move=> r x atg /REF2 [ctg DEC GET].
    move: (USERREGS r x ctg atg) (conj GET DEC) => H /H {USERREGS H GET DEC} [GET DEC].
    by eauto.
Qed.

Ltac failwith message :=
  let op := current_instr_opcode in
  fail 1000 message op.

Ltac check_conv t1 t2 :=
  let e := constr:(erefl t1 : t1 = t2) in idtac.

Ltac match_mem_get REF sst cst :=
  match goal with
  | GET : PartMaps.get ?smem ?addr = Some ?w@?t |- _ =>
    check_conv smem (Symbolic.mem sst);
    match goal with
    | _ : PartMaps.get ?cmem addr = _ |- _ => check_conv cmem (Concrete.mem cst); fail 1
    | |- _ => idtac
    end;
    first [ have [? ? ?] := proj2 (rs_refm REF) _ _ _ GET
          | failwith "match_mem" ]
  end.

Ltac match_mem_upd REF sst cst :=
  match goal with
  | UPD : PartMaps.upd ?smem ?addr ?w@?t = Some ?smem',
    DEC : decode Symbolic.M ?cmem ?ct = Some (USER ?t) |- _ =>
    check_conv smem (Symbolic.mem sst);
    match goal with
    | _ : refine_memory smem' ?cmem',
      _ : PartMaps.upd cmem ?addr _ = Some ?cmem' |- _ => fail 1
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
  | GET : PartMaps.get ?mem1 ?addr = Some ?x@?ct,
    DEC : decode Symbolic.M ?mem1 ?ct = Some (USER ?t),
    USERMEM : user_mem_unchanged ?mem1 ?mem2 |- _ =>
    match goal with
    | _ : PartMaps.get mem2 addr = _ |- _ => fail 1
    | |- _ => idtac
    end;
    first [ have [? ?] : (PartMaps.get mem2 addr = Some x@ct /\
                          decode Symbolic.M mem2 ct = Some (USER t))
                          by apply/USERMEM; eauto
          | failwith "match_mem_unchanged_tags" ]
  end.

Ltac match_reg_get REF sst cst :=
  match goal with
  | GET : PartMaps.get ?sregs ?r = Some ?w@?t |- _ =>
    check_conv sregs (Symbolic.regs sst);
    match goal with
    | _ : PartMaps.get ?cregs r = Some _ |- _ => check_conv cregs (Concrete.regs cst); fail 1
    | |- _ => idtac
    end;
    first [ destruct (proj2 (rs_refr REF) _ _ _ GET) as [? ? ?]
          | failwith "match_reg_get" ]
  end.

Ltac match_reg_upd REF sst cst :=
  match goal with
  | UPD : PartMaps.upd ?sregs ?r ?w@?t = Some ?sregs',
    DEC : decode Symbolic.R ?cmem ?ct = Some (USER ?t) |- _ =>
    check_conv sregs (Symbolic.regs sst);
    match goal with
    | _ : refine_registers sregs' ?cregs' cmem,
      _ : PartMaps.upd _ r _ = Some ?cregs' |- _ => fail 1
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
          | failwith "match_data 7" ]

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
                 | match_reg_unchanged REF sst cst ]
  end.

Ltac user_data_unchanged :=
  match goal with
  | GET : PartMaps.get ?mem1 ?addr = Some ?w@?ct,
    DEC : decode Symbolic.M ?mem1 ?ct = Some (USER ?t),
    USERMEM : user_mem_unchanged ?mem1 ?mem2 |- _ =>
    match goal with
    | _ : PartMaps.get mem2 addr = Some _ |- _ => fail 1
    | |- _ => idtac
    end;
    first [ destruct (proj1 (USERMEM _ _ _ _) (conj GET DEC)) as [? ?]
          | failwith "user_data_unchanged 1" ]

  | GET : PartMaps.get ?regs1 ?r = Some ?w@?ct,
    DEC : decode Symbolic.R ?cmem1 ?ct = Some (USER ?t),
    USERREGS : user_regs_unchanged ?regs1 ?regs2 ?cmem1 ?cmem2 |- _ =>
    match goal with
    | _ : PartMaps.get regs2 r = Some _ |- _ => fail 1
    | |- _ => idtac
    end;
    first [ destruct (proj1 (USERREGS _ _ _ _) (conj GET DEC)) as [? ?]
          | failwith "user_data_unchanged 2" ]
  end.

Lemma no_syscall_no_entry_point mem addr t :
  wf_entry_points table mem ->
  Symbolic.get_syscall table addr = None ->
  ~~ match PartMaps.get mem addr with
     | Some i@it => (is_nop i) && (decode Symbolic.M mem it == Some (ENTRY t))
     | None => false
     end.
Proof.
  intros WF GETSC.
  apply/negP=> E.
  move: (proj2 (WF addr t) E) => [? [? ?]].
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
    econstructor (solve [eauto;
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

Ltac analyze_syscall :=
  match goal with
  | H : Symbolic.run_syscall _ _ = Some ?sst' |- _ =>
    destruct sst' as [smem' sregs' [spc' sapc'] int'];
    exploit syscalls_correct_allowed_case; eauto;
    intros;
    repeat match goal with
    | H : exists _, _ |- _ => destruct H
    | H : _ /\ _ |- _ => destruct H
    end;
    eexists; split;
    [apply user_kernel_user_step_weaken; eassumption|solve_refine_state]
  end.

Ltac analyze_cache_miss :=
  match goal with
  | PC : PartMaps.get ?cmem ?pc = Some ?i@_,
    INST : decode_instr ?i = Some _,
    MVEC : mvec_in_kernel ?cmem,
    KINV : kernel_invariant_statement _ ?cmem _ ?cache _,
    CACHE : cache_correct ?cache,
    LOOKUP : Concrete.cache_lookup ?cache _ _ = None,
    HANDLER : Symbolic.transfer ?mvec = Some _ |- _ =>
    let STORE := fresh "STORE" in
    destruct (mvec_in_kernel_store_mvec _ MVEC) as [? STORE];
    pose proof (store_mvec_mvec_in_kernel _ _ STORE);
    pose proof (kernel_invariant_store_mvec ki _ _ _ _ _ KINV STORE);
    destruct (handler_correct_allowed_case _ _ _ pc@(Concrete.ctpc _) _ KINV _ STORE CACHE)
      as ([? ? ? [? ?] ?] &
          KEXEC & CACHE' & LOOKUP' & MVEC' & USERMEM & USERREGS & PC' & WFENTRYPOINTS' & KINV'');
    simpl in PC'; inv PC';
    match_data
  end.

Lemma forward_simulation_miss sst cst ivec ovec cmvec :
  refine_state ki table sst cst ->
  build_ivec table sst = Some ivec ->
  build_cmvec cst = Some cmvec ->
  Symbolic.transfer ivec = Some ovec ->
  Concrete.cache_lookup (Concrete.cache cst) masks cmvec = None ->
  exists cst' crvec,
    [/\ exec (Concrete.step _ masks) cst cst',
        refine_state ki table sst cst',
        decode_ovec e _ (Concrete.mem cst') crvec = Some ovec &
        Concrete.cache_lookup (Concrete.cache cst') masks cmvec = Some crvec ].
Proof.
  move=> REF IVEC CMVEC TRANS LOOKUP.
  have [cmem Hcmem] := mvec_in_kernel_store_mvec cmvec (rs_mvec REF).
  have FAULT := lookup_none_step CMVEC LOOKUP Hcmem.
  have [cmvec'] := refine_ivec REF IVEC.
  rewrite CMVEC. move => [<-] {cmvec'} DEC.
  have := handler_correct_allowed_case (Concrete.pc cst) (rs_kinv REF) DEC TRANS Hcmem
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
  have [ |ivec' [ovec' [DEC' DECo TRANS' _]]] := rs_cache REF LOOKUP _.
    by case/decode_ivec_inv: DEC => [[op [? ? ->]]|[? ? ->]].
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
  case GETi: (PartMaps.get (Symbolic.mem sst) (Symbolic.pcv sst)) => [[i ti]|]; last first.
    move: STEP ivec ovec TRANS IVEC CMVEC.
    rewrite {1}(Symbolic.state_eta sst) /build_ivec /= GETi.
    case GETSC: (Symbolic.get_syscall _ _) => [sc|] //=.
    move=> RUN ivec ovec TRANS [E]. subst ivec.
    have [i [cti [GETi' DECti /is_nopP ISNOP]]] := wf_entry_points_if (rs_entry_points REF) GETSC.
    rewrite (rs_pc REF) in GETi'.
    rewrite /build_cmvec GETi' /= ISNOP /= (Symbolic.state_eta sst'). move => [E]. subst cmvec.
    rewrite (Symbolic.state_eta sst') in RUN.
    have := syscalls_correct_allowed_case (rs_kinv REF) (rs_refm REF)
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
  suff : match @step masks _ ops cst with
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
  move=> ? // DECo STEP; match_inv; match_data; rewrite ?LOOKUP; find_and_rewrite;
  try solve [rewrite (rs_pc REF); solve_refine_state].


  move=>

  match_data.

Ltac concretize_ivec ivec :=
  match goal with
  | REF : refine_state _ _ ?sst ?cst |- _ =>
    first [
        let ivec := eval hnf in ivec in
        let mvec := match ivec with
                    | Symbolic.mkIVec ?op ?tpc ?ti ?ts =>
                      let op := match op with
                                | OP ?op => op
                                end in
                      let cti := match goal with
                                 | _ : decode Symbolic.M _ ?cti = Some (USER ti) |- _ => cti
                                 end in
                      let ct1 := match ts with
                                 | (?t1, _) =>
                                   match goal with
                                   | _ : decode _ _ ?ct1 = Some (USER t1) |- _ => ct1
                                   end
                                 | _ => constr:(@Concrete.TNone mt)
                                 end in
                      let ct2 := match ts with
                                 | (_, (?t2, _)) =>
                                   match goal with
                                   | _ : decode _ _ ?ct2 = Some (USER t2) |- _ => ct2
                                   end
                                 | _ => constr:(@Concrete.TNone mt)
                                 end in
                      let ct3 := match ts with
                                 | (_, (_, (?t3, _))) =>
                                   match goal with
                                   | _ : decode _ _ ?ct3 = Some (USER t3) |- _ => ct3
                                   end
                                 | _ => constr:(@Concrete.TNone mt)
                                 end in
                      constr:(Concrete.mkMVec (op_to_word op) (common.tag (Concrete.pc cst)) cti ct1 ct2 ct3)
                    end in
        assert (build_cmvec cst = Some mvec) by (rewrite /build_cmvec; find_and_rewrite; reflexivity);
        assert (build_ivec table sst = Some ivec) by (rewrite /build_ivec; find_and_rewrite; reflexivity)
      | failwith "concretize_ivec" ]
  end.

Ltac solve_hit_case REF sst cst TRANS LOOKUP :=
  match goal with
  | IVEC : build_ivec _ sst = Some ?ivec,
    CMVEC : build_cmvec cst = Some ?cmvec |- _ =>
    first [ let DECo := fresh "DECo" in
            have /= DECo := transfer_lookup REF IVEC CMVEC TRANS LOOKUP;
            match_inv; match_data;
            eexists; split; [ eapply exec_one; solve_concrete_step | solve_refine_state ]
          | failwith "solve_hit_case" ]
  end.

Ltac analyze_step :=
  match goal with
  | REF : refine_state _ _ ?sst ?cst,
    TRANS : Symbolic.transfer ?ivec = Some ?ovec |- _ =>
    let trpc := fresh "trpc" in
    let tr   := fresh "tr"   in
    let ctrpc := fresh "ctrpc" in
    let ctr := fresh "ctr" in
    let rvec := fresh "rvec" in
    try simpl in ovec;
    destruct ovec as [trpc tr]; simpl in tr;
    concretize_ivec ivec;
    let cmvec := match goal with
                 | _ : build_cmvec _ = Some ?cmvec |- _ => cmvec
                 end in
    destruct (Concrete.cache_lookup (Concrete.cache cst) masks cmvec) as [[ctrpc ctr] | ] eqn:LOOKUP;

    [
      (* Cache hit case *)

      solve_hit_case REF sst cst TRANS LOOKUP

    |
      (* Cache miss case, fault handler will execute *)
      idtac (*
      analyze_cache_miss;
      solve [eexists; split;
      [
        eapply re_step; trivial; [solve_concrete_step|];
        try (
          eapply restricted_exec_trans;
          try solve [eapply exec_until_weaken; eassumption];
          try solve [eapply exec_one; solve_concrete_step]
        )
      | solve_refine_state ] ]
      || let op := current_instr_opcode in fail 3 "failed miss case" op *)
    ]
  | _ : Symbolic.run_syscall _ _ = Some _ |- _ => idtac
  end.

Lemma forward_simulation sst sst' cst :
  refine_state ki table sst cst ->
  Symbolic.step table sst sst' ->
  exists cst',
    exec (Concrete.step _ masks) cst cst' /\
    refine_state ki table sst' cst'.
Proof.
  move=> REF STEP.
  inv STEP;
  have := rs_pc REF; rewrite /Symbolic.pcv /= => ?; try subst pc'; try subst;
  match_data;
  repeat autounfold in NEXT;
  match_inv;

  analyze_step.

  analyze_cache_miss.
  eexists. split.
  apply exec_one. solve_concrete_step.
  solve_refine_state.
  destruct REF.
  constructor; simpl; eauto.
  eauto using rs_refm.


  eapply Concrete.step_nop; eauto. eapply concrete_state_eta.
  repeat autounfold. simpl. rewrite LOOKUP. reflexivity.

  match goal with
  | LOOKUP : Concrete.cache_lookup _ _ _ = _ |- _ =>
    econstructor (solve [eauto; try solve [user_data_unchanged];
                         repeat autounfold; simpl;
                         simpl in LOOKUP; rewrite LOOKUP;
                         match goal with
                         | STORE : Concrete.store_mvec _ _ = Some _ |- _ =>
                           rewrite STORE
                         | |- _ => idtac
                         end;
                         simpl in *;
                         find_and_rewrite; match_inv; eauto])
  end.


 solve_concrete_step.

  match_data.

  simpl.

  subst

  eexists. split.
  apply exec_one. solve_concrete_step.

  econstructor; eauto; simpl.

  assert (build_ivec table (Symbolic.State mem reg pc0@tpc0 extra) = Some mvec).
  by rewrite /build_ivec; find_and_rewrite.
  match goal with
  | H : Concrete.cache_lookup _ _ ?cmvec = _ |- _ =>
    assert (build_cmvec (Concrete.mkState cmem cregs cache pc0@tpc epc) = Some cmvec)
  end.
  by rewrite /build_cmvec; find_and_rewrite.



  simpl.


  let cmvec := concretize_ivec in
  set (A := cmvec).

  Focus 2.

  match goal with
    | |- context[exec _ ?cst _] =>
      case: (boolP (cache_allows_syscall table cst)) => [ALLOWED | NOTALLOWED]
  end.
  + by analyze_syscall.
  + move: (wf_entry_points_if _ WFENTRYPOINTS GETCALL) => [i [GETPC ISNOP]].
    rewrite /is_nop in ISNOP.
    case DEC: (decode_instr i) ISNOP => [[] |] // _.
    move: (CALL) => CALL'. rewrite /Symbolic.run_syscall /= in CALL'.
    rewrite /cache_allows_syscall GETCALL /= in NOTALLOWED.
    match type of NOTALLOWED with
    | context[Concrete.cache_lookup _ _ ?x] =>
      set (cmvec := x);
      destruct (Concrete.cache_lookup _ masks x) eqn:LOOKUP; first by []
    end.
    move {NOTALLOWED}.
    match type of CALL' with
    | context[Symbolic.transfer ?mvec] =>
      destruct (Symbolic.transfer mvec) eqn:HANDLER; last by []
    end.
    assert (HANDLER' : handler e Symbolic.transfer cmvec = Some (Concrete.mkRVec Concrete.TKernel Concrete.TKernel)).
    { rewrite /handler /=.
      match goal with
      | H : Symbolic.transfer ?mvec = _ |- _ =>
      change cmvec with (encode_ivec e (ivec_of_uivec mvec)) end.
      by rewrite decode_ivecK /= HANDLER /= /ovec_of_uovec /encode_ovec. }
    destruct (mvec_in_kernel_store_mvec cmvec MVEC) as [? STORE].
    pose proof (store_mvec_mvec_in_kernel _ _ STORE).
    pose proof (kernel_invariant_store_mvec ki _ _ _ _ _ KINV STORE).
    destruct (handler_correct_allowed_case _ cmvec _ pc0@(Concrete.ctpc cmvec) _ KINV HANDLER' STORE CACHE)
      as ([? ? ? [? ?] ?] &
          KEXEC & CACHE' & LOOKUP' & MVEC' & USERMEM & USERREGS & PC' & WFENTRYPOINTS' & KINV'').
    simpl in PC'. inv PC'.
    match_data.
    destruct sst' as [amem' aregs' [apc' tapc'] int'].
    match type of KEXEC with
    | kernel_user_exec _ ?cst' =>
      have ALLOWED : cache_allows_syscall table cst'
        by rewrite /cache_allows_syscall /= GETCALL LOOKUP'
    end.
    exploit syscalls_correct_allowed_case; eauto. simpl.
    intros HH.
    repeat match goal with
    | H : exists _, _ |- _ => destruct H
    | H : _ /\ _ |- _ => destruct H
    end.
    eexists. split.
    eapply re_step; trivial.
    { solve_concrete_step. }
    eapply restricted_exec_trans. eapply exec_until_weaken. eassumption.
    eapply user_kernel_user_step_weaken. eassumption.
    solve_refine_state.
Qed.

End Refinement.
