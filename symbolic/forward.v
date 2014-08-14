Require Import List NPeano Arith Bool.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Require Import lib.Integers lib.utils lib.partial_maps lib.Coqlib.
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

Hint Unfold Concrete.next_state_reg.
Hint Unfold Concrete.next_state_reg_and_pc.
Hint Unfold Concrete.next_state_pc.
Hint Unfold Concrete.next_state.
Hint Unfold Concrete.miss_state.

Let in_kernel_user k t : Concrete.is_kernel_tag (@encode _ _ (e k) (USER t)) = false.
Proof.
  unfold Concrete.is_kernel_tag.
  erewrite encode_kernel_tag.
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
  | H : PartMaps.get ?amem ?addr = Some ?w,
    REFM : refine_memory ?amem ?cmem |- _ =>
    match goal with
    | _ : PartMaps.get cmem addr = _ |- _ => fail 1
    | |- _ => idtac
    end;
    apply REFM in H

  | GET : PartMaps.get ?mem1 ?addr = Some ?x@(encode (USER ?t)),
    USERMEM : user_mem_unchanged ?mem1 ?mem2 |- _ =>
    match goal with
    | _ : PartMaps.get mem2 addr = _ |- _ => fail 1
    | |- _ => idtac
    end;
    assert (PartMaps.get mem2 addr = Some x@(encode (USER t)));
    try solve [eapply USERMEM; assumption]

  | H : PartMaps.upd ?amem ?addr _ = Some ?amem',
    REFM : refine_memory ?amem ?cmem |- _ =>
    match goal with
    | _ : refine_memory amem' ?cmem',
      _ : PartMaps.upd cmem ?addr _ = Some ?cmem'|- _ => fail 1
    | |- _ => idtac
    end;
    let cmem' := fresh "cmem'" in
    let UPD' := fresh "UPD'" in
    let REFM' := fresh "REFM'" in
    destruct (refine_memory_upd' _ _ _ REFM H) as (cmem' & UPD' & REFM')

  | H : PartMaps.get ?aregs ?r = Some _,
    REFR : refine_registers ?aregs ?cregs |- _ =>
    apply REFR in H

  | UPD : PartMaps.upd ?aregs ?r _ = Some ?aregs',
    REFR : refine_registers ?aregs ?cregs |- _ =>
    match goal with
    | _ : refine_registers aregs' ?cregs',
      _ : PartMaps.upd cregs r _ = Some ?cregs'|- _ => fail 1
    | |- _ => idtac
    end;
    let cregs' := fresh "cregs'" in
    let UPD' := fresh "UPD'" in
    let REFR' := fresh "REFR'" in
    destruct (refine_registers_upd' _ _ _ REFR UPD) as (cregs' & UPD' & REFR')

  | REFM : refine_memory ?smem ?cmem,
    USERMEM : user_mem_unchanged ?cmem ?cmem' |- _ =>
    match goal with
    | _ : refine_memory smem cmem' |- _ => fail 1
    | |- _ => idtac
    end;
    pose proof (user_mem_unchanged_refine_memory REFM USERMEM)

  | REFR : refine_registers ?sregs ?cregs,
    USERREGS : user_regs_unchanged ?cregs ?cregs' |- _ =>
    match goal with
    | _ : refine_registers sregs cregs' |- _ => fail 1
    | |- _ => idtac
    end;
    pose proof (user_regs_unchanged_refine_registers REFR USERREGS)

  end.

Ltac user_data_unchanged :=
  match goal with
  | GET : PartMaps.get ?mem1 ?addr = Some _,
    USERMEM : user_mem_unchanged ?mem1 ?mem2
    |- PartMaps.get ?mem2 ?addr = Some _ =>
    simpl in GET, USERMEM;
    rewrite <- (USERMEM addr); eassumption

  | GET : PartMaps.get ?regs1 ?r = _,
    USERREGS : user_regs_unchanged ?regs1 ?regs2
    |- PartMaps.get ?regs2 ?r = _ =>
    simpl in GET, USERREGS;
    rewrite <- (USERREGS r); eauto
  end.

Lemma no_syscall_no_entry_point mem addr t :
  wf_entry_points table mem ->
  Symbolic.get_syscall table addr = None ->
  ~~ match PartMaps.get mem addr with
     | Some i@it => (is_nop i) && (it == @encode _ _ (e Symbolic.M) (ENTRY t))
     | None => false
     end.
Proof.
  intros WF GETSC.
  destruct (match PartMaps.get mem addr with
            | Some i@it => (is_nop i) && (it == @encode _ _ (e Symbolic.M) (ENTRY t))
            | None => false
            end) eqn:E; trivial.
  apply WF in E.
  destruct E as [? [? ?]]. congruence.
Qed.

Ltac solve_concrete_step :=
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
                         repeat match goal with
                         | H : ?X = _ |- context[?X] =>
                           rewrite H; simpl
                         end; match_inv; eauto])
  end.

Ltac destruct_mvec_operands :=
  repeat match goal with
  | ts : Vector.t _ 0 |- _ => induction ts using Vector.case0
  | ts : Vector.t _ (S _) |- _ => induction ts using caseS
  | ts : Empty_set |- _ => destruct ts
  end.

Lemma symbolic_handler_concrete_cache cache umvec urvec rvec :
  cache_correct cache ->
  Symbolic.transfer umvec = Some urvec ->
  Concrete.cache_lookup cache masks (encode_ivec _ (ivec_of_uivec umvec)) = Some rvec ->
  rvec = encode_ovec _ (ovec_of_uovec urvec).
Proof.
  intros CACHE HANDLER LOOKUP.
  assert (INUSER : @word_lift _ _ (e Symbolic.P) (fun t => is_user t)
                             (Concrete.ctpc (encode_ivec _ (ivec_of_uivec umvec))) = true).
  { destruct umvec as [op tpc ti ts].
    simpl.
    unfold word_lift.
    rewrite decodeK.
    by destruct op. }
  move: (CACHE _ _ INUSER LOOKUP) => [ivec' [ovec' [E1 [E2 [E3 E4]]]]]. subst.
  apply encode_ivec_inj in E1.
  apply ivec_of_uivec_inj in E1. subst.
  congruence.
Qed.

Lemma symbolic_handler_concrete_handler mvec rvec :
  Symbolic.transfer mvec = Some rvec ->
  ~~ privileged_op (Symbolic.op mvec) ->
  handler _ [eta Symbolic.transfer] (encode_ivec e (ivec_of_uivec mvec))
  = Some (encode_ovec _ (ovec_of_uovec rvec)).
Proof.
  move: mvec rvec => [op tpc ti ts] rvec H PRIV.
  by rewrite /handler decode_ivecK (lock ivec_of_uivec) /=
             -(lock ivec_of_uivec) ivec_of_uivec_privileged
             (negbTE PRIV) ivec_of_uivecK /= H /=.
Qed.

Ltac solve_refine_state :=
  unfold in_user, word_lift in *; simpl in *;
  repeat rewrite decodeK; simpl in *;
  try match goal with
  | USERREGS : user_regs_unchanged ?cregs _,
    H : PartMaps.get ?cregs ?r = _ |- _ =>
    simpl in USERREGS; rewrite -> (USERREGS r) in H
  end;
  econstructor;
  eauto using user_mem_unchanged_refine_memory,
              refine_registers_upd', user_regs_unchanged_refine_registers,
              mvec_in_kernel_user_upd, wf_entry_points_user_upd,
              no_syscall_no_entry_point.

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
    LOOKUP : Concrete.cache_lookup ?cache _ (encode_ivec _ (ivec_of_uivec ?mvec)) = None,
    HANDLER : Symbolic.transfer ?mvec = Some _ |- _ =>
    let cmvec := constr:(encode_ivec _ (ivec_of_uivec mvec)) in
    let STORE := fresh "STORE" in
    destruct (mvec_in_kernel_store_mvec cmvec MVEC) as [? STORE];
    pose proof (store_mvec_mvec_in_kernel _ _ STORE);
    pose proof (kernel_invariant_store_mvec ki _ _ _ _ _ KINV STORE);
    let HANDLER' := constr:(@symbolic_handler_concrete_handler mvec _ HANDLER erefl) in
    destruct (handler_correct_allowed_case _ cmvec _ pc@(Concrete.ctpc cmvec) _ KINV HANDLER' STORE CACHE)
      as ([? ? ? [? ?] ?] &
          KEXEC & CACHE' & LOOKUP' & MVEC' & USERMEM & USERREGS & PC' & WFENTRYPOINTS' & KINV'');
    simpl in PC'; inv PC';
    match_data;
    unfold encode_ivec, encode_ovec, ovec_of_uovec in *; simpl in *
  end.

Ltac analyze_step :=
  match goal with
  | rvec : _,
    CACHE : cache_correct ?cache,
    HANDLER : Symbolic.transfer ?mvec = Some ?rvec |- _ =>
    let trpc := fresh "trpc" in
    let tr   := fresh "tr"   in
    destruct rvec as [trpc tr]; simpl in tr;
    let cmvec := constr:(encode_ivec e (ivec_of_uivec mvec)) in
    destruct (Concrete.cache_lookup cache masks cmvec) as [rvec' | ] eqn:LOOKUP;

    [
      (* Cache hit case *)
      generalize (@symbolic_handler_concrete_cache _ mvec _ _  CACHE HANDLER LOOKUP);
      intros; subst rvec';
      unfold encode_ivec, encode_ovec, ovec_of_uovec in LOOKUP; simpl in *;
      match_data;
      solve [eexists; split;
                 [apply exec_one; solve_concrete_step|solve_refine_state]]

          || let op := current_instr_opcode in fail 3 "failed hit case" op
    |
      (* Cache miss case, fault handler will execute *)
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
      || let op := current_instr_opcode in fail 3 "failed miss case" op
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
  intros REF STEP.
  destruct REF as [smem sregs int cmem cregs cache epc pc tpc
                   ? ? REFM REFR CACHE MVEC WFENTRYPOINTS KINV].
  subst sst cst.
  inv STEP;
  try match goal with
  | H : Symbolic.State _ _ _ _ = Symbolic.State _ _ _ _ |- _ =>
    inv H
  end;
  match_data;
  repeat autounfold in NEXT;
  match_inv;

  analyze_step.

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
