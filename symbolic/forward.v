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

Hint Unfold Concrete.next_state_reg.
Hint Unfold Concrete.next_state_reg_and_pc.
Hint Unfold Concrete.next_state_pc.
Hint Unfold Concrete.next_state.
Hint Unfold Concrete.miss_state.

Let in_kernel_user t ic : Concrete.is_kernel_tag _ (encode (USER t ic)) = false.
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

  | GET : PartMaps.get ?mem1 ?addr = Some ?x@(encode (USER ?t false)),
    USERMEM : user_mem_unchanged ?mem1 ?mem2 |- _ =>
    match goal with
    | _ : PartMaps.get mem2 addr = _ |- _ => fail 1
    | |- _ => idtac
    end;
    assert (PartMaps.get mem2 addr = Some x@(encode (USER t false)));
    try solve [eapply USERMEM; assumption]

  | H : PartMaps.upd ?amem ?addr _ = _,
    REFM : refine_memory ?amem ?cmem |- _ =>
    match goal with
      | _ : PartMaps.upd cmem addr _ = _ |- _ => fail 1
      | |- _ => idtac
    end;
    let old := fresh "old" in
    let Hold := fresh "Hold" in
    let cmem' := fresh "cmem'" in
    let UPD' := fresh "UPD'" in
    let REFM' := fresh "REFM'" in
    destruct (refine_memory_upd' _ _ _ REFM H) as (cmem' & UPD' & REFM')

  | H : PartMaps.get ?aregs ?r = Some _,
    REFR : refine_registers ?aregs ?cregs |- _ =>
    apply REFR in H

  | UPD : PartMaps.upd ?aregs ?r _ = Some _,
    REFR : refine_registers ?aregs ?cregs |- _ =>
    match goal with
    | _ : TotalMaps.get cregs r = _ |- _ => fail 1
    | |- _ => idtac
    end;
    let old := fresh "old" in
    let Hold := fresh "Hold" in
    let UPD' := fresh "UPD'" in
    destruct (PartMaps.upd_inv (*Symbolic.reg_axioms (t := mt)*) _ _ _ UPD) as [old Hold];
    apply REFR in Hold;
    assert (UPD' := refine_registers_upd' _ _ REFR UPD)

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
  | GET : PartMaps.get _ ?addr = Some _,
    USERMEM : user_mem_unchanged _ _
    |- PartMaps.get _ ?addr = Some _ =>
    simpl in GET, USERMEM;
    rewrite <- (USERMEM addr); eassumption

  | GET : TotalMaps.get _ ?r = _,
    USERREGS : user_regs_unchanged _ _
    |- TotalMaps.get _ ?r = _ =>
    simpl in GET, USERREGS;
    rewrite <- (USERREGS r); eauto
  end.

Lemma no_syscall_no_entry_point mem addr :
  wf_entry_points table mem ->
  Symbolic.get_syscall table addr = None ->
  negb match PartMaps.get mem addr with
       | Some _@it => it == encode ENTRY
       | None => false
       end = true.
Proof.
  intros WF GETSC.
  destruct (match PartMaps.get mem addr with
            | Some _@it => it == encode ENTRY
            | None => false
            end) eqn:E; trivial.
  apply WF in E.
  destruct E. congruence.
Qed.

(* Just for automation *)
Let kernel_invariant_ra_upd mem regs cache int w t:
  ki mem regs cache int ->
  ra_in_user regs ->
  ki mem (TotalMaps.upd regs ra w@(encode (USER t false))) cache int.
Proof.
  intros KINV RA.
  unfold ra_in_user, word_lift in RA.
  destruct (TotalMaps.get regs ra) as [v t'] eqn:E.
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

Ltac destruct_mvec_operands :=
  repeat match goal with
  | ts : Vector.t _ 0 |- _ => induction ts using Vector.case0
  | ts : Vector.t _ (S _) |- _ => induction ts using caseS
  | ts : Empty_set |- _ => destruct ts
  end.

Let symbolic_handler_concrete_cache cache umvec ic urvec rvec :
  cache_correct cache ->
  Symbolic.handler umvec = Some urvec ->
  Concrete.cache_lookup _ cache masks (encode_mvec (mvec_of_umvec ic umvec)) = Some rvec ->
  rvec = encode_rvec (rvec_of_urvec (Symbolic.op umvec) urvec).
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
  destruct_mvec_operands; simpl in *;
  rewrite HANDLER in E3; simpl in E3; congruence.
Qed.

Let symbolic_handler_concrete_handler mvec rvec ic :
  Symbolic.handler mvec = Some rvec ->
  match decode_mvec (encode_mvec (mvec_of_umvec ic mvec)) with
  | Some mvec => handler (fun m => Symbolic.handler m) mvec
  | None => None
  end = Some (rvec_of_urvec (Symbolic.op mvec) rvec).
Proof.
  intros H.
  rewrite decode_mvecK; eauto.
  destruct mvec as [op tpc ti ts].
  unfold handler, rules.handler. simpl.
  destruct op; simpl in *;
  destruct_mvec_operands; simpl in *; now rewrite H.
Qed.

Ltac solve_refine_state :=
  unfold in_user, word_lift in *; simpl in *;
  repeat rewrite decodeK; simpl in *;
  try match goal with
  | USERREGS : user_regs_unchanged ?cregs _,
    H : TotalMaps.get ?cregs ?r = _ |- _ =>
    simpl in USERREGS; rewrite -> (USERREGS r) in H
  end;
  repeat match goal with
  | |- _ /\ _ =>
    split;
    eauto using user_mem_unchanged_refine_memory,
                refine_registers_upd', user_regs_unchanged_refine_registers,
                user_regs_unchanged_ra_in_user, ra_in_user_upd,
                mvec_in_kernel_user_upd, wf_entry_points_user_upd,
                no_syscall_no_entry_point, kernel_invariant_ra_upd
  end.

Ltac analyze_syscall :=
  match goal with
  | H : Symbolic.sem _ _ = Some ?ast' |- _ =>
    destruct ast' as [amem' aregs' [apc' tapc'] int'];
    exploit syscalls_correct_allowed_case; eauto;
    intros;
    repeat match goal with
    | H : exists _, _ |- _ => destruct H
    | H : _ /\ _ |- _ => destruct H
    end
  end.

Lemma forward_simulation ast ast' cst :
  refine_state ki table ast cst ->
  Symbolic.step table ast ast' ->
  exists cst',
    exec (Concrete.step _ masks) cst cst' /\
    refine_state ki table ast' cst'.
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
      try analyze_syscall;
      try solve [eexists; split;
                 [apply exec_one; solve_concrete_step|solve_refine_state]]

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
      match_data;
      unfold encode_mvec, encode_rvec, rvec_of_urvec in *; simpl in *;
      try analyze_syscall;
      try solve [eexists; split;
      [
        eapply re_step; trivial; [solve_concrete_step|];
        try (
          eapply restricted_exec_trans;
          try solve [eapply exec_until_weaken; eapply KEXEC];
          try solve [eapply exec_one; solve_concrete_step]
        )
      | solve_refine_state ] ]
      (* || let op := current_instr_opcode in fail 3 "failed miss case" op *)
    ]
  end.

  - exploit H; eauto. clear H. intros H.
    repeat match goal with
    | H : exists _, _ |- _ => destruct H
    | H : _ /\ _ |- _ => destruct H
    end.
    eexists. split.
    + eapply re_step; trivial; [solve_concrete_step|].
      eapply exec_until_weaken.
      eassumption.
    + solve_refine_state.

  - exploit H4; eauto. clear H4. intros H4.
    repeat match goal with
    | H : exists _, _ |- _ => destruct H
    | H : _ /\ _ |- _ => destruct H
    end.
    eexists. split.
    + eapply re_step; trivial; [solve_concrete_step|].
      eapply restricted_exec_trans.
      { eapply exec_until_weaken. eassumption. }
      eapply re_step; trivial; [solve_concrete_step|].
      eapply exec_until_weaken. eassumption.
    + solve_refine_state.

Qed.

End Refinement.
