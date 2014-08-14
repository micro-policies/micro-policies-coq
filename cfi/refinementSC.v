Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Require Import Coq.Lists.List.
Require Import lib.Integers.
Require Import lib.utils.
Require Import lib.partial_maps.
Require Import lib.Coqlib.
Require lib.list_utils.
Require Import common.common.
Require Import symbolic.symbolic.
Require Import symbolic.exec.
Require Import concrete.concrete.
Require Import concrete.exec.
Require Import cfi.classes.
Require Import cfi.concrete.
Require Import cfi.symbolic.
Require Import cfi.preservation.
Require Import cfi.rules.
Require Import cfi.refinementAS. (*for Map - should remove when we move it*)
Require Import symbolic.backward.
Require Import symbolic.refinement_common.

Set Implicit Arguments.

Import PartMaps.

Section Refinement.

Context {mt : machine_types}
        {ops : machine_ops mt}
        {opss : machine_ops_spec ops}
        {ids : @classes.cfi_id mt}
        {e : @rules.encodable mt rules.cfi_tag_eqType}.

Variable cfg : id -> id -> bool.

Instance sp : Symbolic.params := Sym.sym_cfi cfg.

Variable stable : list (Symbolic.syscall mt).
Variable ki : refinement_common.kernel_invariant.

Definition masks := symbolic.rules.masks.

(*Used for our invariants*)
Hypothesis syscall_preserves_instruction_tags :
  forall sc st st',
    Sym.instructions_tagged (cfg := cfg) (Symbolic.mem st) ->
    Symbolic.sem sc st = Some st' ->
    Sym.instructions_tagged (cfg := cfg) (Symbolic.mem st').

Hypothesis syscall_preserves_valid_jmp_tags :
  forall sc st st',
    Sym.valid_jmp_tagged stable (Symbolic.mem st) ->
    Symbolic.sem sc st = Some st' ->
    Sym.valid_jmp_tagged stable (Symbolic.mem st').

Hypothesis syscall_preserves_entry_tags :
  forall sc st st',
    Sym.entry_points_tagged stable (Symbolic.mem st) ->
    Symbolic.sem sc st = Some st' ->
    Sym.entry_points_tagged stable (Symbolic.mem st').

Definition refine_state_no_inv (sst : Symbolic.state mt) (cst : Concrete.state mt) :=
  @refine_state_weak mt ops sp (fun _ => e) ki stable sst cst.

Definition refine_state (sst : Symbolic.state mt) (cst : Concrete.state mt) :=
  @refine_state_weak mt ops sp (fun _ => e) ki stable sst cst /\
  Sym.invariants stable sst.

Definition is_user (x : atom (word mt) (word mt)) :=
  rules.word_lift (fun t => rules.is_user t) (common.tag x).

Definition coerce (x : atom (word mt) (word mt)) : atom (word mt) (cfi_tag) :=
  match rules.decode (common.tag x) with
    | Some (rules.USER tg) => (common.val x)@tg
    | _ => (common.val x)@DATA (*this is unreachable in our case, dummy value*)
  end.

Lemma mem_refinement_equiv :
  forall (smem : Symbolic.memory mt sp) cmem cmem',
    refinement_common.refine_memory smem cmem ->
    Conc.equiv cmem cmem' ->
    exists (smem' : Symbolic.memory mt sp),
    refinement_common.refine_memory smem' cmem' /\
    Sym.equiv smem smem'.
Proof.
  intros smem cmem cmem' REF EQUIV.
  exists (PartMaps.map coerce (filter is_user cmem')).
  split.
  { (*refinement proof*)
    intros addr v tg.
    split.
    { intro CGET.
      rewrite PartMaps.map_correctness. rewrite filter_correctness.
      rewrite CGET. simpl.
      destruct (is_user v@(rules.encode (rules.USER (user_tag:=cfi_tags Symbolic.M) tg))) eqn:USER.
      + simpl. unfold coerce. simpl. rewrite rules.decodeK. reflexivity.
      + unfold is_user in USER. simpl in USER.
        unfold rules.word_lift in USER.
        rewrite rules.decodeK in USER. simpl in USER. discriminate. }
    { intro SGET.
      rewrite PartMaps.map_correctness filter_correctness in SGET.
      destruct (get cmem' addr) eqn:CGET.
      - destruct a as [cv ctg].
        simpl in SGET.
        unfold is_user, rules.word_lift in SGET.
        destruct (rules.decode ctg) eqn:CTG.
        + destruct t; rewrite CTG in SGET; simpl in *.
          * unfold coerce in SGET. rewrite CTG in SGET.
            simpl in SGET. inv SGET.
            simpl. apply rules.encodeK in CTG. rewrite CTG. reflexivity.
          * discriminate.
          * discriminate.
        + rewrite CTG in SGET. simpl in SGET; discriminate.
      - simpl in SGET. discriminate.
    }
  }
  { (*equiv proof*)
    unfold Sym.equiv, pointwise.
    intro addr.
    unfold Conc.equiv in EQUIV. unfold pointwise in EQUIV.
    specialize (EQUIV addr). simpl.
    destruct (get smem addr) eqn:SGET; simpl in SGET; rewrite SGET.
    - destruct a as [v utg].
      unfold refinement_common.refine_memory in REF.
      specialize (REF addr v utg).
      destruct REF as [REFCS REFSC].
      assert (CGET := REFSC SGET).
      rewrite CGET in EQUIV.
      destruct (get cmem' addr) eqn:CGET'.
      + destruct a as [v' ctg'].
        inversion EQUIV
          as [a a' v0 v'' ut ut' EQ1 EQ2 SEQUIV| a a' NEQ EQ]; subst.
        * rewrite PartMaps.map_correctness filter_correctness.
          rewrite CGET'.
          unfold is_user. unfold rules.word_lift.
          simpl. inversion EQ1; inversion EQ2; subst.
          rewrite rules.decodeK.
          simpl. unfold coerce.
          simpl. rewrite rules.decodeK.
          apply rules.encode_inj in H1.
          inversion H1; subst.
          assumption.
        * simpl in NEQ.
          assert (CONTRA: (exists ut : cfi_tag,
           rules.encode (rules.USER (user_tag:=cfi_tag_eqType) utg) =
           rules.encode (rules.USER (user_tag:=cfi_tag_eqType) ut)))
             by (eexists; eauto).
          apply NEQ in CONTRA. destruct CONTRA.
      + destruct EQUIV.
    - destruct (get cmem addr) eqn:CGET.
      + destruct a as [v ctg]. unfold refinement_common.refine_memory in REF.
        rewrite PartMaps.map_correctness filter_correctness.
        unfold is_user. unfold rules.word_lift.
        destruct (get cmem' addr) eqn:CGET'.
        * destruct a as [v' ctg'].
          simpl.
          destruct (rules.decode ctg') eqn:DECODE.
          - destruct (rules.is_user t) eqn:USER.
            + simpl.
              unfold rules.is_user in USER.
              destruct t; try discriminate.
              apply rules.encodeK in DECODE.
              rewrite <- DECODE in EQUIV.
              inversion EQUIV
                as [a a' v0 v'' ? ut' EQ1 EQ2 SEQUIV| a a' NEQ EQ]; subst.
               { inversion EQ1; subst.
                 apply REF in CGET. rewrite SGET in CGET; discriminate. }
               { simpl in NEQ.
                 inv EQ.
                 apply NEQ. eexists; eauto.
               }
            + simpl. constructor.
          - simpl. constructor.
        * destruct EQUIV.
     + destruct (get cmem' addr) eqn:CGET'.
       * destruct EQUIV.
       * rewrite PartMaps.map_correctness filter_correctness.
         rewrite CGET'. simpl. constructor.
  }
Qed.

Definition creg_to_sreg x :=
  match is_user x with
    | true => Some (coerce x)
    | false => None
  end.

Lemma reg_refinement_equiv :
  forall (sregs : Symbolic.registers mt sp) cregs cregs',
    refinement_common.refine_registers sregs cregs ->
    Conc.reg_equiv cregs cregs' ->
    exists (sregs' : Symbolic.registers mt sp),
    refinement_common.refine_registers sregs' cregs' /\
    Sym.equiv sregs sregs'.
Proof.
  intros sreg creg creg' REF EQUIV.
  exists (PartMaps.map_filter creg_to_sreg creg').
  split.
  { (*Refinement proof*)
    intros n v tg.
    split.
    { intros CGET'.
      rewrite PartMaps.map_filter_correctness.
      rewrite CGET'. simpl.
      unfold creg_to_sreg.
      destruct (is_user v@(rules.encode (rules.USER (user_tag:=cfi_tags Symbolic.R) tg))) eqn:USER.
      + simpl. unfold coerce. simpl. rewrite rules.decodeK. reflexivity.
      + unfold is_user in USER. simpl in USER.
        unfold rules.word_lift in USER.
        rewrite rules.decodeK in USER. simpl in USER. discriminate. }
    { intro SGET'.
      rewrite PartMaps.map_filter_correctness in SGET'.
      destruct (PartMaps.get creg' n) as [[v' t']|] eqn:CGET'; last by [].
      simpl in SGET'.
      unfold creg_to_sreg in SGET'.
      unfold is_user, rules.word_lift in SGET'.
      simpl in SGET'.
      destruct (rules.decode t') eqn:CTG.
      + unfold rules.is_user, coerce in SGET'. destruct t; simpl in CTG.
        * rewrite CTG in SGET'.
          simpl in SGET'. inv SGET'.
          simpl. apply rules.encodeK in CTG. rewrite CTG. reflexivity.
        * discriminate.
        * discriminate.
      + discriminate.
    }
  }
  { (*equiv proof*)
    unfold Sym.equiv, pointwise.
    intro n.
    unfold Conc.reg_equiv in EQUIV.
    specialize (EQUIV n).
    destruct EQUIV as ([v1 t1] & [v2 t2] & E1 & E2 & EQUIV).
    destruct (get sreg n) eqn:SGET; simpl in SGET; rewrite SGET.
    - destruct a as [v utg].
      specialize (REF n v utg).
      destruct REF as [REFCS REFSC].
      assert (CGET := REFSC SGET).
      rewrite CGET in E1. inversion E1; subst v1 t1; clear E1.
      rewrite PartMaps.map_filter_correctness.
      inversion EQUIV
        as [a a' v0 v'' ? ut' EQ1 EQ2 SEQUIV| a a' NEQ EQ]; subst.
      * inv EQ2.
        unfold creg_to_sreg, is_user, rules.word_lift, coerce, rules.is_user.
        simpl. rewrite E2. simpl. rewrite rules.decodeK.
        inv EQ1.
        apply rules.encode_inj in H1. inv H1.
        assumption.
      * inv EQ. simpl in NEQ.
        assert (CONTRA: (exists ut : cfi_tag,
           rules.encode (rules.USER (user_tag:=cfi_tag_eqType) utg) =
           rules.encode (rules.USER (user_tag:=cfi_tag_eqType) ut)))
          by (eexists; eauto).
        apply NEQ in CONTRA. destruct CONTRA.
    - rewrite PartMaps.map_filter_correctness.
      rewrite E2. simpl.
      inversion EQUIV
        as [a a' v0 v'' ? ut' EQ1 EQ2 SEQUIV| a a' NEQ EQ]; subst.
       + inv EQ1.
         apply REF in E1.
         rewrite E1 in SGET. discriminate.
       + inv EQ.
         unfold creg_to_sreg, is_user, rules.word_lift, coerce.
         simpl.
         destruct (rules.decode t2) eqn:DECODE.
         { destruct t.
           - apply rules.encodeK in DECODE.
             simpl in NEQ.
             exfalso. apply NEQ. eexists; eauto.
           - unfold rules.is_user. constructor.
           - unfold rules.is_user. constructor.
         }
         { constructor. }
  }
Qed.

(*Kernel invariants preserved by attacker*)
Lemma mvec_in_kernel_preserved_by_equiv
      (mem : Concrete.memory mt) (mem' : Concrete.memory mt) :
  refinement_common.mvec_in_kernel mem ->
  Conc.equiv mem mem' ->
  refinement_common.mvec_in_kernel mem'.
Proof.
  intros INV MEQUIV.
  unfold refinement_common.mvec_in_kernel.
  intros addr INMVEC.
  specialize (INV addr).
  apply INV in INMVEC.
  destruct INMVEC as [v GET].
  unfold Conc.equiv, pointwise in MEQUIV.
  specialize (MEQUIV addr).
  rewrite GET in MEQUIV.
  destruct (get mem' addr) eqn:GET'.
  - inversion MEQUIV
      as [? a' v0 v'' ? ut' EQ1 EQ2 SEQUIV| ? a' NEQ EQ]; subst.
    + inversion EQ1; subst.
      rewrite rules.encode_kernel_tag in H1.
      apply rules.encode_inj in H1.
      discriminate.
    + eexists; reflexivity.
  - destruct MEQUIV.
Qed.

Lemma wf_entry_points_preserved_by_equiv
      (mem : Concrete.memory mt) (mem' : Concrete.memory mt) :
  refinement_common.wf_entry_points stable mem ->
  Conc.equiv mem mem' ->
  refinement_common.wf_entry_points stable mem'.
Proof.
  intros INV MEQUIV.
  intros addr stg.
  specialize (INV addr stg).
  specialize (MEQUIV addr).
  split.
  { intro SCALL.
    apply INV in SCALL.
    case: (get mem addr) INV MEQUIV SCALL => [[v ctg]|] INV MEQUIV SCALL; last by [].
    case: (get mem' addr) MEQUIV => [[v' ctg']|] MEQUIV; last by [].
    inversion MEQUIV
          as [? a' v0 v'' ? ut' EQ1 EQ2 SEQUIV| ? a' NEQ EQ]; subst.
    - inv EQ1.
      apply andb_true_iff in SCALL.
      destruct SCALL as [? SCALL].
      move/eqP/rules.encode_inj: SCALL => CONTRA.
      inversion CONTRA.
    - simpl in *. inv EQ. assumption.
  }
  { intro CALL.
    case: (get mem' addr) INV MEQUIV CALL => [[v' ctg']|] //= INV MEQUIV CALL.
    case: (get mem addr) INV MEQUIV => [[v ctg]|] //= INV MEQUIV.
    inversion MEQUIV
          as [? a' v0 v'' ? ut' EQ1 EQ2 SEQUIV| ? a' NEQ EQ]; subst.
    + inv EQ2.
      apply andb_true_iff in CALL.
      destruct CALL as [? CALL].
      move/eqP/rules.encode_inj: CALL => CONTRA.
      inversion CONTRA.
    + simpl in *. inv EQ. apply INV in CALL.
      assumption.
  }
Qed.

(*Q: Do we want to prove anything about this? Maybe using the other assumptions
   on ki?*)
Hypothesis ki_preserved_by_equiv :
  forall mem mem' reg reg' cache int,
    refinement_common.kernel_invariant_statement ki mem reg cache int ->
    Conc.equiv mem mem' ->
    Conc.reg_equiv reg reg' ->
    refinement_common.kernel_invariant_statement ki mem' reg' cache int.

Hint Resolve mvec_in_kernel_preserved_by_equiv.
Hint Resolve wf_entry_points_preserved_by_equiv.

Lemma backwards_simulation_attacker_aux sst cst cst' :
  refine_state_no_inv sst cst ->
  Conc.step_a cst cst' ->
  exists sst',
    Sym.step_a sst sst' /\
    refine_state_no_inv sst' cst'.
Proof.
  intros REF STEP.
  inversion STEP; subst.
  unfold refine_state in REF.
  destruct REF as [REF | CONTRA].
  move: tpc INUSER REF STEP => tpc' INUSER REF STEP.
  - destruct REF as [smem sreg int cmem cregs cache' epc' pc' tpc
                     ? ? REFM REFR ? ? WFENTRY ?].
    subst sst.
    symmetry in EC. inv EC.
    destruct (mem_refinement_equiv REFM MEQUIV) as [smem' [REFM' SMEQUIV]].
    destruct (reg_refinement_equiv REFR REQUIV) as [sreg' [REFR' SREQUIV]].
    eexists; split; [idtac | left]; econstructor; eauto.
  - destruct CONTRA as [? [? [? [? CONTRA]]]].
    clear REQUIV MEQUIV.
    unfold refinement_common.kernel_exec in CONTRA.
    apply restricted_exec_snd in CONTRA.
    unfold refinement_common.in_kernel in CONTRA.
    simpl in CONTRA. unfold Concrete.is_kernel_tag in CONTRA.
    unfold rules.word_lift in INUSER.
    move/eqP: CONTRA => CONTRA.
    rewrite CONTRA in INUSER.
    rewrite rules.encode_kernel_tag in INUSER.
    rewrite rules.decodeK in INUSER.
    unfold rules.is_user in INUSER.
    congruence.
Qed.

Theorem backwards_simulation_attacker sst cst cst' :
  refine_state sst cst ->
  Conc.step_a cst cst' ->
  exists sst',
    Sym.step_a sst sst' /\
    refine_state sst' cst'.
Proof.
  intros REF STEP.
  destruct REF as [REF INV];
  destruct (backwards_simulation_attacker_aux REF STEP) as [sst' [SSTEP REF']];
  eexists; split; [eassumption | split];
  eauto using Sym.invariants_preserved_by_step_a.
Qed.

(* Preservation related stuff, probably move to other file*)

Definition smachine := Sym.symbolic_cfi_machine stable.
Definition cmachine := Conc.concrete_cfi_machine ki stable masks.

Context {kcc : kernel_code_correctness ki stable}. (*should this go to the top?*)

Definition check st st' := in_user st && in_user st'.

Program Instance cfi_refinementSC  :
  (machine_refinement smachine cmachine) := {
    refine_state st st' := refine_state st st';

    check st st' := check st st'
}.
Next Obligation.
Proof.
  unfold refine_state in REF.
  destruct REF as [REF INV].
  destruct REF as [UREF | KREF].
  - (*starting from a user state*)
    split.
    { (*Visible step starting from a user state*)
      intro VIS.
      unfold check in VIS.
      apply andb_true_iff in VIS.
      destruct VIS as [VIS VIS'].
      assert (HIT: hit_step cst cst')
          by (constructor; auto).
      destruct (cache_hit_simulation UREF HIT) as [sst' [SSTEP REF']].
      unfold refine_state, refine_state_weak.
      eexists; split. eauto.
      split;
      eauto using Sym.invariants_preserved_by_step.
    }
    { (*invisible step starting a from user state*)
      intro INVIS.
      unfold check in INVIS.
      apply andb_false_iff in INVIS.
      destruct INVIS as [CONTRA | NUSER].
      - eapply @refine_state_in_user in UREF.
        rewrite UREF in CONTRA.
        by discriminate.
      - (*user to not user step*)
        left.
        unfold refine_state. split.
        right. exists cst; exists cst'.
        repeat (split; auto).
        unfold kernel_exec.
        destruct (user_into_kernel UREF STEP NUSER).
        eapply re_refl; eauto.
        eauto using Sym.invariants_preserved_by_step.
    }
  - (*starting from a kernel state*)
    split.
    { (*and taking a visible step*)
      intro VIS.
      unfold check in VIS.
      apply andb_true_iff in VIS.
      destruct VIS as [VIS VIS'].
      destruct KREF as [ust [kst [UREF [UKSTEP KEXEC]]]].
      unfold kernel_exec in KEXEC.
      apply restricted_exec_snd in KEXEC.
      unfold in_user in VIS. admit. (*
      apply in_user_in_kernel in VIS.
      rewrite VIS in KEXEC. discriminate. *)
    }
    { (*and taking an invisible step*)
      intro VIS.
      assert (REFW : @refine_state_weak mt ops sp (fun _ => e) ki stable ast cst)
        by (right; auto).
      destruct (backwards_simulation REFW STEP) as [REFW' | [ast' [STEP' REF']]].
      - left. split; auto.
      - right. eexists; split; eauto.
        unfold refine_state.
        split.
        + left. assumption.
        + eauto using Sym.invariants_preserved_by_step.
    }
Qed.
Next Obligation.
  apply (backwards_simulation_attacker REF STEPA).
Qed.

Import ListNotations.

(*XXX: Move this to refinement_common?*)
Lemma kernel_step cst cst' ast kst cst0 :
  refinement_common.refine_state ki stable ast cst0 ->
  Concrete.step ops rules.masks cst0 kst ->
  kernel_exec kst cst ->
  Concrete.step _ masks cst cst' ->
  in_kernel cst = true ->
  in_user cst' = false ->
  in_kernel cst' = true.
Proof.
  intros REF STEP EXEC STEP' INKERNEL INUSER.
  assert (REFW: @refine_state_weak _ _ _ _ ki stable ast cst).
  { right. eauto. }
  generalize (backwards_simulation REFW STEP').
  intros [[REF' | (? & ? & ? & ? & KEXEC')] | (? & _ & REF')].
  - apply @refine_state_in_user in REF'. by congruence.
  - by apply restricted_exec_snd in KEXEC'.
  - apply @refine_state_in_user in REF'. by congruence.
Qed.

(*This is a helper lemma to instantiate CFI refinement between
  symbolic and concrete*)
Lemma attacker_no_v : forall si sj,
                 Sym.invariants stable si ->
                 Sym.ssucc stable si sj = false ->
                 Symbolic.step stable si sj ->
                 Sym.step_a si sj ->
                 False.
Proof.
  intros si sj INV SUCC STEP STEPA.
  destruct INV as [ITG [VTG ETG]].
  inversion STEPA. subst.
  inversion STEP;
   repeat (
      match goal with
        | [H: Symbolic.next_state_pc _ _ _ = _ |- _] =>
          unfold Symbolic.next_state_pc in H
        | [H: Symbolic.next_state_reg _ _ _ _ = _ |- _] =>
          unfold Symbolic.next_state_reg in H
        | [H: Symbolic.next_state_reg_and_pc _ _ _ _ _ = _ |- _] =>
          unfold Symbolic.next_state_reg_and_pc in H
        | [H: Symbolic.next_state _ _ _ = Some _ |- _] =>
          unfold Symbolic.next_state in H; simpl in H; match_inv
      end); subst;
   unfold Sym.ssucc in SUCC; simpl in SUCC;
   inversion ST; try subst;

   try match goal with
     | [H: (?Pc + 1)%w = ?Pc |- _] =>
       rewrite H in SUCC; try subst mem' reg' int; try subst mem reg
  end;
   try rewrite PC in SUCC; try rewrite INST in SUCC;
   try match goal with
     | [H: Some _ = Some _ |- _] => simpl in H; inversion H
   end;
   try match goal with
         | [H: match ?Expr with _ => _ end = _ |- _] =>
           destruct Expr eqn:?
       end;
   try match goal with
     | [H: (?Pc + 1)%w = ?Pc |- _] =>
       rewrite H in SUCC; rewrite eqxx in SUCC; discriminate
   end.
  (*jump case*)
  unfold Sym.instructions_tagged in ITG.
  specialize (ITG _ _ _ PC). simpl in ITG. subst.
  congruence.
  (*bnz case*)
  destruct (w == 0%w).
  - subst mem' reg'. simpl in *.
    destruct a as [v [|]].
    + rewrite H2 in Heqo0. rewrite PC in Heqo0. inversion Heqo0. subst o i.
      rewrite INST in SUCC.
      destruct o0;
      apply orb_false_iff in SUCC; destruct SUCC;
      rewrite H2 in H; rewrite H2 in H; rewrite eqxx in H; by discriminate.
    + rewrite H2 in Heqo0. rewrite Heqo0 in PC. by inversion PC.
  - subst mem' reg'. simpl in *.
    destruct a as [v [|]].
    + rewrite H2 in Heqo0. rewrite PC in Heqo0. inversion Heqo0. subst o i.
      rewrite INST in SUCC.
      destruct o0;
      apply orb_false_iff in SUCC; destruct SUCC;
      rewrite H2 in H0; rewrite H2 in H0; rewrite eqxx in H0; by discriminate.
    + rewrite H2 in Heqo0. rewrite Heqo0 in PC. by inversion PC.
  subst mem' reg' int.
  rewrite H2 in Heqo0.
  rewrite Heqo0 in PC. by discriminate.
 (*jal case*)
  unfold Sym.instructions_tagged in ITG.
  specialize (ITG _ _ _ PC). simpl in ITG. subst.
  congruence.
  (*syscall case*)
  by discriminate.
  rewrite GETCALL in Heqo.
  by discriminate.
Qed.

Definition khandler := rules.handler (fun _ => e) (@Symbolic.transfer sp).
Definition uhandler := @Symbolic.transfer sp.

(*XXX: Move these to refinement_common*)
Lemma get_reg_no_user sreg reg r v ctg t :
  @refinement_common.refine_registers mt sp (fun _ => e) sreg reg ->
  get sreg r = None ->
  PartMaps.get reg r = Some v@ctg ->
  rules.decode ctg = Some t ->
  t = rules.KERNEL \/ (exists ut, t = rules.ENTRY ut).
Proof.
  intros REF SGET GET DEC.
  destruct t.
  - apply rules.encodeK in DEC.
    rewrite <- DEC in GET.
    apply REF in GET.
    rewrite SGET in GET. discriminate.
  - auto.
  - right; eexists; reflexivity.
Qed.

Lemma get_mem_no_user smem mem addr v ctg t :
  @refinement_common.refine_memory mt sp (fun _ => e) smem mem ->
  get smem addr = None ->
  get mem addr = Some v@ctg ->
  rules.decode ctg = Some t ->
  t = rules.KERNEL \/ (exists ut, t = rules.ENTRY ut).
Proof.
  intros REF SGET GET DEC.
  destruct t.
  - apply rules.encodeK in DEC.
    rewrite <- DEC in GET.
    apply REF in GET.
    rewrite SGET in GET. discriminate.
  - auto.
  - right; eexists; reflexivity.
Qed.

Lemma in_user_ctpc cst :
  refinement_common.in_user cst = true ->
  exists ut,
    rules.decode (common.tag (Concrete.pc cst)) = Some (rules.USER ut).
Proof.
  intros USER.
  unfold refinement_common.in_user in USER.
  unfold rules.word_lift in USER.
  destruct (rules.decode (common.tag (Concrete.pc cst))) eqn:DEC.
  - destruct t.
    + eexists; reflexivity.
    + simpl in USER. discriminate.
    + simpl in USER. discriminate.
  - discriminate.
Qed.

(*Case 1: umvec = Some & cmvec = Some*)

Lemma umvec_implies_cmvec sst cst smvec :
  in_user cst ->
  refine_state sst cst ->
  build_ivec stable sst = Some smvec ->
  exists cmvec, build_cmvec mt cst = Some cmvec.
Proof.
  intros USER [[REF | CONTRA] ?] MVEC.
  - eexists. eapply refine_ivec; eauto.
  - exfalso.
    destruct CONTRA as [? [? [? [? KEXEC]]]].
    apply restricted_exec_snd in KEXEC.
    unfold in_user in USER.
    admit. (*eapply @in_user_in_kernel in USER.
    by congruence.*)
Qed.

Lemma unique_cmvec sst cst umvec cmvec :
  in_user cst = true ->
  refine_state sst cst ->
  build_ivec stable sst = Some umvec ->
  build_cmvec mt cst = Some cmvec ->
  rules.encode_ivec (fun _ => e) (rules.ivec_of_uivec umvec) = cmvec.
Proof.
  intros USER REF MVEC CMVEC.
  destruct REF as [REF INV].
  destruct REF as [UREF | KREF].
  - erewrite -> refine_ivec in CMVEC; eauto.
    by move: CMVEC => [<-].
  - destruct KREF as [? [? [? [? KEXEC]]]].
    apply restricted_exec_snd in KEXEC.
    eapply @in_user_in_kernel in USER.
    by congruence.
Qed.

(*Case 2*)

Lemma no_user_access_implies_halt sst cst cmvec :
  in_user cst = true ->
  refine_state sst cst ->
  build_ivec stable sst = None ->
  build_cmvec mt cst = Some cmvec ->
  khandler cmvec = None.
Proof.
  intros USER REF MVEC CMVEC.
  destruct REF as [REF ?].
  destruct REF as [REF | CONTRA].
  - destruct (khandler cmvec) as [rvec|] eqn:E; last by [].
    generalize (handler_build_ivec REF CMVEC E).
    move => [? ?] //. congruence.
  - destruct CONTRA as [? [? [? [? KEXEC]]]].
    apply restricted_exec_snd in KEXEC.
    eapply @in_user_in_kernel in USER.
    by congruence.
Qed.

(*Case 3*)

Lemma fault_steps_at_kernel_aux ast cst cst' cmvec :
  refinement_common.refine_state ki stable ast cst ->
  Concrete.step _ masks cst cst' ->
  build_cmvec mt cst = Some cmvec ->
  khandler cmvec = None ->
  exists cmem',
  Concrete.store_mvec (Concrete.mem cst) cmvec = Some cmem' /\
  cst' = Concrete.mkState cmem'
                          (Concrete.regs cst)
                          (Concrete.cache cst)
                          (Concrete.fault_handler_start mt)@Concrete.TKernel
                          (Concrete.pc cst).
Proof.
  intros REF CSTEP CMVEC KHANDLER.
  destruct REF as [smem sreg int cmem creg cache epc pc tpc
                         ASI CSI REFM REFR CACHE MVEC WF KI].
  case LOOKUP: (Concrete.cache_lookup cache masks cmvec) => [rvec|].
  - have ISUSER: rules.word_lift (fun x => rules.is_user x) (Concrete.ctpc cmvec) = true.
    { move: CMVEC => /(build_cmvec_ctpc _) ->.
      by rewrite CSI /rules.word_lift ?rules.decodeK /=. }
    move: (CACHE _ _ ISUSER LOOKUP) => [? [? [HANDLER1 [HANDLER2 [HANDLER3 HANDLER4]]]]].
    rewrite /khandler /rules.handler HANDLER1 /= rules.decode_ivecK
            /= rules.ivec_of_uivec_privileged (negbTE HANDLER4) in KHANDLER.
    admit.
  - generalize (mvec_in_kernel_store_mvec cmvec MVEC).
    move => {MVEC} [cmem' MVEC].
    eexists cmem'.
    subst cst.
    split; first by [].
    eapply initial_handler_state'; try eassumption.
    by rewrite /in_user /rules.word_lift /= rules.decodeK.
Qed.

Lemma fault_steps_at_kernel ast cst cst' cmvec :
  in_user cst = true ->
  refine_state ast cst ->
  Concrete.step _ masks cst cst' ->
  build_cmvec mt cst = Some cmvec ->
  khandler cmvec = None ->
  exists cmem',
  Concrete.store_mvec (Concrete.mem cst) cmvec = Some cmem' /\
  cst' = Concrete.mkState cmem'
                          (Concrete.regs cst)
                          (Concrete.cache cst)
                          (Concrete.fault_handler_start mt)@Concrete.TKernel
                          (Concrete.pc cst).
Proof.
  intros USER REF STEP MVEC HANDLER.
  destruct REF as [REF ?].
  destruct REF as [UREF | KREF].
  - eauto using fault_steps_at_kernel_aux.
  - destruct KREF as [? [? [? [? KEXEC]]]].
    apply restricted_exec_snd in KEXEC.
    eapply @in_user_in_kernel in USER.
    by congruence.
Qed.

Lemma refine_traces_kexec axs cxs cst cst' :
  refine_traces cfi_refinementSC axs (cst :: cxs) ->
  in_kernel cst = true ->
  In cst' cxs ->
  in_kernel cst' \/ exists cst'',
                      in_user cst'' = true /\
                      exec (Concrete.step ops masks) cst cst''.
Proof.
  intros RTRACE KERNEL IN.
  gdep cst. gdep axs.
  induction cxs; intros.
  - destruct IN.
  - inversion RTRACE
        as [? ? REF' | ? ? ? ? ? STEP CHECK REF REF' RTRACE'
            | ? ? ? ? ? ? STEP ASTEP REF REF' RTRACE'
            | ? ? ? ? ? ? NSTEP STEPA CSTEPA REF REF' RTRACE'];
    subst; simpl in *.
    { (*non-visible step*)
      destruct IN as [? | IN]; subst.
      + destruct (in_user cst') eqn:USER.
        * right. exists cst'. split; auto.
          econstructor(eauto).
        * destruct REF as [WREF INV]; clear INV.
          destruct WREF as [CONTRA | KREF].
          { apply @refine_state_in_user in CONTRA.
            apply @in_user_in_kernel in CONTRA.
            congruence.
          }
          { destruct KREF as [cst0 [kst [KREF [CSTEP KEXEC]]]].
            assert (KERNEL' := kernel_step KREF CSTEP KEXEC STEP KERNEL USER).
            left. assumption.
          }
      + destruct (in_user a) eqn:USER.
        * right. exists a; split; auto.
          econstructor(eauto).
        * destruct REF as [WREF INV]; clear INV.
          destruct WREF as [CONTRA | KREF].
          { apply @refine_state_in_user in CONTRA.
            apply @in_user_in_kernel in CONTRA.
            congruence.
          }
          { destruct KREF as [cst0 [kst [KREF [CSTEP KEXEC]]]].
            assert (KERNEL' := kernel_step KREF CSTEP KEXEC STEP KERNEL USER).
            destruct (IHcxs IN (ast :: axs0) a RTRACE' KERNEL')
              as [KERNEL'' | [cst'' [USER'' EXEC]]].
            - left; assumption.
            - right. exists cst''.
              split; auto.
              econstructor(eauto).
          }
    }
    { (*visible step*)
      destruct IN as [? | IN]; subst.
      + destruct (in_user cst') eqn:USER.
        * right. exists cst'. split; auto.
          econstructor(eauto).
        * destruct REF as [WREF INV]; clear INV.
          destruct WREF as [CONTRA | KREF].
          { apply @refine_state_in_user in CONTRA.
            apply @in_user_in_kernel in CONTRA.
            congruence.
          }
          { destruct KREF as [cst0 [kst [KREF [CSTEP KEXEC]]]].
            assert (KERNEL' := kernel_step KREF CSTEP KEXEC STEP KERNEL USER).
            left. assumption.
          }
      + destruct (in_user a) eqn:USER.
        * right. exists a; split; auto.
          econstructor(eauto).
        * destruct REF as [WREF INV]; clear INV.
          destruct WREF as [CONTRA | KREF].
          { apply @refine_state_in_user in CONTRA.
            apply @in_user_in_kernel in CONTRA.
            congruence.
          }
          { destruct KREF as [cst0 [kst [KREF [CSTEP KEXEC]]]].
            assert (KERNEL' := kernel_step KREF CSTEP KEXEC STEP KERNEL USER).
            destruct (IHcxs IN (ast' :: axs0) a RTRACE' KERNEL')
              as [KERNEL'' | [cst'' [USER'' EXEC]]].
            - left; assumption.
            - right. exists cst''.
              split; auto.
              econstructor(eauto).
          }
    }
    { (*attacker step - attacker not allowed in kernel mode*)
      inversion STEPA; subst.
      clear IHcxs RTRACE' RTRACE NSTEP CSTEPA MEQUIV REQUIV IN.
      unfold rules.word_lift, rules.is_user in INUSER.
      unfold in_kernel, Concrete.is_kernel_tag in KERNEL.
      rewrite rules.encode_kernel_tag in KERNEL. simpl in KERNEL.
      move/eqP:KERNEL=>KERNEL.
      rewrite KERNEL in INUSER.
      rewrite rules.decodeK in INUSER.
      inversion INUSER.
    }
Qed.

Lemma attacker_up_to ast ast' cst cst' axs cxs :
  Sym.all_attacker (ast :: ast' :: axs) ->
  Sym.all_stuck stable (ast :: ast' :: axs) ->
  Conc.step_a cst cst' /\ ~ Concrete.step ops masks cst cst' ->
  refine_traces cfi_refinementSC (ast :: ast' :: axs) (cst :: cst' :: cxs) ->
  Conc.all_attacker masks (cst :: cst' :: cxs) \/
  exists hd tl csi csj,
    cst :: cst' :: cxs = hd ++ csi :: csj :: tl /\
    Conc.all_attacker masks (hd ++ [csi]) /\
    Concrete.step _ masks csi csj /\ check csi csj = false /\
    ((exists asi, refine_traces cfi_refinementSC [asi] (csi :: csj :: tl)
                /\ exec (@Sym.step_a mt ids cfg) ast asi)
    \/ (exists asi asj atl,
          refine_traces cfi_refinementSC (asi :: asj :: atl) (csj :: tl) /\
          Sym.all_stuck stable (asi :: asj :: atl) /\
          exec (@Sym.step_a mt ids cfg) ast asi /\
          refine_state asi csi)).
Proof.
  intros ALLA ALLS CSTEP RTRACE.
  gdep ast'. gdep ast. gdep cst'. gdep cst. gdep axs.
  induction cxs as [|cst'' cxs]; simpl in *; intros.
  - inversion RTRACE
        as [? ? REF' | ? ? ? ? ? STEP CHECK REF REF' RTRACE'
            | ? ? ? ? ? ? STEP ASTEP REF REF' RTRACE'
            | ? ? ? ? ? ? NSTEP STEPA CSTEPA REF REF' RTRACE']; subst.
    + left.
      intros ? ? IN2;
        destruct IN2 as [[? ?] | CONTRA];
        [subst | destruct CONTRA].
      auto.
    + exfalso. simpl in *.
      assert (IN: In ast (ast :: ast' :: axs))
        by (simpl; auto).
      specialize (ALLS ast IN).
      eauto.
    + left. intros ? ? IN2.
      destruct IN2 as [[? ?] | CONTRA];
        [subst | destruct CONTRA].
      * simpl in *. auto.
  - inversion RTRACE
        as [? ? REF' | ? ? ? ? ? STEP CHECK REF REF' RTRACE'
            | ? ? ? ? ? ? STEP ASTEP REF REF' RTRACE'
            | ? ? ? ? ? ? NSTEP STEPA CSTEPA REF REF' RTRACE']; subst.
    + exfalso. simpl in STEP.
      destruct CSTEP as [? CONTRA].
      destruct (CONTRA STEP).
    + exfalso. simpl in *.
      assert (IN: In ast (ast :: ast' :: axs))
        by (simpl; auto).
      specialize (ALLS ast IN).
      eauto.
    + destruct axs as [|ast'' axs].
      * inversion RTRACE'
          as [? ? REF''| | | ]; subst.
       { simpl in *.
         right.
         exists [cst]; exists cxs; exists cst'; exists cst''.
         split; auto.
         split. intros ? ? IN2.
         destruct IN2 as [[? ?] | CONTRA];
           [subst | destruct CONTRA].
         split; auto.
         split; auto.
         split; auto.
         left.
         exists ast'. split; auto.
         econstructor(eauto).
       }
      * inversion RTRACE'; subst.
        { right.
          exists [cst]; exists cxs; exists cst'; exists cst''.
          split; auto.
          split.
          intros ? ? IN2;
            destruct IN2 as [[? ?] | CONTRA]; [subst | destruct CONTRA].
          auto.
          split. assumption.
          split. assumption.
          right.
          eexists; eexists; eexists; split; eauto.
          split.
          apply Sym.all_stuck_red in ALLS.
          by auto.
          by econstructor(eauto).
        }
        { assert (IN: In ast' (ast :: ast' :: ast'' :: axs))
            by (simpl; auto).
          specialize (ALLS ast' IN).
          simpl in H6.
          exfalso.
          eauto.
        }
        {
          apply Sym.all_attacker_red in ALLA.
          apply Sym.all_stuck_red in ALLS.
          assert (STEP: Conc.step_a cst' cst'' /\ ~ Concrete.step ops masks cst' cst'')
            by auto.
          specialize (IHcxs axs cst' cst'' STEP ast' ast'' ALLA ALLS RTRACE').
          destruct IHcxs as [ALLA' | IH].
          - (*all attacker*)
            left.
            intros csi csj IN2.
            destruct IN2 as [[? ?] | IN2]; subst.
            + simpl in *. auto.
            + auto.
          - destruct IH
              as [chd [ctl [csi [csj [CLST [ALLA' [UCSTEP [CHECK IH]]]]]]]].
            destruct IH as [IH | IH].
            { destruct IH as [asi [RTRACE'' EXEC]].
              right.
              rewrite CLST.
              exists (cst :: chd); exists ctl; exists csi; exists csj.
              split; auto.
              split.
              { intros ? ? IN2.
                destruct chd.
                - destruct IN2 as [[? ?] | CONTRA];
                [subst | destruct CONTRA].
                  inv CLST.
                  assumption.
                - inv CLST.
                  destruct IN2 as [[? ?] | IN2]; subst.
                + auto.
                + apply ALLA' in IN2.
                  assumption.
              }
              { split. assumption.
                split; [assumption | idtac].
                left. exists asi. split; auto.
                econstructor(eauto).
              }
            }
            { destruct IH as [asi [asj [atl [RTRACE'' [STUCK'' [EXEC'' REF'']]]]]].
              right.
              rewrite CLST.
              exists (cst :: chd); exists ctl; exists csi; exists csj.
              split; auto.
              split.
              { intros ? ? IN2.
                destruct chd.
                - destruct IN2 as [[? ?] | CONTRA];
                [subst | destruct CONTRA].
                  inv CLST.
                  assumption.
                - inv CLST.
                  destruct IN2 as [[? ?] | IN2]; subst.
                + auto.
                + apply ALLA' in IN2.
                  assumption.
              }
              { split. assumption.
                split; [assumption | idtac].
                right. eexists; eexists; eexists; split;  eauto.
              }
            }
        }
Qed.

Lemma all_attacker_implies_all_user cst cst' cxs :
  Conc.all_attacker masks (cst :: cst' :: cxs) ->
  forallb in_user (cst :: cst' :: cxs).
Proof.
  intro ALLA.
  apply forallb_forall.
  intros x IN.
  gdep cst'. gdep cst.
  induction cxs; intros.
  - destruct IN as [? | IN]; subst.
    + assert (IN2 : In2 x cst' [x;cst'])
        by (simpl; auto).
      apply ALLA in IN2.
      destruct IN2 as [STEPA ?].
      inv STEPA; auto.
    + destruct IN as [? | CONTRA];
      [subst | destruct CONTRA].
      assert (IN2 : In2 cst x [cst;x])
        by (simpl; auto).
      destruct (ALLA _ _ IN2) as [STEPA ?].
      inv STEPA; auto.
  - destruct IN as [? | IN]; subst.
    + assert (IN2: In2 x cst' (x :: cst' :: a :: cxs))
        by (simpl; auto).
      destruct (ALLA _ _ IN2) as [STEPA ?].
      inv STEPA; auto.
    + apply Conc.all_attacker_red in ALLA.
      eauto.
Qed.

Lemma all_attacker_implies_all_user' cst cst' cxs :
  Conc.all_attacker masks (cst :: cxs ++ [cst']) ->
  forallb in_user (cst :: cxs ++ [cst']).
Proof.
  intro ALLA.
  apply forallb_forall.
  intros x IN.
  gdep cst'. gdep cst.
  induction cxs; intros.
  - destruct IN as [? | IN]; subst.
    + assert (IN2 : In2 x cst' [x;cst'])
        by (simpl; auto).
      apply ALLA in IN2.
      destruct IN2 as [STEPA ?].
      inv STEPA; auto.
    + destruct IN as [? | CONTRA];
      [subst | destruct CONTRA].
      assert (IN2 : In2 cst x [cst;x])
        by (simpl; auto).
      destruct (ALLA _ _ IN2) as [STEPA ?].
      inv STEPA; auto.
  - destruct IN as [? | IN]; subst.
    + assert (IN2: In2 x a (x :: a :: cxs ++ [cst']))
        by (simpl; auto).
      simpl in ALLA.
      apply ALLA in IN2.
      destruct IN2 as [STEPA ?].
      inv STEPA; auto.
    + simpl in ALLA.
      apply Conc.all_attacker_red in ALLA.
      specialize (IHcxs _ _ ALLA IN).
      assumption.
Qed.

Lemma user_into_kernel_wrapped sst cst cst' :
  in_user cst = true ->
  refine_state sst cst ->
  Concrete.step ops masks cst cst' ->
  in_user cst' = false -> in_kernel cst' = true.
Proof.
  intros USER REF STEP NUSER.
  destruct REF as [REF ?].
  destruct REF as [WREF | CONTRA].
  - eauto using user_into_kernel.
  - destruct CONTRA as [? [? [? [? KEXEC]]]].
    apply restricted_exec_snd in KEXEC.
    apply @in_user_in_kernel in USER.
    by congruence.
Qed.

Lemma violation_implies_kexec sst cst cst' umvec sxs cxs :
  Sym.violation stable sst ->
  build_ivec stable sst = Some umvec ->
  in_user cst = true ->
  check cst cst' = false ->
  Concrete.step ops masks cst cst' ->
  refine_state sst cst ->
  refine_traces cfi_refinementSC (sst :: sxs) (cst' :: cxs) ->
  forallb in_kernel (cst' :: cxs).
Proof.
  intros VIOLATION UMVEC USER CHECK STEP REF RTRACE.
  apply andb_false_iff in CHECK.
  destruct CHECK as [CONTRA | NUSER'];
    [congruence | idtac].
  assert (UHANDLER := Sym.is_violation_implies_stop stable sst VIOLATION UMVEC).
  assert (KERNEL := user_into_kernel_wrapped USER REF STEP NUSER').
  destruct (umvec_implies_cmvec USER REF UMVEC) as [cmvec CMVEC].
  assert (KHANDLER := refine_ivec_fail _ UHANDLER).
  assert (EQ := unique_cmvec USER REF UMVEC CMVEC).
  rewrite EQ in KHANDLER. clear EQ.
  destruct (fault_steps_at_kernel USER REF STEP CMVEC KHANDLER)
    as [cmem' [STORE EQST]].
  apply forallb_forall.
  intros kst IN.
  destruct IN as [? | IN]; [subst kst; auto | idtac].
  destruct (refine_traces_kexec kst RTRACE KERNEL IN)
    as [KERNEL' | [cst'' [USER'' EXEC]]].
  * assumption.
  * (*the case where one user step was in the trace contradicts*)
    destruct REF as [REF ?].
    destruct REF as [REF | CONTRA].
    { destruct REF.
      destruct (in_kernel cst'') eqn:KERNEL''.
      - apply @in_user_in_kernel in USER''. by congruence.
      - destruct cst as [cmemt cregt cachet [cpct ctpct] epct].
        destruct sst as [smemt sregt [spct tpct] intt].
        simpl in EQST. inversion ES.
        subst smemt sregt spct tpct intt.
        inversion EC.
        subst cmemt cregt cachet cpct epct.
        assert (KEXEC:=
                  @handler_correct_disallowed_case mt ops sp (fun _ => e) ki
                                                   stable _ cmem
                                                   cmem' cmvec cregs
                                                   cache (pc@ctpct) int cst''
                                                   KINV KHANDLER STORE KERNEL'').
        rewrite <- EQST in *.
        destruct (KEXEC EXEC).
    }
    { (*refinement contradictory case*)
      destruct CONTRA as [? [? [? [? KEXEC]]]].
      apply restricted_exec_snd in KEXEC.
      apply @in_user_in_kernel in USER.
        by congruence.
    }
Qed.

Lemma no_umvec_implies_kexec sst cst cst' sxs cxs :
  Sym.violation stable sst ->
  build_ivec stable sst = None ->
  in_user cst = true ->
  check cst cst' = false ->
  Concrete.step ops masks cst cst' ->
  refine_state sst cst ->
  refine_traces cfi_refinementSC (sst :: sxs) (cst' :: cxs) ->
  forallb in_kernel (cst' :: cxs).
Proof.
  intros VIOLATION UMVEC USER CHECK STEP REF RTRACES.
  destruct (build_cmvec mt cst) as [cmvec|] eqn:CMVEC.
      { (*case the cmvec for cst exists*)
        assert (KHANDLER := no_user_access_implies_halt USER REF UMVEC CMVEC).
        (*factor this in a seperate lemma*)
        destruct (fault_steps_at_kernel USER REF STEP CMVEC KHANDLER)
        as [cmem' [STORE EQST]].
        (*kernel tail proof*)
        apply forallb_forall.
        intros kst IN.
        apply andb_false_iff in CHECK.
        destruct CHECK as [CONTRA | NUSER']; [congruence | idtac].
        assert (KERNEL := user_into_kernel_wrapped USER REF STEP NUSER').
        destruct IN as [? | IN]; [subst kst; auto | idtac].
        destruct (refine_traces_kexec kst RTRACES KERNEL IN)
          as [KERNEL' | [cst'' [USER'' EXEC]]].
        * assumption.
        * (*the case where one user step was in the trace contradicts*)
          destruct REF as [REF ?].
            destruct REF as [REF | CONTRA].
            { destruct REF.
              destruct (in_kernel cst'') eqn:KERNEL''.
              - apply @in_user_in_kernel in USER''. by congruence.
              - destruct cst as [cmemt cregt cachet [cpct ctpct] epct].
                destruct sst as [smemt sregt [spct tpct] intt].
                simpl in EQST. inversion ES.
                subst smemt sregt spct tpct intt.
                inversion EC.
                subst cmemt cregt cachet cpct epct.
                assert (KEXEC:=
                      @handler_correct_disallowed_case mt ops sp (fun _ => e) ki
                                                       stable _ cmem
                                                       cmem' cmvec cregs
                                                       cache (pc@ctpct) int cst''
                                                       KINV KHANDLER STORE KERNEL'').
                rewrite <- EQST in *.
                destruct (KEXEC EXEC).
            }
            { (*refinement contradictory case*)
              destruct CONTRA as [? [? [? [? KEXEC]]]].
              apply restricted_exec_snd in KEXEC.
              apply @in_user_in_kernel in USER.
              by congruence.
            }
      }
      { (*case the cmvec does not exist*)
        exfalso.
        apply step_build_cmvec in STEP.
        destruct STEP.
        congruence. }
Qed.

Theorem cfg_true_equiv ssi ssj csi csj :
  refine_state ssi csi ->
  refine_state ssj csj ->
  Symbolic.step stable ssi ssj ->
  Sym.ssucc stable ssi ssj = true ->
  Concrete.step ops masks csi csj ->
  Conc.csucc cfg csi csj = true.
Proof.
  intros.
  destruct H as [REF INV].
  destruct REF as [UREFI | KREFI].
  - destruct H0 as [REF' INV'].
    destruct REF' as [UREFJ | KREFJ].
    + move: (refine_state_in_user UREFI) (refine_state_in_user UREFJ) => USERI USERJ.
      destruct UREFI as [smemi sregi inti cmemi cregi cachei epci pci tpci
                         ASI CSI REFM REFR CACHE MVE WF KI],
               UREFJ as [smemj sregj intj cmemj cregj cachej epcj pcj tpcj
                         ASJ CSJ REFM' REFR' C3 C5 C6 C7].
      assert (NKERNEL : in_kernel csi || in_kernel csj = false).
      { apply @in_user_in_kernel in USERI.
        apply @in_user_in_kernel in USERJ.
        apply orb_false_iff. split; subst; auto.
      }
      unfold Conc.csucc.
      rewrite NKERNEL CSI CSJ /=.
      unfold Sym.ssucc in H2.
      rewrite ASI ASJ /= in H2.
      destruct (get smemi pci) as [[v tg]|] eqn:GET.
      * rewrite GET in H2. assert (REFMI := REFM pci v tg).
        apply REFMI in GET.
        destruct tg as [[src|]|].
        { simpl in GET. rewrite GET /= rules.decodeK.
          destruct (decode_instr v) eqn:INST.
          - destruct i eqn:OP; try assumption. (*TODO: fix jmp/jal copy paste*)
            { (*jmp*)
              destruct (get smemi pcj) as [[v' tg]|] eqn:GET'.
              - assert (REFMJ := REFM pcj v' tg).
                rewrite GET' in H2.
                apply REFMJ in GET'.
                clear REFMJ.
                rewrite GET' /= rules.decodeK.
                  by assumption.
              - rewrite GET' in H2.
                destruct (Symbolic.get_syscall stable pcj) eqn:GETCALL.
                + rewrite GETCALL in H2.
                  unfold wf_entry_points in WF.
                  specialize (WF pcj (Symbolic.entry_tag s)).
                  assert (ECALL : exists sc : Symbolic.syscall mt,
                                    Symbolic.get_syscall stable pcj = Some sc /\
                                    Symbolic.entry_tag sc = Symbolic.entry_tag s)
                    by (eexists; eauto).
                  apply WF in ECALL.
                  case: (get cmemi pcj) ECALL => [[v' tg]|] ECALL //.
                  apply andb_true_iff in ECALL.
                  destruct ECALL as [ISNOP ETAG].
                  simpl.
                  move/eqP:ETAG => ETAG.
                  rewrite ETAG /= rules.decodeK.
                  destruct (Symbolic.entry_tag s) as [[?|]|] eqn:ETAG';
                    rewrite ETAG' in H2; try discriminate.
                  apply andb_true_iff.
                  by auto.
                + rewrite GETCALL in H2. by discriminate.
            }
            { (*jal*)
              destruct (get smemi pcj) as [[v' tg]|] eqn:GET'.
              - assert (REFMJ := REFM pcj v' tg).
                rewrite GET' in H2.
                apply REFMJ in GET'.
                clear REFMJ.
                rewrite GET' /= rules.decodeK.
                  by assumption.
              - rewrite GET' in H2.
                destruct (Symbolic.get_syscall stable pcj) eqn:GETCALL.
                + rewrite GETCALL in H2.
                  unfold wf_entry_points in WF.
                  specialize (WF pcj (Symbolic.entry_tag s)).
                  assert (ECALL : exists sc : Symbolic.syscall mt,
                                    Symbolic.get_syscall stable pcj = Some sc /\
                                    Symbolic.entry_tag sc = Symbolic.entry_tag s)
                    by (eexists; eauto).
                  apply WF in ECALL.
                  case: (get cmemi pcj) ECALL => [[v' tg]|] ECALL //.
                  apply andb_true_iff in ECALL.
                  destruct ECALL as [ISNOP ETAG].
                  simpl.
                  move/eqP:ETAG => ETAG.
                  rewrite ETAG /= rules.decodeK.
                  destruct (Symbolic.entry_tag s) as [[?|]|] eqn:ETAG';
                    rewrite ETAG' in H2; try discriminate.
                  apply andb_true_iff.
                  by auto.
                + rewrite GETCALL in H2. by discriminate.
            }
          - by discriminate.
        }
        {  simpl in GET. rewrite GET /= rules.decodeK.
           destruct (decode_instr v) eqn:INST.
           - destruct i eqn:OP; by assumption.
           - by discriminate.
        }
        { by discriminate. }
        { rewrite GET in H2.
          destruct (get cmemi pci) as [[v ctg]|] eqn:GET'.
          - simpl.
            subst csi csj.
            assert (CONTRA := fun CACHE GET' =>
                                valid_initial_user_instr_tags (v := v) (ti := ctg) CACHE USERI USERJ H3 GET').
            specialize (CONTRA CACHE GET').
            destruct (rules.decode ctg) as [[t | | ]|] eqn:DEC; try solve [inversion CONTRA].
            apply rules.encodeK in DEC.
            rewrite <- DEC in GET'.
            simpl in GET'. apply REFM in GET'. subst.
            rewrite GET' in GET. discriminate.
          - admit. (*inversion H3;
            inv ST; simpl in *; try congruence.*)
          - admit.
          - admit.
          - admit.
        }
    + destruct KREFJ as [? [? [? [? KEXEC]]]].
      apply restricted_exec_snd in KEXEC.
      unfold Conc.csucc. rewrite KEXEC.
      simpl. rewrite orb_true_r. reflexivity.
  - destruct KREFI as [? [? [? [? KEXEC]]]].
    apply restricted_exec_snd in KEXEC.
    unfold Conc.csucc. rewrite KEXEC.
    by reflexivity.
Qed.

Theorem cfg_false_equiv ssi ssj csi csj :
  refine_state ssi csi ->
  refine_state ssj csj ->
  Sym.ssucc stable ssi ssj = false ->
  check csi csj = true ->
  Concrete.step ops masks csi csj ->
  Conc.csucc cfg csi csj = false.
Proof.
  intros.
  destruct H as [REF INV], H0 as [REF' INV']. clear INV'.
  unfold check in H2.
  apply andb_true_iff in H2.
  destruct H2 as [USER USER'].
  destruct REF as [REF | CONTRA].
  - destruct REF' as [REF' | CONTRA'].
    + apply @in_user_in_kernel in USER.
      apply @in_user_in_kernel in USER'.
      unfold Conc.csucc. rewrite USER USER'.
      simpl.
      move: (refine_state_in_user REF) (refine_state_in_user REF') => USERT USERT'.
      destruct REF as [smem sreg int cmem creg cache epc pc tpc
                       ASI CSI REFM REFR CACHE MVEC WF KI],
               REF' as [smem' sreg' int' cmem' creg' cache' epc' pc' tpc'
                        ASJ CSJ REFM' REFR' C3 C5 C6 C7].
      simpl. subst.
      unfold Sym.ssucc in H1.
      simpl in H1.
      destruct (get smem pc) eqn:GET.
      { destruct a as [v utg].
        destruct utg.
        - rewrite GET in H1.
          apply REFM in GET.
          rewrite GET.
          simpl.
          rewrite rules.decodeK.
          destruct (decode_instr v).
          + (*is instruction*)
            destruct i eqn:OP; destruct o; try trivial.
            destruct (get smem pc') as [[v' [[dst|]|]]|] eqn:SGET'.
            * rewrite SGET' in H1.
              apply REFM in SGET'.
              rewrite SGET' /= rules.decodeK.
              by assumption.
            * apply REFM in SGET'.
              rewrite SGET' /= rules.decodeK.
              by reflexivity.
            * apply REFM in SGET'.
              rewrite SGET' /= rules.decodeK.
              by reflexivity.
            * rewrite SGET' in H1.
              destruct (get cmem pc') as [[cv' ctg]|] eqn:GET'.
              { simpl.
                destruct (rules.decode ctg) eqn:DEC.
                - destruct t.
                  apply rules.encodeK in DEC. rewrite <- DEC in GET'.
                  apply REFM in GET'. rewrite GET' in SGET'.
                  by discriminate.
                - by reflexivity.
                - unfold wf_entry_points in WF.
                  destruct (Symbolic.get_syscall stable pc') eqn:GETCALL.
                  + rewrite GETCALL in H1.
                    specialize (WF pc' (Symbolic.entry_tag s0)).
                    assert (ECALL: (exists sc : Symbolic.syscall mt,
                               Symbolic.get_syscall stable pc' = Some sc /\
                               Symbolic.entry_tag sc = Symbolic.entry_tag s0))
                      by (eexists; eauto).
                    apply WF in ECALL.
                    rewrite GET' in ECALL.
                    apply andb_true_iff in ECALL. destruct ECALL as [ISNOP CTG].
                    move/eqP:CTG => CTG.
                    rewrite CTG in DEC.
                    rewrite rules.decodeK in DEC. inv DEC.
                    destruct (Symbolic.entry_tag s0) as [[?|]|] eqn:ETAG; rewrite ETAG in H1;
                    auto.
                    apply andb_false_iff. right.
                    by assumption.
                  + clear H1.
                    destruct sct as [[?|]|] eqn:TG.
                    * apply andb_false_iff. left.
                      destruct (is_nop cv') eqn:NOP.
                      { exfalso.
                        apply rules.encodeK in DEC.
                        specialize (WF pc' (INSTR (Some s0))).
                        assert (CONTRA: match get cmem pc' with
                                          | Some i@it =>
                                            is_nop i && (it == rules.encode (rules.ENTRY (INSTR (Some s0))))
                                          | None => false
                                        end = true).
                        { rewrite GET'. apply andb_true_iff. rewrite <- DEC.
                          split; auto. by rewrite eqxx. }
                        apply WF in CONTRA. destruct CONTRA as [? [CONTRA ?]].
                        rewrite CONTRA in GETCALL. by discriminate.
                      }
                      { by reflexivity. }
                    * by reflexivity.
                    * by reflexivity.
                    * by reflexivity.
              }
              { by reflexivity. }
              (*copy paste from above, TODO: fix*)
              destruct (get smem pc') as [[v' [[dst|]|]]|] eqn:SGET'.
            * rewrite SGET' in H1.
              apply REFM in SGET'.
              rewrite SGET' /= rules.decodeK.
              by assumption.
            * apply REFM in SGET'.
              rewrite SGET' /= rules.decodeK.
              by reflexivity.
            * apply REFM in SGET'.
              rewrite SGET' /= rules.decodeK.
              by reflexivity.
            * rewrite SGET' in H1.
              destruct (get cmem pc') as [[cv' ctg]|] eqn:GET'.
              { simpl.
                destruct (rules.decode ctg) eqn:DEC.
                - destruct t.
                  apply rules.encodeK in DEC. rewrite <- DEC in GET'.
                  apply REFM in GET'. rewrite GET' in SGET'.
                  by discriminate.
                - by reflexivity.
                - unfold wf_entry_points in WF.
                  destruct (Symbolic.get_syscall stable pc') eqn:GETCALL.
                  + rewrite GETCALL in H1.
                    specialize (WF pc' (Symbolic.entry_tag s0)).
                    assert (ECALL: (exists sc : Symbolic.syscall mt,
                               Symbolic.get_syscall stable pc' = Some sc /\
                               Symbolic.entry_tag sc = Symbolic.entry_tag s0))
                      by (eexists; eauto).
                    apply WF in ECALL.
                    rewrite GET' in ECALL.
                    apply andb_true_iff in ECALL. destruct ECALL as [ISNOP CTG].
                    move/eqP:CTG => CTG.
                    rewrite CTG in DEC.
                    rewrite rules.decodeK in DEC. inv DEC.
                    destruct (Symbolic.entry_tag s0) as [[?|]|] eqn:ETAG; rewrite ETAG in H1;
                    auto.
                    apply andb_false_iff. right.
                    by assumption.
                  + clear H1.
                    destruct sct as [[?|]|] eqn:TG.
                    * apply andb_false_iff. left.
                      destruct (is_nop cv') eqn:NOP.
                      { exfalso.
                        apply rules.encodeK in DEC.
                        specialize (WF pc' (INSTR (Some s0))).
                        assert (CONTRA: match get cmem pc' with
                                          | Some i@it =>
                                            is_nop i && (it == rules.encode (rules.ENTRY (INSTR (Some s0))))
                                          | None => false
                                        end = true).
                        { rewrite GET'. apply andb_true_iff. rewrite <- DEC.
                          split; auto. rewrite eqxx. by reflexivity. }
                        apply WF in CONTRA. destruct CONTRA as [? [CONTRA ?]].
                        rewrite CONTRA in GETCALL. by discriminate.
                      }
                      { by reflexivity. }
                    * by reflexivity.
                    * by reflexivity.
                    * by reflexivity.
              }
              { by reflexivity. }
          + by assumption.
        - apply REFM in GET. rewrite GET.
          simpl. rewrite rules.decodeK. reflexivity.
      }
      { simpl. destruct (get cmem pc) as [[v ctg]|] eqn:GET'; trivial. simpl.
        destruct (rules.decode ctg) as [[t | | ]| ] eqn:DECTG; trivial.
        apply rules.encodeK in DECTG.
        rewrite <- DECTG in GET'.
        apply REFM in GET'.
        rewrite GET in GET'; discriminate.
      }
    + destruct CONTRA' as [? [? [? [? KEXEC]]]].
      apply restricted_exec_snd in KEXEC.
      apply @in_user_in_kernel in USER'. rewrite KEXEC in USER'.
      discriminate.
  - destruct CONTRA as [? [? [? [? KEXEC]]]].
      apply restricted_exec_snd in KEXEC.
      apply @in_user_in_kernel in USER. rewrite KEXEC in USER.
      discriminate.
Qed.

Import ListNotations.

Open Scope list_scope.
Close Scope seq_scope.

Program Instance cfi_refinementAS_specs :
  machine_refinement_specs cfi_refinementSC.
Next Obligation. (*step or no step*)
  by case: (stepP' masks mt cst cst') => [H | H]; auto.
Qed.
Next Obligation. (*initial states*)
  unfold Conc.cinitial in H.
  destruct H as [ast [INIT REF]].
  eexists; split; [eassumption | split].
  - left; assumption.
  - destruct INIT as [? INV]; by assumption.
Qed.
Next Obligation.
  unfold check in H1.
  apply andb_false_iff in H1.
  destruct H1 as [CONTRA | NUSER].
  - destruct H as [REF INV].
    move: REF => [/(@refine_state_in_user _) INUSER | REF].
    + rewrite INUSER in CONTRA.
        by discriminate.
    + destruct REF as [? [? [? [? KEXEC]]]].
      apply restricted_exec_snd in KEXEC.
      unfold Conc.csucc. rewrite KEXEC.
      by reflexivity.
  - destruct H as [REF INV].
    destruct REF as [REF | REF].
    + assert (KERNEL' := user_into_kernel REF H0 NUSER).
      unfold Conc.csucc. rewrite KERNEL'.
      rewrite orb_true_r. reflexivity.
    + destruct REF as [? [? [? [? KEXEC]]]].
      apply restricted_exec_snd in KEXEC.
      unfold Conc.csucc. rewrite KEXEC.
      by reflexivity.
Qed.
Next Obligation. (*symbolic-concrete cfg relation*)
  destruct (Sym.ssucc stable asi asj) eqn:SUCC.
  - eauto using cfg_true_equiv.
  - eauto using cfg_false_equiv.
Qed.
Next Obligation. (*symbolic no attacker on violation*)
  destruct H as [? INV].
  eauto using attacker_no_v.
Qed.
Next Obligation. (*symbolic stopping implies concrete stopping*)
Proof.
  rename H into CHECK.
  rename H0 into SUCC.
  rename H1 into SSTEP.
  rename H2 into REFI.
  rename H3 into RTRACES.
  rename H4 into SSTOP.
  unfold Sym.stopping in SSTOP.
  unfold Conc.stopping.
  unfold check in CHECK.
  apply andb_true_iff in CHECK.
  destruct CHECK as [USERI USERJ].
  destruct REFI as [WREFI INVI].
  inversion RTRACES
    as [? ? REF' | ? ? ? ? ? STEP CHECK REFJ REF' RTRACE'
        | ? ? ? ? ? ? STEP ASTEP REFJ REF' RTRACE'
        | ? ? ? ? ? ? NSTEP STEPA SSTEPA REF REF' RTRACE'];
    subst; simpl in *.
  - (*case trace is a singleton*)
    left.
    split; [intros ? ? IN2; destruct IN2 | idtac].
    apply andb_true_iff. auto.
  - (*case an invisible step is taken*)
    destruct (Sym.succ_false_implies_violation INVI SUCC SSTEP)
      as [CONTRA | VIOLATION]; first done.
    right.
    exists [csj]; exists (cst' :: cxs0).
    split; auto.
    split.
    intros ? ? CONTRA; destruct CONTRA.
    split.
    apply forallb_forall. intros ? IN.
    destruct IN as [? | CONTRA];
      [subst | destruct CONTRA].
      by auto.
    destruct (build_ivec stable asj) as [umvec|] eqn:UMVEC.
    + (*case the umvec for asj exists*)
        by eauto using violation_implies_kexec.
    + (*case where the umvec for asj does not exist*)
        by eauto using no_umvec_implies_kexec.
  - (*case of normal steps*)
    exfalso.
    destruct SSTOP as [? ALLS].
    assert (IN: In asj (asj :: ast' :: axs0))
      by (simpl; auto).
    apply ALLS in IN.
    by eauto.
  - (*case of attacker steps*)
     destruct (Sym.succ_false_implies_violation INVI SUCC SSTEP)
      as [CONTRA | VIOLATION]; first done.
     destruct SSTOP as [ALLA ALLS].
     assert (STEPA' : Conc.step_a csj cst' /\ ~ Concrete.step ops masks csj cst')
       by auto.
     clear STEPA NSTEP.
     destruct (attacker_up_to ALLA ALLS STEPA' RTRACES) as [ALLA' | IH].
     + left. split. by assumption.
       apply all_attacker_implies_all_user in ALLA'. by assumption.
     + (*inductive cases*)
       destruct IH
         as [chd [ctl [csi' [csj' [CLST [ALLA' [CSTEP [CHECK IH']]]]]]]].
       clear RTRACES RTRACE'.
       destruct IH' as [[asj' [RTRACE AEXEC]]| [asi' [asj' [atl RTRACE]]]].
       { (*non-contradictory case, we took some attacker steps at first*)
         assert (VIOLATION' := Sym.violation_preserved_by_exec_a _ VIOLATION AEXEC).
         clear VIOLATION.
         right.
         rewrite CLST.
         exists (chd++[csi']); exists (csj'::ctl).
         split. rewrite <- app_assoc. by reflexivity.
         split. by assumption.
         split.
         { apply forallb_forall.
           destruct chd.
           - intros ? IN.
             destruct IN as [? | IN]; subst.
             + inv CLST.
               by auto.
             + destruct IN.
           - intros x IN.
             apply all_attacker_implies_all_user' in ALLA'.
             assert (ALLU: forall x, In x ((s :: chd) ++ [csi']) -> in_user x)
               by (apply forallb_forall; auto).
             specialize (ALLU _ IN). by auto.
         }
         { inversion RTRACE as [| ? ? ? ? ? STEP' CHECK' REFI' REFJ' RTRACE' | |];
           subst.
           assert (USERI' : in_user csi' = true).
           { destruct chd.
             - inv CLST.
                 by assumption.
             - apply all_attacker_implies_all_user' in ALLA'.
               assert (IN: In csi' (s :: chd ++ [csi']))
                 by (eauto using list_utils.in_last).
               assert (ALLU: forall x, In x ((s :: chd) ++ [csi']) -> in_user x)
               by (apply forallb_forall; auto).
             specialize (ALLU _ IN). by auto.
           }
           destruct (build_ivec stable asj') as [umvec|] eqn:UMVEC.
           - (*case the umvec exists*)
             eauto using violation_implies_kexec.
           - (*case the umvec does not exist*)
             eauto using no_umvec_implies_kexec.
         }
       }
       { (*contradictory case, mixed attacker steps and unchecked ones*)
         exfalso.
         destruct RTRACE as [RTRACE [ALLS' [AEXEC REFN]]].
         destruct (refine_traces_astep RTRACE)
           as [csn [csn' [IN2 [SSTEPN | [SSTEPAN STEPAN]]]]].
         * assert (IN: In asi' (asi' :: asj' :: atl))
             by (simpl; auto).
           apply ALLS' in IN. by eauto.
           assert (VIOLATION' := Sym.violation_preserved_by_exec_a _ VIOLATION AEXEC).
           clear VIOLATION.
           assert (USERI' : in_user csi' = true).
           { destruct chd.
             - inv CLST.
               by auto.
             - apply all_attacker_implies_all_user' in ALLA'.
               assert (ALLU : forall x, In x (s :: chd ++ [csi']) ->
                                        in_user x = true)
                 by (apply forallb_forall; auto).
               assert (IN: In csi' (s :: chd ++ [csi']))
                 by (eauto using list_utils.in_last).
               by auto.
           }
           assert (USERN: in_user csn = true)
             by (inv STEPAN; auto).
           destruct ctl; [by inversion RTRACE |idtac].
           destruct (build_ivec stable asi') as [umvec|] eqn:UMVEC.
            - (*case the umvec exists*)
             assert (KERNEL := violation_implies_kexec VIOLATION' UMVEC USERI'
                                                       CHECK CSTEP REFN RTRACE).
             apply In2_implies_In in IN2.
             assert (KERNEL' : forall x, In x (csj' :: s :: ctl) -> in_kernel x)
               by (apply forallb_forall; auto).
             apply KERNEL' in IN2.
             apply @in_user_in_kernel in USERN.
             rewrite IN2 in USERN.
             by discriminate.
           - (*case the umvec does not exist*)
             assert (KERNEL := no_umvec_implies_kexec VIOLATION' UMVEC USERI'
                                                       CHECK CSTEP REFN RTRACE).
             apply In2_implies_In in IN2.
             assert (KERNEL' : forall x, In x (csj' :: s :: ctl) -> in_kernel x)
               by (apply forallb_forall; auto).
             apply KERNEL' in IN2.
             apply @in_user_in_kernel in USERN.
             rewrite IN2 in USERN.
             by discriminate.
       }
Qed.

End Refinement.
