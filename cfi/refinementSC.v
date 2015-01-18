Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ord word partmap.

Require Import lib.utils lib.partmap_utils.
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
Require Import symbolic.backward.
Require Import symbolic.forward.
Require Import symbolic.refinement_common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Refinement.

Context {mt : machine_types}
        {ops : machine_ops mt}
        {opss : machine_ops_spec ops}
        {ids : @classes.cfi_id mt}
        {e : rules.fencodable mt rules.cfi_tags}.

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

(*TODO: Remove this hypothesis, as soon as we get kinds for tags*)
Hypothesis syscall_preserves_register_tags :
  forall sc st st',
    Sym.registers_tagged (cfg:=cfg) (Symbolic.regs st) ->
    Symbolic.sem sc st = Some st' ->
    Sym.registers_tagged (Symbolic.regs st').

Hypothesis syscall_preserves_jump_tags :
  forall sc st st',
    Sym.jumps_tagged (cfg:=cfg) (Symbolic.mem st) ->
    Symbolic.sem sc st = Some st' ->
    Sym.jumps_tagged (Symbolic.mem st').

Hypothesis syscall_preserves_jal_tags :
  forall sc st st',
    Sym.jals_tagged (cfg:=cfg) (Symbolic.mem st) ->
    Symbolic.sem sc st = Some st' ->
    Sym.jals_tagged (Symbolic.mem st').

Definition refine_state_no_inv (sst : Symbolic.state mt) (cst : Concrete.state mt) :=
  @refine_state_weak mt ops sp _ ki stable sst cst.

Definition refine_state (sst : Symbolic.state mt) (cst : Concrete.state mt) :=
  @refine_state_weak mt ops sp _ ki stable sst cst /\
  Sym.invariants stable sst.

Definition is_user k (x : atom (mword mt) (mword mt)) :=
  oapp (fun t => rules.is_user t) false (@rules.fdecode _ _ e k (common.tag x)).

Definition coerce k (x : atom (mword mt) (mword mt)) : atom (mword mt) (cfi_tag) :=
  match rules.fdecode k (common.tag x) with
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
  exists (mapm (coerce Symbolic.M) (filterm (is_user Symbolic.M) cmem')).
  split.
  { (*refinement proof*)
    split.
    { move=> addr v ct t /= DEC CGET.
      rewrite getm_map /= getm_filter /=.
      by rewrite CGET /is_user /= DEC /= /coerce DEC. }
    { move=> addr v t /=.
      rewrite getm_map /= getm_filter /=.
      case CGET: (getm cmem' addr) => [[cv ctg]|] //=.
      rewrite /is_user /=.
      case DEC: (rules.fdecode _ _) => [[t'|]|] //=.
      rewrite /coerce /= DEC. move=> [? ?]. subst cv t'.
      eauto. } }
  { (*equiv proof*)
    unfold Sym.equiv, pointwise.
    intro addr.
    unfold Conc.equiv in EQUIV. unfold pointwise in EQUIV.
    specialize (EQUIV addr). simpl.
    destruct (getm smem addr) eqn:SGET; simpl in SGET; rewrite SGET.
    - destruct a as [v utg].
      unfold refinement_common.refine_memory in REF.
      have [ctg DEC CGET] := proj2 REF addr v utg SGET.
      rewrite CGET in EQUIV.
      destruct (getm cmem' addr) eqn:CGET'.
      + destruct a as [v' ctg'].
        destruct EQUIV
          as [v0 v'' ct ut ct' ut' EQ1 DEC1 EQ2 DEC2 SEQUIV|NEQ EQ]; subst.
        * inv EQ1. inv EQ2.
          rewrite getm_map /= getm_filter /= CGET' /=
                  /is_user /= DEC2 /= /coerce /= DEC2.
          rewrite /= DEC1 in DEC.
          move: DEC => [?]. by subst.
        * inv EQ. simpl in NEQ.
          suff: False by [].
          apply: NEQ.
          rewrite /= in DEC. rewrite DEC.
          by eauto.
      + by destruct EQUIV.
    - destruct (getm cmem addr) eqn:CGET.
      + destruct a as [v ctg]. unfold refinement_common.refine_memory in REF.
        rewrite getm_map /= getm_filter /=.
        case CGET': (getm cmem' addr) EQUIV => [a|] //= EQUIV.
        rewrite /is_user /=.
        destruct EQUIV
          as [v0 v'' ? ? ? ut' EQ1 DEC1 EQ2 DEC2 SEQUIV|NEQ EQ]; subst; simpl.
        { inv EQ1.
          by rewrite (proj1 REF _ _ _ _ DEC1 CGET) in SGET. }
        { case DEC: (rules.fdecode _ _) => [[ut|]|] //=.
          apply: NEQ => /=.
          by rewrite DEC; eauto. }
     + destruct (getm cmem' addr) eqn:CGET'.
       * destruct EQUIV.
       * rewrite getm_map /= getm_filter /=.
         rewrite CGET'. simpl. constructor.
  }
Qed.

Lemma reg_refinement_equiv :
  forall (sregs : Symbolic.registers mt sp) cregs cregs' cmem,
    refinement_common.refine_registers sregs cregs cmem ->
    Conc.reg_equiv cregs cregs' ->
    exists (sregs' : Symbolic.registers mt sp),
    refinement_common.refine_registers sregs' cregs' cmem /\
    Sym.equiv sregs sregs'.
Proof.
  intros sreg creg creg' cmem REF EQUIV.
  exists (mapm (coerce Symbolic.R) (filterm (is_user Symbolic.R) creg')).
  split.
  { (*Refinement proof*)
    split.
    { move=> n v ctg tg /= DEC CGET'.
      by rewrite getm_map /= getm_filter /=
                 CGET' /= /is_user /= DEC /= /coerce /= DEC. }
    { move=> n v tg.
      rewrite getm_map /= getm_filter /=.
      case CGET': (creg' n)=> [[v' t']|] //=.
      rewrite /is_user /= /coerce /=.
      case CTG: (rules.fdecode _ _) => [[ut|?]|] //=.
      rewrite CTG /= => - [? ?]. subst v' ut.
      by eauto. }
  }
  { (*equiv proof*)
    unfold Sym.equiv, pointwise.
    intro n.
    unfold Conc.reg_equiv in EQUIV.
    specialize (EQUIV n).
    destruct EQUIV as ([v1 t1] & [v2 t2] & E1 & E2 & EQUIV).
    destruct (getm sreg n) eqn:SGET; simpl in SGET; rewrite SGET.
    - destruct a as [v utg].
      move: (proj2 REF n v utg SGET) => [ctg DEC CGET].
      rewrite CGET in E1. inversion E1; subst v1 t1; clear E1.
      rewrite getm_map /= getm_filter /=.
      destruct EQUIV
        as [v0 v'' ? ? ? ut' EQ1 DEC1 EQ2 DEC2 SEQUIV|NEQ EQ]; subst.
      * inv EQ1. inv EQ2. rewrite /= DEC1 in DEC. inv DEC.
        unfold is_user, coerce, rules.is_user.
        by rewrite E2 /= DEC2 /= DEC2.
      * inv EQ. simpl in NEQ.
        suff: False by [].
        by apply: NEQ; eexists; eauto.
    - rewrite getm_map /= getm_filter /=.
      rewrite E2. simpl.
      destruct EQUIV
        as [v0 v'' ? ? ? ut' EQ1 DEC1 EQ2 DEC2 SEQUIV|NEQ EQ]; subst.
       + inv EQ1.
         rewrite /is_user /coerce /=.
         case DEC: (rules.fdecode _ _) => [[?|?]|] //=.
         by rewrite (proj1 REF _ _ _ _ DEC1 E1) in SGET.
       + inv EQ.
         rewrite /is_user /coerce /=.
         case DEC: (rules.fdecode _ t2) => [[?|?]|] //=.
         apply: NEQ.
         by rewrite DEC; eauto.
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
  destruct (getm mem' addr) eqn:GET'.
  - destruct MEQUIV
      as [v0 v'' ? ? ? ut' EQ1 DEC1 EQ2 DEC2 SEQUIV|NEQ EQ]; subst.
    + inversion EQ1; subst. eauto.
      by rewrite rules.fdecode_kernel_tag in DEC1.
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
    case: (mem addr) INV MEQUIV SCALL => [[v ctg]|] INV MEQUIV SCALL; last by [].
    case: (mem' addr) MEQUIV => [[v' ctg']|] MEQUIV; last by [].
    destruct MEQUIV
          as [v0 v'' ? ? ? ut' EQ1 DEC1 EQ2 DEC2 SEQUIV|NEQ EQ]; subst.
    - inv EQ1. inv EQ2.
      by rewrite /= DEC1 andbF in SCALL.
    - simpl in *. inv EQ. assumption.
  }
  { intro CALL.
    case: (mem' addr) INV MEQUIV CALL => [[v' ctg']|] //= INV MEQUIV CALL.
    case: (mem addr) INV MEQUIV => [[v ctg]|] //= INV MEQUIV.
    inversion MEQUIV
          as [v0 v'' ? ? ? ut' EQ1 DEC1 EQ2 DEC2 SEQUIV| NEQ EQ]; subst.
    + inv EQ1. inv EQ2.
      move/andP in CALL.
      destruct CALL as [? CALL].
      by rewrite /= DEC2 in CALL.
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
  case: sst => smem sregs [pc tpc] int.
  case: cst => cmem cregs cache [pc' ctpc] epc.
  intros REF STEP.
  inversion STEP; subst.
  unfold refine_state in REF.
  destruct REF as [REF | CONTRA].
  move: tpc INUSER REF STEP => tpc' INUSER REF STEP.
  - destruct REF as [? ? REFM REFR ? ? WFENTRY ?].
    destruct (mem_refinement_equiv REFM MEQUIV) as [smem' [REFM' SMEQUIV]].
    destruct (reg_refinement_equiv REFR REQUIV) as [sreg' [REFR' SREQUIV]].
    eexists; split; [idtac | left]; econstructor; eauto.
  - case: CONTRA => [? [? [? [? CONTRA]]]].
    clear REQUIV MEQUIV.
    unfold refinement_common.kernel_exec in CONTRA.
    apply restricted_exec_snd in CONTRA.
    rewrite /refinement_common.in_kernel
            /= /Concrete.is_kernel_tag in CONTRA.
    move/eqP in CONTRA. rewrite /Concrete.pct /= in CONTRA. subst ctpc.
    by rewrite rules.fdecode_kernel_tag in INUSER.
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

Context {kcc : kernel_code_bwd_correctness ki stable}. (*should this go to the top?*)

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
      move/andP in VIS.
      destruct VIS as [VIS VIS'].
      assert (HIT: hit_step cst cst')
          by (constructor; auto).
      destruct (cache_hit_simulation UREF HIT) as [ast' SSTEP REF'].
      unfold refine_state, refine_state_weak.
      eexists; split. eauto.
      split;
      eauto using Sym.invariants_preserved_by_step.
    }
    { (*invisible step starting a from user state*)
      intro INVIS.
      case/nandP: INVIS=> [CONTRA | NUSER].
      - eapply @refine_state_in_user in UREF.
        rewrite UREF in CONTRA.
        by discriminate.
      - (*user to not user step*)
        left.
        unfold refine_state. split.
        + right. exists cst; exists cst'.
          repeat (split; auto).
          unfold kernel_exec.
          move: (user_into_kernel UREF STEP NUSER) => ?.
          by eapply re_refl; eauto.
        + eauto using Sym.invariants_preserved_by_step.
    }
  - (*starting from a kernel state*)
    split.
    { (*and taking a visible step*)
      intro VIS.
      unfold check in VIS.
      move/andP in VIS.
      destruct VIS as [VIS VIS'].
      destruct KREF as [ust [kst [UREF [UKSTEP KEXEC]]]].
      unfold kernel_exec in KEXEC.
      apply restricted_exec_snd in KEXEC.
      apply @in_user_in_kernel in VIS.
      by rewrite KEXEC in VIS.
    }
    { (*and taking an invisible step*)
      intro VIS.
      assert (REFW : @refine_state_weak mt ops sp _ ki stable ast cst)
        by (right; auto).
      destruct (backwards_simulation REFW STEP) as [REFW' | [ast' STEP' REF']].
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

(*XXX: Move this to refinement_common?*)
Lemma kernel_step cst cst' ast kst cst0 :
  refinement_common.refine_state ki stable ast cst0 ->
  Concrete.step ops rules.masks cst0 kst ->
  kernel_exec kst cst ->
  Concrete.step _ masks cst cst' ->
  in_kernel cst ->
  ~~ in_user cst' ->
  in_kernel cst'.
Proof.
  intros REF STEP EXEC STEP' INKERNEL INUSER.
  assert (REFW: @refine_state_weak _ _ _ _ ki stable ast cst).
  { right. eauto. }
  generalize (backwards_simulation REFW STEP').
  intros [[REF' | (? & ? & ? & ? & KEXEC')] | [? _ REF']].
  - apply @refine_state_in_user in REF'. by rewrite REF' in INUSER.
  - by apply restricted_exec_snd in KEXEC'.
  - apply @refine_state_in_user in REF'. by rewrite REF' in INUSER.
Qed.

(*This is a helper lemma to instantiate CFI refinement between
  symbolic and concrete*)
Lemma attacker_no_v : forall si sj,
                 Sym.invariants stable si ->
                 ~~ Sym.ssucc stable si sj ->
                 Symbolic.step stable si sj ->
                 ~ Sym.step_a si sj.
Proof.
  move=> si sj INV /negbTE SUCC STEP STEPA.
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
      apply Bool.orb_false_iff in SUCC; destruct SUCC;
      rewrite H2 in H; rewrite H2 in H; rewrite eqxx in H; by discriminate.
    + rewrite H2 in Heqo0. rewrite Heqo0 in PC. by inversion PC.
  - subst mem' reg'. simpl in *.
    destruct a as [v [|]].
    + rewrite H2 in Heqo0. rewrite PC in Heqo0. inversion Heqo0. subst o i.
      rewrite INST in SUCC.
      destruct o0;
      apply Bool.orb_false_iff in SUCC; destruct SUCC;
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

(*XXX: Move these to refinement_common*)
Lemma get_reg_no_user sreg reg m r v ctg t :
  @refinement_common.refine_registers mt sp _ sreg reg m ->
  getm sreg r = None ->
  getm reg r = Some v@ctg ->
  rules.fdecode Symbolic.R ctg = Some t ->
  exists ut, t = rules.ENTRY ut.
Proof.
  intros REF SGET GET DEC.
  destruct t.
  - move: (proj1 REF r v ctg ut DEC GET).
    by rewrite SGET.
  - eexists; reflexivity.
Qed.

Lemma get_mem_no_user smem mem addr v ctg t :
  @refinement_common.refine_memory mt sp _ smem mem ->
  getm smem addr = None ->
  getm mem addr = Some v@ctg ->
  rules.fdecode Symbolic.M ctg = Some t ->
  exists ut, t = rules.ENTRY ut.
Proof.
  intros REF SGET GET DEC.
  destruct t.
  - move: (proj1 REF addr v ctg ut DEC GET).
    by rewrite SGET.
  - eexists; reflexivity.
Qed.

Lemma in_user_ctpc cst :
  refinement_common.in_user cst ->
  exists ut,
    rules.fdecode Symbolic.P (common.tag (Concrete.pc cst)) = Some (rules.USER ut).
Proof.
  rewrite /in_user /=.
  by case: (rules.fdecode _ _) => [[?|?]|] //=; eauto.
Qed.

Lemma refine_traces_kexec axs cxs cst cst' :
  refine_traces cfi_refinementSC axs (cst :: cxs) ->
  in_kernel cst ->
  cst' \in cxs ->
  in_kernel cst' \/ exists cst'',
                      in_user cst'' /\
                      exec (Concrete.step ops masks) cst cst''.
Proof.
  elim: cxs axs cst => [|a cxs IHcxs] axs cst RTRACE KERNEL IN; first by [].
  inversion RTRACE
        as [? ? REF' | ? ? ? ? ? STEP CHECK REF REF' RTRACE'
            | ? ? ? ? ? ? STEP ASTEP REF REF' RTRACE'
            | ? ? ? ? ? ? NSTEP STEPA CSTEPA REF REF' RTRACE'];
  subst; simpl in *.
  { (*non-visible step*)
    rewrite !inE in IN; case/orP: IN => [/eqP ? | IN]; try subst a.
    + have [USER|USER] := boolP (in_user cst').
      * right. exists cst'. split; auto.
        econstructor(eauto).
      * destruct REF as [WREF INV]; clear INV.
        destruct WREF as [CONTRA | KREF].
        { apply @refine_state_in_user in CONTRA.
          apply @in_user_in_kernel in CONTRA.
          by rewrite KERNEL in CONTRA.
        }
        { destruct KREF as [cst0 [kst [KREF [CSTEP KEXEC]]]].
          assert (KERNEL' := kernel_step KREF CSTEP KEXEC STEP KERNEL USER).
          left. assumption.
        }
    + have [USER|USER] := boolP (in_user a).
      * right. exists a; split; auto.
        econstructor(eauto).
      * destruct REF as [WREF INV]; clear INV.
        destruct WREF as [CONTRA | KREF].
        { apply @refine_state_in_user in CONTRA.
          apply @in_user_in_kernel in CONTRA.
          by rewrite KERNEL in CONTRA.
        }
        { destruct KREF as [cst0 [kst [KREF [CSTEP KEXEC]]]].
          assert (KERNEL' := kernel_step KREF CSTEP KEXEC STEP KERNEL USER).
          destruct (IHcxs (ast :: axs0) a RTRACE' KERNEL' IN)
            as [KERNEL'' | [cst'' [USER'' EXEC]]].
          - left; assumption.
          - right. exists cst''.
            split; auto.
            econstructor(eauto).
        }
  }
  { (*visible step*)
    rewrite !inE in IN; case/orP: IN=> [/eqP ?|IN]; try subst a.
    + have [USER|USER] := boolP (in_user cst').
      * right. exists cst'. split; auto.
        econstructor(eauto).
      * destruct REF as [WREF INV]; clear INV.
        destruct WREF as [CONTRA | KREF].
        { apply @refine_state_in_user in CONTRA.
          apply @in_user_in_kernel in CONTRA.
          by rewrite KERNEL in CONTRA.
        }
        { destruct KREF as [cst0 [kst [KREF [CSTEP KEXEC]]]].
          assert (KERNEL' := kernel_step KREF CSTEP KEXEC STEP KERNEL USER).
          left. assumption.
        }
    + have [USER|USER] := boolP (in_user a).
      * right. exists a; split; auto.
        econstructor(eauto).
      * destruct REF as [WREF INV]; clear INV.
        destruct WREF as [CONTRA | KREF].
        { apply @refine_state_in_user in CONTRA.
          apply @in_user_in_kernel in CONTRA.
          by rewrite KERNEL in CONTRA.
        }
        { destruct KREF as [cst0 [kst [KREF [CSTEP KEXEC]]]].
          assert (KERNEL' := kernel_step KREF CSTEP KEXEC STEP KERNEL USER).
          destruct (IHcxs (ast' :: axs0) a RTRACE' KERNEL' IN)
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
    move/eqP: KERNEL INUSER.
    rewrite /Concrete.pct /= => ->.
    by rewrite rules.fdecode_kernel_tag.
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
    Conc.all_attacker masks (hd ++ [:: csi]) /\
    Concrete.step _ masks csi csj /\ ~~ check csi csj /\
    ((exists asi, refine_traces cfi_refinementSC [:: asi] (csi :: csj :: tl)
                /\ exec (@Sym.step_a mt ids cfg) ast asi)
    \/ (exists asi asj atl,
          refine_traces cfi_refinementSC (asi :: asj :: atl) (csj :: tl) /\
          Sym.all_stuck stable (asi :: asj :: atl) /\
          exec (@Sym.step_a mt ids cfg) ast asi /\
          refine_state asi csi)).
Proof.
  intros ALLA ALLS CSTEP RTRACE.
  move: axs cst cst' ast ast' ALLA ALLS CSTEP RTRACE.
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
      have IN: ast \in (ast :: ast' :: axs) by rewrite inE eqxx.
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
      have IN: ast \in (ast :: ast' :: axs) by rewrite inE eqxx.
      specialize (ALLS ast IN).
      eauto.
    + destruct axs as [|ast'' axs].
      * inversion RTRACE'
          as [? ? REF''| | | ]; subst.
       { simpl in *.
         right.
         exists [:: cst]; exists cxs; exists cst'; exists cst''.
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
          exists [:: cst]; exists cxs; exists cst'; exists cst''.
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
        { have IN: ast' \in (ast :: ast' :: ast'' :: axs) by rewrite !inE eqxx orbT.
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
          specialize (IHcxs axs cst' cst'' ast' ast'' ALLA ALLS STEP RTRACE').
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
  all in_user (cst :: cst' :: cxs).
Proof.
  intro ALLA.
  apply/allP=> x IN.
  elim: cxs cst cst' ALLA IN => [|a cxs IH]; intros.
  - have IN2 : In2 cst cst' [:: cst;cst'] by simpl; auto.
    apply ALLA in IN2.
    destruct IN2 as [STEPA ?].
    by rewrite !inE in IN; case/orP: IN=> /eqP ?; subst; inv STEPA; auto.
  - rewrite inE in IN; case/orP: IN=> [/eqP ? | IN]; subst.
    + assert (IN2: In2 cst cst' (cst :: cst' :: a :: cxs))
        by (simpl; auto).
      destruct (ALLA _ _ IN2) as [STEPA ?].
      by inv STEPA; auto.
    + by apply Conc.all_attacker_red in ALLA; eauto.
Qed.

Lemma all_attacker_implies_all_user' cst cst' cxs :
  Conc.all_attacker masks (cst :: cxs ++ [:: cst']) ->
  all in_user (cst :: cxs ++ [:: cst']).
Proof.
  intro ALLA.
  apply/allP=> x IN.
  elim: cxs cst cst' ALLA IN=> [|a cxs IH] /=; intros.
  - rewrite !inE in IN; case/orP: IN=> /eqP ?; subst.
    + have IN2 : In2 cst cst' [:: cst;cst'] by (simpl; auto).
      apply ALLA in IN2.
      destruct IN2 as [STEPA ?].
      by inv STEPA; auto.
    + assert (IN2 : In2 cst cst' [:: cst;cst']) by (simpl; auto).
      destruct (ALLA _ _ IN2) as [STEPA ?].
      inv STEPA; auto.
  - rewrite inE in IN; case/orP: IN=> [/eqP ?|IN]; subst.
    + assert (IN2: In2 cst a (cst :: a :: cxs ++ [:: cst']))
        by (simpl; auto).
      simpl in ALLA.
      apply ALLA in IN2.
      destruct IN2 as [STEPA ?].
      by inv STEPA; auto.
    + simpl in ALLA.
      apply Conc.all_attacker_red in ALLA.
      specialize (IH _ _ ALLA IN).
      assumption.
Qed.

Lemma user_into_kernel_wrapped sst cst cst' :
  in_user cst ->
  refine_state sst cst ->
  Concrete.step ops masks cst cst' ->
  ~~ in_user cst' -> in_kernel cst'.
Proof.
  intros USER REF STEP NUSER.
  destruct REF as [REF ?].
  destruct REF as [WREF | CONTRA].
  - by eauto using user_into_kernel.
  - destruct CONTRA as [? [? [? [? KEXEC]]]].
    apply restricted_exec_snd in KEXEC.
    apply @in_user_in_kernel in USER.
    by rewrite KEXEC in USER.
Qed.

(* MOVE to refinement_common. *)
Lemma transfer_none_lookup_none cmvec ivec cmem cache :
  refinement_common.cache_correct cache cmem ->
  rules.decode_ivec (rules.encodable_of_fencodable e) cmem cmvec = Some ivec ->
  Symbolic.transfer ivec = None ->
  Concrete.cache_lookup cache masks cmvec = None.
Proof.
  move=> CACHE DEC TRANS.
  case LOOKUP: (Concrete.cache_lookup cache masks cmvec) => [crvec|] //=.
  have [t E] : exists t, rules.decode Symbolic.P cmem (Concrete.ctpc cmvec) = Some (rules.USER t).
    by have [[op [? []]]|[]] := rules.decode_ivec_inv DEC; eauto.
  have := CACHE _ _ LOOKUP.
  rewrite {}E => /(_ erefl) [ivec' [ovec [DEC' _ TRANS']]].
  rewrite DEC in DEC'. case: DEC' TRANS => ->.
  by rewrite TRANS'.
Qed.

Lemma violation_implies_kexec sst cst cst' umvec sxs cxs :
  Sym.violation stable sst ->
  build_ivec stable sst = Some umvec ->
  in_user cst ->
  ~~ check cst cst' ->
  Concrete.step ops masks cst cst' ->
  refine_state sst cst ->
  refine_traces cfi_refinementSC (sst :: sxs) (cst' :: cxs) ->
  all in_kernel (cst' :: cxs).
Proof.
  move=> VIOLATION UMVEC USER NUSER' STEP REF RTRACE.
  rewrite /check USER /= in NUSER'.
  assert (UHANDLER := Sym.is_violation_implies_stop stable sst VIOLATION UMVEC).
  assert (KERNEL := user_into_kernel_wrapped USER REF STEP NUSER').
  rewrite /= KERNEL /=.
  apply/allP=> kst /(refine_traces_kexec RTRACE KERNEL)
                   [? //|[cst'' [USER'' EXEC]]].
  (*the case where one user step was in the trace contradicts*)
  destruct REF as [[REF | CONTRA] ?].
  - have [//= cmvec CMVEC DEC] := refine_ivec REF UMVEC.
    destruct REF.
    apply @in_user_in_kernel in USER''.
    destruct cst as [cmemt cregt cachet [cpct ctpct] epct].
    destruct sst as [smemt sregt [spct tpct] intt].
    rewrite /Concrete.pcv /= in rs_pc. subst cpct.
    simpl in DEC.
    have := @handler_correct_disallowed_case mt ops sp _ ki
                                             stable kcc _
                                             cmvec _
                                             _ spct@ctpct _ cst''
                                             rs_kinv _ USER''.
    rewrite DEC UHANDLER => /(_ erefl).
    have LOOKUP := transfer_none_lookup_none rs_cache DEC UHANDLER.
    have /= <- := initial_handler_state CMVEC LOOKUP STEP.
    by move=> /(_ EXEC).
  - (*refinement contradictory case*)
    destruct CONTRA as [? [? [? [? KEXEC]]]].
    apply restricted_exec_snd in KEXEC.
    apply @in_user_in_kernel in USER.
    by rewrite KEXEC in USER.
Qed.

Lemma no_umvec_implies_kexec sst cst cst' sxs cxs :
  Sym.violation stable sst ->
  build_ivec stable sst = None ->
  in_user cst ->
  ~~ check cst cst' ->
  Concrete.step ops masks cst cst' ->
  refine_state sst cst ->
  refine_traces cfi_refinementSC (sst :: sxs) (cst' :: cxs) ->
  all in_kernel (cst' :: cxs).
Proof.
  move=> VIOLATION UMVEC USER NUSER' STEP REF RTRACE.
  rewrite /check USER /= in NUSER'.
  (*assert (UHANDLER := Sym.is_violation_implies_stop stable sst VIOLATION UMVEC).*)
  assert (KERNEL := user_into_kernel_wrapped USER REF STEP NUSER').
  rewrite /= KERNEL /=.
  apply/allP=> kst /(refine_traces_kexec RTRACE KERNEL)
                   [? //|[cst'' [USER'' EXEC]]].
  (*the case where one user step was in the trace contradicts*)
  destruct REF as [[REF | CONTRA] ?].
  - have [cmvec CMVEC] := step_build_cmvec STEP.
    case DEC: (rules.decode_ivec _ (Concrete.mem cst) cmvec) => [ivec|].
      by rewrite (refine_ivec_inv REF CMVEC DEC) in UMVEC.
    destruct REF. subst.
    have := @handler_correct_disallowed_case mt ops sp _ ki
                                             stable kcc _
                                             cmvec _ _ (Concrete.pc cst) _ cst''
                                             rs_kinv _ (in_user_in_kernel USER'').
    rewrite DEC => /(_ erefl).
    case LOOKUP: (Concrete.cache_lookup (Concrete.cache cst) masks cmvec) => [crvec|].
      rewrite /in_user /= in USER.
      have := rs_cache _ _ LOOKUP.
      rewrite (build_cmvec_ctpc CMVEC) /= => /(_ USER) [ivec [ovec [DEC' _ _ _]]].
      by rewrite DEC' in DEC.
    by rewrite -(initial_handler_state CMVEC LOOKUP STEP) => /(_ EXEC).
  - (*refinement contradictory case*)
    destruct CONTRA as [? [? [? [? KEXEC]]]].
    apply restricted_exec_snd in KEXEC.
    apply @in_user_in_kernel in USER.
    by rewrite KEXEC in USER.
Qed.

Theorem cfg_true_equiv ssi ssj csi csj :
  refine_state ssi csi ->
  refine_state ssj csj ->
  Symbolic.step stable ssi ssj ->
  Sym.ssucc stable ssi ssj ->
  Concrete.step ops masks csi csj ->
  Conc.csucc cfg csi csj.
Proof.
  intros.
  destruct H as [REF INV].
  destruct REF as [UREFI | KREFI].
  - destruct H0 as [REF' INV'].
    destruct REF' as [UREFJ | KREFJ].
    + move: (refine_state_in_user UREFI) (refine_state_in_user UREFJ) => USERI USERJ.
      assert (NKERNEL : in_kernel csi || in_kernel csj = false).
      { apply/norP.
        by rewrite (in_user_in_kernel USERI) (in_user_in_kernel USERJ). }
      destruct ssi as [smemi sregi [pci tpci] inti].
      destruct csi as [cmemi cregi cachei [pci' ctpci] epci].
      destruct UREFI as [PCI DEC REFM REFR CACHE MVE WF KI].
      rewrite /Concrete.pcv /= in PCI. subst pci'.
      destruct ssj as [smemj sregj [pcj tpcj] intj].
      destruct csj as [cmemj cregj cachej [pcj' ctpcj] epcj].
      destruct UREFJ as [PCJ DEC' REFM' REFR' C3 C5 C6 C7].
      rewrite /Concrete.pcv /= in PCJ. subst pcj'.
      unfold Conc.csucc.
      rewrite NKERNEL /=.
      unfold Sym.ssucc in H2.
      rewrite /= in H2.
      destruct (getm smemi pci) as [[v tg]|] eqn:GET.
      * rewrite GET in H2.
        have [ctg /= DECctg CGET] := proj2 REFM pci v tg GET.
        rewrite CGET DECctg /=.
        destruct tg as [[src|]|].
        { simpl in GET.
          destruct (decode_instr v) eqn:INST.
          - destruct i eqn:OP; try assumption. (*TODO: fix jmp/jal copy paste*)
            { (*jmp*)
              destruct (getm smemi pcj) as [[v' tg]|] eqn:GET'.
              - have [ctg' /= DECctg' CGET'] := proj2 REFM pcj v' tg GET'.
                rewrite GET' in H2.
                by rewrite CGET' DECctg'.
              - rewrite GET' in H2.
                destruct (Symbolic.get_syscall stable pcj) eqn:GETCALL.
                + rewrite GETCALL in H2.
                  unfold wf_entry_points in WF.
                  specialize (WF pcj (Symbolic.entry_tag s)).
                  assert (ECALL : exists2 sc : Symbolic.syscall mt,
                                    Symbolic.get_syscall stable pcj = Some sc &
                                    Symbolic.entry_tag sc = Symbolic.entry_tag s)
                    by (eexists; eauto).
                  apply WF in ECALL.
                  case: (getm cmemi pcj) ECALL => [[v' tg]|] ECALL //.
                  move/andP in ECALL.
                  case: ECALL => [ISNOP /= /eqP ETAG].
                  rewrite ETAG.
                  destruct (Symbolic.entry_tag s) as [[?|]|] eqn:ETAG';
                    rewrite ETAG' in H2; try discriminate.
                  apply/andP.
                  by auto.
                + rewrite GETCALL in H2. by discriminate.
            }
            { (*jal*)
              destruct (getm smemi pcj) as [[v' tg]|] eqn:GET'.
              - have [ctg' /= DECctg' CGET'] := proj2 REFM pcj v' tg GET'.
                rewrite GET' in H2.
                by rewrite CGET' DECctg'.
              - rewrite GET' in H2.
                destruct (Symbolic.get_syscall stable pcj) eqn:GETCALL.
                + rewrite GETCALL in H2.
                  unfold wf_entry_points in WF.
                  specialize (WF pcj (Symbolic.entry_tag s)).
                  assert (ECALL : exists2 sc : Symbolic.syscall mt,
                                    Symbolic.get_syscall stable pcj = Some sc &
                                    Symbolic.entry_tag sc = Symbolic.entry_tag s)
                    by (eexists; eauto).
                  apply WF in ECALL.
                  case: (getm cmemi pcj) ECALL => [[v' tg]|] ECALL //.
                  case/andP: ECALL => [ISNOP ETAG].
                  simpl.
                  move/eqP:ETAG => /= ETAG.
                  rewrite ETAG.
                  destruct (Symbolic.entry_tag s) as [[?|]|] eqn:ETAG';
                    rewrite ETAG' in H2; try discriminate.
                  apply/andP.
                  by auto.
                + rewrite GETCALL in H2. by discriminate.
            }
          - by discriminate.
        }
        { by trivial. }
        { by discriminate. }
        { rewrite GET in H2.
          case GETSC: (Symbolic.get_syscall _ _) H2 => [sc|] //= _.
          remember (Symbolic.entry_tag sc) as sct eqn:ETAG. symmetry in ETAG.
          have /WF: exists2 sc, Symbolic.get_syscall stable pci = Some sc &
                               Symbolic.entry_tag sc = sct by eexists; eauto.
          case GET': (getm cmemi  pci) => [[v ctg]|] //=.
          assert (CONTRA := fun CACHE GET' =>
                              valid_initial_user_instr_tags (v := v) (ti := ctg) CACHE USERI USERJ H3 GET').
          move: (CONTRA CACHE GET') => {CONTRA} /=.
          case: (rules.fdecode _ ctg) => [[t | ]|] //= _.
          by rewrite andbF. }
    + destruct KREFJ as [? [? [? [? KEXEC]]]].
      apply restricted_exec_snd in KEXEC.
      unfold Conc.csucc. rewrite KEXEC.
      simpl. rewrite orbT. reflexivity.
  - destruct KREFI as [? [? [? [? KEXEC]]]].
    apply restricted_exec_snd in KEXEC.
    unfold Conc.csucc. rewrite KEXEC.
    by reflexivity.
Qed.

Theorem cfg_false_equiv ssi ssj csi csj :
  refine_state ssi csi ->
  refine_state ssj csj ->
  ~~ Sym.ssucc stable ssi ssj ->
  check csi csj ->
  Concrete.step ops masks csi csj ->
  ~~ Conc.csucc cfg csi csj.
Proof.
  intros.
  destruct H as [REF INV], H0 as [REF' INV']. clear INV'.
  unfold check in H2.
  move/andP in H2.
  destruct H2 as [USER USER'].
  destruct REF as [REF | CONTRA].
  - destruct REF' as [REF' | CONTRA'].
    + apply @in_user_in_kernel in USER.
      apply @in_user_in_kernel in USER'.
      unfold Conc.csucc. rewrite (negbTE USER) (negbTE USER').
      simpl.
      move: (refine_state_in_user REF) (refine_state_in_user REF') => USERT USERT'.
      destruct ssi as [smem sreg [pc tpc] int],
               csi as [cmem creg cache [pc2 ctpc] epc],
               ssj as [smem' sreg' [pc' tpc'] int'],
               csj as [cmem' creg' cache' [pc2' ctpc'] epc'],
               REF as [PC DEC REFM REFR CACHE MVEC WF KI],
               REF' as [PC' DEC' REFM' REFR' C3 C5 C6 C7].
      simpl. rewrite /Concrete.pcv /= in PC PC'. subst pc2 pc2'.
      unfold Sym.ssucc in H1.
      simpl in H1.
      destruct (getm smem pc) eqn:GET.
      { destruct a as [v utg].
        destruct utg.
        - rewrite GET in H1.
          move/(proj2 REFM): GET => //= [ctg DECctg GET].
          rewrite GET DECctg.
          simpl.
          destruct (decode_instr v).
          + (*is instruction*)
            destruct i eqn:OP; destruct o; try trivial.
            destruct (getm smem pc') as [[v' [[dst|]|]]|] eqn:SGET'.
            * rewrite SGET' in H1.
              move/(proj2 REFM): SGET' => [/= ctg' DECctg' SGET'].
              by rewrite SGET' DECctg'.
            * move/(proj2 REFM): SGET' => [/= ctg' DECctg' SGET'].
              by rewrite SGET' DECctg'.
            * move/(proj2 REFM): SGET' => [/= ctg' DECctg' SGET'].
              by rewrite SGET' DECctg'.
            * rewrite SGET' in H1.
              rewrite /Symbolic.pcv /=.
              destruct (getm cmem pc') as [[cv' ctg']|] eqn:GET'.
              { simpl.
                case DEC'': (rules.fdecode _ ctg') => [[ut|ut]|] //=.
                - by rewrite (proj1 REFM _ _ _ _ DEC'' GET') in SGET'.
                - unfold wf_entry_points in WF.
                  destruct (Symbolic.get_syscall stable pc') eqn:GETCALL.
                  + rewrite GETCALL in H1.
                    specialize (WF pc' (Symbolic.entry_tag s0)).
                    assert (ECALL: (exists2 sc : Symbolic.syscall mt,
                               Symbolic.get_syscall stable pc' = Some sc &
                               Symbolic.entry_tag sc = Symbolic.entry_tag s0))
                      by (eexists; eauto).
                    apply WF in ECALL.
                    rewrite GET' in ECALL.
                    move/andP in ECALL. destruct ECALL as [ISNOP CTG].
                    move/eqP:CTG => CTG.
                    rewrite /= DEC'' in CTG. case: CTG => CGT. subst ut.
                    destruct (Symbolic.entry_tag s0) as [[?|]|] eqn:ETAG; rewrite ETAG in H1;
                    auto.
                    by rewrite (negbTE H1) andbF.
                  + clear H1.
                    case: ut DEC'' => [[ut|]|] //= DEC''.
                    apply/negP=> /andP [ISNOP _].
                    move: (wf_entry_points_only_if WF GET' DEC'' ISNOP) => [? ? ?].
                    congruence.
              }
              { by reflexivity. }
              (*copy paste from above, TODO: fix*)
              destruct (getm smem pc') as [[v' [[dst|]|]]|] eqn:SGET'.
            * rewrite SGET' in H1.
              move/(proj2 REFM): SGET' => [/= ctg' DECctg' SGET'].
              by rewrite SGET' DECctg'.
            * move/(proj2 REFM): SGET' => [/= ctg' DECctg' SGET'].
              by rewrite SGET' DECctg'.
            * move/(proj2 REFM): SGET' => [/= ctg' DECctg' SGET'].
              by rewrite SGET' DECctg'.
            * rewrite SGET' in H1.
              rewrite /Symbolic.pcv /=.
              destruct (getm cmem pc') as [[cv' ctg']|] eqn:GET'.
              { simpl.
                case DEC'': (rules.fdecode _ ctg') => [[ut|ut]|] //=.
                - by rewrite (proj1 REFM _ _ _ _ DEC'' GET') in SGET'.
                - unfold wf_entry_points in WF.
                  destruct (Symbolic.get_syscall stable pc') eqn:GETCALL.
                  + rewrite GETCALL in H1.
                    specialize (WF pc' (Symbolic.entry_tag s0)).
                    assert (ECALL: (exists2 sc : Symbolic.syscall mt,
                               Symbolic.get_syscall stable pc' = Some sc &
                               Symbolic.entry_tag sc = Symbolic.entry_tag s0))
                      by (eexists; eauto).
                    apply WF in ECALL.
                    rewrite GET' in ECALL.
                    case/andP: ECALL=> [ISNOP CTG].
                    move/eqP:CTG => CTG.
                    rewrite /= DEC'' in CTG. case: CTG => CGT. subst ut.
                    destruct (Symbolic.entry_tag s0) as [[?|]|] eqn:ETAG; rewrite ETAG in H1;
                    auto.
                    by rewrite (negbTE H1) andbF.
                  + clear H1.
                    case: ut DEC'' => [[ut|]|] //= DEC''.
                    apply/negP=> /andP [ISNOP _].
                    move: (wf_entry_points_only_if WF GET' DEC'' ISNOP) => [? ? ?].
                    congruence.
              }
              { by reflexivity. }
          + by assumption.
        - apply REFM in GET.
          case: GET=> ctg /= DEC'' GET.
          by rewrite /= GET DEC''.
      }
      { rewrite /Symbolic.pcv /=.
        destruct (getm cmem pc) as [[v ctg]|] eqn:GET'; trivial. simpl.
        case DECTG: (rules.fdecode _ _)=> [[t| ]| ] //=.
        by rewrite (proj1 REFM _ _ _ _ DECTG GET') in GET. }
    + destruct CONTRA' as [? [? [? [? KEXEC]]]].
      apply restricted_exec_snd in KEXEC.
      apply @in_user_in_kernel in USER'. rewrite KEXEC in USER'.
      discriminate.
  - destruct CONTRA as [? [? [? [? KEXEC]]]].
      apply restricted_exec_snd in KEXEC.
      apply @in_user_in_kernel in USER. rewrite KEXEC in USER.
      discriminate.
Qed.

Program Instance cfi_refinementAS_specs :
  machine_refinement_specs cfi_refinementSC.
Next Obligation. (*step or no step*)
  by case: (stepP' masks cst cst') => [H | H]; auto.
Qed.
Next Obligation. (*initial states*)
  unfold Conc.cinitial in H.
  destruct H as [ast [INIT REF]].
  eexists; split; [eassumption | split].
  - left; assumption.
  - destruct INIT as [? INV]; by assumption.
Qed.
Next Obligation.
  case/nandP: H1=> [CONTRA | NUSER].
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
      rewrite orbT. reflexivity.
    + destruct REF as [? [? [? [? KEXEC]]]].
      apply restricted_exec_snd in KEXEC.
      unfold Conc.csucc. rewrite KEXEC.
      by reflexivity.
Qed.
Next Obligation. (*symbolic-concrete cfg relation*)
  apply (introTF idP).
  have [SUCC|SUCC] := boolP (Sym.ssucc stable asi asj).
  - by eauto using cfg_true_equiv.
  - apply/negP. by eauto using cfg_false_equiv.
Qed.
Next Obligation. (*symbolic no attacker on violation*)
  destruct H as [? INV].
  by eapply attacker_no_v; eauto.
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
  case/andP: CHECK => [USERI USERJ].
  destruct REFI as [WREFI INVI].
  inversion RTRACES
    as [? ? REF' | ? ? ? ? ? STEP CHECK REFJ REF' RTRACE'
        | ? ? ? ? ? ? STEP ASTEP REFJ REF' RTRACE'
        | ? ? ? ? ? ? NSTEP STEPA SSTEPA REF REF' RTRACE'];
    subst; simpl in *.
  - (*case trace is a singleton*)
    left.
    split; [intros ? ? IN2; destruct IN2 | idtac].
    by apply/andP; auto.
  - (*case an invisible step is taken*)
    destruct (Sym.succ_false_implies_violation INVI SUCC SSTEP)
      as [CONTRA | VIOLATION]; first done.
    right.
    exists [:: csj]; exists (cst' :: cxs0).
    split; auto.
    split.
    intros ? ? CONTRA; destruct CONTRA.
    split; first by apply/allP=> x; rewrite inE => /eqP -> {x}; auto.
    destruct (build_ivec stable asj) as [umvec|] eqn:UMVEC.
    + (*case the umvec for asj exists*)
        by eauto using violation_implies_kexec.
    + (*case where the umvec for asj does not exist*)
        by eauto using no_umvec_implies_kexec.
  - (*case of normal steps*)
    exfalso.
    destruct SSTOP as [? ALLS].
    have IN: asj \in (asj :: ast' :: axs0) by rewrite inE eqxx.
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
         exists (chd++[:: csi']); exists (csj'::ctl).
         split. rewrite -catA. by reflexivity.
         split. by assumption.
         split.
         { apply/allP.
           destruct chd.
           - move=> x /=; rewrite inE; move=> /eqP {x}->.
             by inv CLST; auto.
           - move=> x IN.
             apply all_attacker_implies_all_user' in ALLA'.
             assert (ALLU: forall x, x \in ((s :: chd) ++ [:: csi']) -> in_user x)
               by (apply/allP; auto).
             specialize (ALLU _ IN). by auto.
         }
         { inversion RTRACE as [| ? ? ? ? ? STEP' CHECK' REFI' REFJ' RTRACE' | |];
           subst.
           assert (USERI' : in_user csi').
           { destruct chd.
             - inv CLST.
                 by assumption.
             - apply all_attacker_implies_all_user' in ALLA'.
               have IN: csi' \in (s :: chd ++ [:: csi'])
                 by rewrite !(inE, mem_cat) /= eqxx !orbT; eauto.
               assert (ALLU: forall x, x \in ((s :: chd) ++ [:: csi']) -> in_user x)
               by (apply/allP; auto).
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
         * assert (IN: asi' \in (asi' :: asj' :: atl))
             by (rewrite !inE eqxx; auto).
           apply ALLS' in IN. by eauto.
           assert (VIOLATION' := Sym.violation_preserved_by_exec_a _ VIOLATION AEXEC).
           clear VIOLATION.
           assert (USERI' : in_user csi').
           { destruct chd.
             - inv CLST.
               by auto.
             - apply all_attacker_implies_all_user' in ALLA'.
               assert (ALLU : forall x, x \in (s :: chd ++ [:: csi']) ->
                                        in_user x)
                 by (apply/allP; auto).
               have IN: csi' \in (s :: chd ++ [:: csi'])
                 by rewrite !(inE, mem_cat) eqxx !orbT /=; auto.
               by auto.
           }
           assert (USERN: in_user csn)
             by (inv STEPAN; auto).
           destruct ctl; [by inversion RTRACE |idtac].
           destruct (build_ivec stable asi') as [umvec|] eqn:UMVEC.
            - (*case the umvec exists*)
             assert (KERNEL := violation_implies_kexec VIOLATION' UMVEC USERI'
                                                       CHECK CSTEP REFN RTRACE).
             apply In2_implies_In in IN2.
             assert (KERNEL' : forall x, x \in (csj' :: s :: ctl) -> in_kernel x)
               by (apply/allP; auto).
             apply KERNEL' in IN2.
             apply @in_user_in_kernel in USERN.
             rewrite IN2 in USERN.
             by discriminate.
           - (*case the umvec does not exist*)
             assert (KERNEL := no_umvec_implies_kexec VIOLATION' UMVEC USERI'
                                                       CHECK CSTEP REFN RTRACE).
             apply In2_implies_In in IN2.
             assert (KERNEL' : forall x, x \in (csj' :: s :: ctl) -> in_kernel x)
               by (apply/allP; auto).
             apply KERNEL' in IN2.
             apply @in_user_in_kernel in USERN.
             rewrite IN2 in USERN.
             by discriminate.
       }
Qed.

End Refinement.
