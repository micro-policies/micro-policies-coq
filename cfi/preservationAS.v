Require Import lib.utils.
Require Import common.common.
Require Import symbolic.symbolic.
Require Import symbolic.exec.
Require Import cfi.classes.
Require Import cfi.abstract.
Require Import cfi.symbolic.
Require Import cfi.preservation.
Require Import cfi.refinementAS.
Require Import cfi.rules.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Set Implicit Arguments.

Import PartMaps.

Section Refinement.

Context {t : machine_types}
        {ops : machine_ops t}
        {opss : machine_ops_spec ops}
        {ids : @classes.cfi_id t}.

Variable cfg : classes.id -> classes.id -> bool.

Instance sp : Symbolic.params := Sym.sym_cfi cfg.

Variable atable : list (Abs.syscall t).
Variable stable : list (Symbolic.syscall t).

Definition amachine :=  Abs.abstract_cfi_machine atable cfg.
Definition smachine := Sym.symbolic_cfi_machine stable.

(*Hypothesis*)
Definition refine_sc := RefinementAS.refine_syscalls stable atable stable.

(*TODO: look at arguments mess*)
Hypothesis ref_sc_correct : refine_sc.

Hypothesis syscall_sem :
  forall ac ast ast',
    @Abs.sem t ac ast = Some ast' ->
       let '(Abs.State imem _ _ _ b) := ast in
       let '(Abs.State imem' _ _ _ b') := ast' in
         imem = imem' /\ b' = b.

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

Hypothesis syscall_preserves_register_tags :
  forall sc st st',
    Sym.registers_tagged (cfg:=cfg)(Symbolic.regs st) ->
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


Definition backwards_simulation :=
  RefinementAS.backwards_simulation ref_sc_correct syscall_sem
                                    syscall_preserves_instruction_tags
                                    syscall_preserves_valid_jmp_tags
                                    syscall_preserves_entry_tags.

Lemma untag_implies_reg_refinement reg :
  Sym.registers_tagged reg ->
  RefinementAS.refine_registers (cfg := cfg) (PartMaps.map RefinementAS.untag_atom reg) reg.
Proof.
  intros RTG r v.
  split.
  - intros GET.
    rewrite PartMaps.map_correctness.
    rewrite GET. reflexivity.
  - intros GET.
    rewrite PartMaps.map_correctness in GET.
    destruct (get reg r) eqn:GET'.
    + destruct a. simpl in GET.
      assert (tag = DATA)
        by (apply RTG in GET'; assumption).
      subst.
      rewrite GET' in GET.
      simpl in GET.
      inv GET.
      assumption.
    + rewrite GET' in GET. simpl in GET. congruence.
Qed.

Lemma untag_data_implies_dmem_refinement mem :
  RefinementAS.refine_dmemory
    (PartMaps.map RefinementAS.untag_atom (filter RefinementAS.is_data mem)) mem.
Proof.
   intros addr v.
   split.
   - intros GET.
     rewrite PartMaps.map_correctness.
     rewrite filter_correctness.
     rewrite GET. reflexivity.
   - intros GET.
     rewrite PartMaps.map_correctness in GET.
     rewrite filter_correctness in GET.
     destruct (get mem addr) eqn:GET'.
     + destruct a as [val tg].
       simpl in GET.
       destruct tg as [[id|]|]; simpl in GET.
       * congruence.
       * congruence.
       * inv GET. reflexivity.
     + simpl in GET. congruence.
Qed.

Definition is_instr (a : atom (word t) cfi_tag) :=
  match common.tag a with
    | INSTR _ => true
    | DATA => false
  end.

Lemma untag_instr_implies_imem_refinement mem :
  RefinementAS.refine_imemory
    (PartMaps.map RefinementAS.untag_atom (filter is_instr mem)) mem.
Proof.
   intros addr v.
   split.
   - intros (ut & GET).
     rewrite PartMaps.map_correctness.
     rewrite filter_correctness.
     rewrite GET. reflexivity.
   - intros GET.
     rewrite PartMaps.map_correctness in GET.
     rewrite filter_correctness in GET.
     destruct (get mem addr) eqn:GET'.
     + destruct a as [val tg].
       simpl in GET.
       destruct tg as [[id|]|]; simpl in GET.
       * inv GET. eexists; reflexivity.
       * inv GET; eexists; reflexivity.
       * congruence.
     + simpl in GET. congruence.
Qed.

Hint Resolve untag_instr_implies_imem_refinement.
Hint Resolve untag_data_implies_dmem_refinement.
Hint Resolve untag_implies_reg_refinement.

Theorem cfg_true_equiv (asi asj : Abs.state t) ssi ssj :
  RefinementAS.refine_state stable asi ssi ->
  RefinementAS.refine_state stable asj ssj ->
  Abs.step atable cfg asi asj ->
  Abs.succ atable cfg asi asj ->
  Symbolic.step stable ssi ssj ->
  Sym.ssucc stable ssi ssj.
Proof.
  intros REF REF' ASTEP ASUCC SSTEP.
  destruct asi as [imem dmem aregs apc b],
           asj as [imem' dmem' aregs' apc' b'].
  destruct ssi as [mem regs [spc tpc] int].
  destruct ssj as [mem' regs' [spc' tpc'] int'].
  destruct REF as [REFI [REFD [REFR [REFPC [? [? [ITG [VTG ETG]]]]]]]].
  destruct REF' as [REFI' [REFD' [REFR' [REFPC' ?]]]].
  unfold Abs.succ in ASUCC.
  unfold RefinementAS.refine_pc in REFPC; simpl in REFPC;
  destruct REFPC as [? TPC];
  unfold RefinementAS.refine_pc in REFPC'; simpl in REFPC';
  destruct REFPC' as [? TPC'];
  subst.
  unfold Sym.ssucc; simpl.
  destruct (get imem spc) as [s|] eqn:GET.
  + destruct (decode_instr s) eqn:INST.
    - destruct i eqn:DECODE;
      apply REFI in GET;
      destruct GET as [id GET'];
      rewrite GET'; destruct id; rewrite INST; simpl;
      try assumption;
      destruct (VTG _ _ ASUCC)
        as [[? ?] [[? GETSPC'] | [GETSPC' [? [GETCALL ETAG]]]]]; simpl in *;
      unfold Abs.valid_jmp, valid_jmp in ASUCC;
      repeat match goal with
        | [H: get _ ?Spc = Some _@(INSTR _),
           H1: get _ ?Spc = Some _@(INSTR (word_to_id ?Spc)) |- _] =>
          rewrite H1 in H; inv H
        | [H: ?Expr = _, H1: context[match ?Expr with _ => _ end] |- _] =>
           rewrite H in H1
        | [H: ?Expr = _ |-
           is_true match ?Expr with _ => _ end] =>
          rewrite H
        | [H: is_true match ?Expr with _ => _ end |-
           is_true match ?Expr with _ => _ end] =>
          destruct Expr
      end; try discriminate; by auto.
    - by discriminate.
  + destruct (Abs.get_syscall atable spc) eqn:GETCALL.
    - destruct (get mem spc) eqn:GET'.
      { destruct a as [v ut].
        destruct ut.
        * assert (EGET': exists id, get mem spc = Some v@(INSTR id))
            by (eexists; eauto).
          apply REFI in EGET'.
          rewrite EGET' in GET. congruence.
        * rewrite GET'.
          destruct (get dmem spc) eqn:AGET.
          + discriminate.
          + apply REFD in GET'.
            rewrite GET' in AGET. congruence.
      }
      { rewrite GET'.
        unfold refine_sc in *. unfold RefinementAS.refine_syscalls in ref_sc_correct.
        assert (CALLDOMAINS := RefinementAS.refine_syscalls_domains ref_sc_correct).
        assert (EGETCALL: exists ac, Abs.get_syscall atable spc = Some ac)
          by (eexists; eauto).
        apply CALLDOMAINS in EGETCALL.
        destruct EGETCALL as [sc GETCALL'].
        rewrite GETCALL'. reflexivity.
      }
    - destruct (get dmem spc); discriminate.
Qed.

Theorem cfg_false_equiv asi asj ssi ssj :
  RefinementAS.refine_state stable asi ssi ->
  RefinementAS.refine_state stable asj ssj ->
  ~~ Abs.succ atable cfg asi asj ->
  Symbolic.step stable ssi ssj ->
  ~~ Sym.ssucc stable ssi ssj.
Proof.
  intros REF REF' ASUCC SSTEP.
  unfold Abs.succ in ASUCC.
  destruct asi as [imem dmem aregs apc b],
           asj as [imem' dmem' aregs' apc' b'].
  destruct ssi as [mem reg [pc tpc] int].
  destruct ssj as [mem' reg' [pc' tpc'] int'].
  destruct REF as [REFI [REFD [REFR [REFPC [? [? [ITG [VTG [ETG ?]]]]]]]]],
           REF' as [REFI' [REFD' [REFR' [REFPC' CORRECT']]]].
  unfold RefinementAS.refine_pc in *.
  simpl in REFPC; simpl in REFPC'; destruct REFPC as [? TPC],
                                            REFPC' as [? TPC'].
  subst.
  unfold Sym.ssucc.
  destruct (get imem pc) as [s|] eqn:GET.
  { apply REFI in GET.
    destruct GET as [id GET].
    destruct (decode_instr s) eqn:INST.
    { destruct i;
      simpl; rewrite GET; simpl; rewrite INST; destruct id; auto;
      unfold Abs.valid_jmp, valid_jmp in ASUCC;
      destruct (get mem pc') as [[v [[id|]|]]|] eqn:GET';
      rewrite GET';
      try match goal with
        | [|- is_true (~~ match Symbolic.get_syscall _ _ with _ => _ end)] =>
          destruct (Symbolic.get_syscall stable pc') eqn:?
      end;
      repeat match goal with
               | [H: ?Expr = _ |- context[?Expr]] =>
                 rewrite H; simpl
               | [H: is_true ?Expr |- context[?Expr] ] =>
                 rewrite H
               | [|- is_true (~~ match Symbolic.entry_tag ?S with _ => _ end)] =>
                 destruct (Symbolic.entry_tag S) as [[?|]|] eqn:?
             end;
      repeat match goal with
               | [H: get _ _ = Some _@(INSTR (Some _)) |- _] =>
                 apply ITG in H
               | [H: get _ ?Addr = None,
                  H1: Symbolic.get_syscall _ ?Addr = Some _,
                  H2: Symbolic.entry_tag _ = INSTR (Some _) |- _] =>
                 apply (ETG _ _ _ H H1) in H2
               | [H: context[?Expr], H1: ?Expr = _ |- _] =>
                 rewrite H1 in H
             end; by auto.
    }
    { simpl. rewrite GET. rewrite INST. destruct id; by reflexivity. }
  }
  { destruct (Abs.get_syscall atable pc) eqn:GETCALL.
    { simpl.
      destruct (get dmem pc) eqn:GET'.
      { apply REFD in GET'. rewrite GET'. reflexivity. }
      { discriminate. }
    }
    { simpl.
      destruct (get mem pc) eqn:GET'.
      { destruct a. destruct tag.
        { assert (EGET' : exists id, get mem pc = Some val@(INSTR id))
               by (eexists; eauto).
          apply REFI in EGET'. congruence.
        }
        { rewrite GET'. reflexivity. }
      }
      { rewrite GET'.
        assert (SCDOMAINS := RefinementAS.refine_syscalls_domains ref_sc_correct).
        apply RefinementAS.same_domain_total with (addr' := pc) in SCDOMAINS.
        apply SCDOMAINS in GETCALL. rewrite GETCALL. reflexivity.
      }
    }
  }
Qed.

Program Instance cfi_refinementAS  :
  (machine_refinement amachine smachine) := {
    refine_state st st' := RefinementAS.refine_state stable st st';

    check st st' := true
}.
Next Obligation.
  split;
  [intros;
    destruct (backwards_simulation syscall_preserves_register_tags
                                   syscall_preserves_jump_tags
                                   syscall_preserves_jal_tags _ REF STEP)
    as [? [? ?]];
   eexists; split; eauto | discriminate].
Qed.
Next Obligation.
  destruct (RefinementAS.backwards_simulation_attacker stable ast REF STEPA);
  eexists; eauto.
Qed.

Import ListNotations.

Program Instance cfi_refinementAS_specs :
  machine_refinement_specs cfi_refinementAS.
Next Obligation.
  by case: (stepP' stable cst cst') => [H | H]; auto.
Qed.
Next Obligation. (*initial state*)
  destruct H as [TPC [ITG [VTG [ETG [RTG ?]]]]].
  destruct cst as [mem reg [pc tpc] int].
  exists (Abs.State (PartMaps.map RefinementAS.untag_atom (filter is_instr mem))
                    (PartMaps.map RefinementAS.untag_atom (filter RefinementAS.is_data mem))
                    (PartMaps.map RefinementAS.untag_atom reg) pc true).
  split.
  - unfold Abs.initial. reflexivity.
  - unfold RefinementAS.refine_state. repeat (split; eauto).
    intros ? ? TPC'.
    simpl in TPC. rewrite TPC in TPC'; congruence.
    intros ? ? TPC'. simpl in TPC. rewrite TPC in TPC'.
    congruence.
Qed.
Next Obligation.
  apply (introTF idP).
  have [?|?] := boolP (Abs.succ atable cfg asi asj).
  - by eauto using cfg_true_equiv.
  - apply/negP. by eauto using cfg_false_equiv.
Qed.
Next Obligation.
  destruct (Abs.step_succ_violation H0 H1) as [H2 H3].
  intro CONTRA. assert (CONT := Abs.step_a_violation CONTRA).
  by rewrite -CONT H2 in H3.
Qed.
Next Obligation.
  unfold Abs.stopping in H4.
  unfold Sym.stopping.
  destruct H4 as [ALLA ALLS].
  induction H3
    as [ast cst REF | ast cst cst' axs' cxs' STEP VIS REF REF' RTRACE' |
        ast ast' cst cst' axs' cxs' STEP ASTEP' REF REF' RTRACE'|
        ast ast' cst cst' axs' cxs' NSTEP STEP ASTEP' REF REF' RTRACE'];
    subst.
  - split.
    + intros csi' csj' CONTRA.
      destruct CONTRA.
    + intros csi' IN.
      destruct IN as [? | CONTRA]; subst.
      * intros (? & CONTRA).
        destruct (backwards_refinement_normal _ _ _ REF CONTRA) as [VIS CLEAN].
        clear CLEAN.
        unfold check in VIS. simpl in VIS.
        destruct (VIS erefl) as [ast' [ASTEP REF']].
        unfold Abs.all_stuck in ALLS.
        assert (IN: In ast [ast]) by (simpl; auto).
        apply ALLS in IN.
        eauto.
      * destruct CONTRA.
  - simpl in *.
    discriminate.
  - simpl in *.
    assert (IN: In ast (ast :: ast' :: axs')) by (simpl; auto).
    apply ALLS in IN.
    exfalso.
    eauto.
  - apply Abs.all_attacker_red in ALLA.
    split.
    { apply Abs.all_stuck_red in ALLS.
      exploit IHRTRACE'; auto.
      intros [IH IH'];
      simpl in *; eauto using Sym.all_attacker_step.
    }
    { intros csi' IN.
      destruct IN as [? | IN]; subst.
      - intros (? & CONTRA).
        destruct (backwards_refinement_normal _ _ _ REF CONTRA) as [CONTRA' H'].
        clear H'.
        simpl in CONTRA'.
        destruct (CONTRA' erefl) as [ast'' [ASTEP REF'']].
        assert (IN: In ast (ast :: ast' :: axs'))
          by (simpl; auto).
        specialize (ALLS ast IN).
        eauto.
      - exploit IHRTRACE'; auto.
        apply Abs.all_stuck_red in ALLS.
        assumption.
        intros [? STUCK].
        specialize (STUCK csi' IN).
        assumption.
    }
Qed.

End Refinement.
