Require Import Coq.Lists.List.
Require Import lib.utils.
Require Import lib.partial_maps.
Require Import lib.Coqlib.
Require Import common.common.
Require Import symbolic.symbolic.
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
        {opss : machine_ops_spec ops}.

Variable valid_jmp : word t -> word t -> bool.

Definition sym_params := Sym.sym_cfi valid_jmp.

Variable atable : list (Abs.syscall t).
Variable stable : list (@Symbolic.syscall t sym_params).

Definition amachine :=  Abs.abstract_cfi_machine atable valid_jmp.
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
    Sym.instructions_tagged valid_jmp (Symbolic.mem st) ->
    Symbolic.sem sc st = Some st' ->
    Sym.instructions_tagged valid_jmp (Symbolic.mem st').

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


Definition backwards_simulation := 
  RefinementAS.backwards_simulation ref_sc_correct syscall_sem 
                                    syscall_preserves_instruction_tags 
                                    syscall_preserves_valid_jmp_tags
                                    syscall_preserves_entry_tags.

(* For initial states - may need to think a bit about how to structure 
   the whole thing*)
Lemma untag_implies_reg_refinement reg :
  RefinementAS.refine_registers valid_jmp (PartMaps.map RefinementAS.untag_atom reg) reg.
Proof.
   intros r v.
   split.
   - intros (ut & GET).
     rewrite PartMaps.map_correctness.
     rewrite GET. reflexivity.
   - intros GET.
     rewrite PartMaps.map_correctness in GET.
     destruct (get reg r) eqn:GET'; rewrite GET'.
     + destruct a. simpl in GET. inv GET.
       eexists; reflexivity.
     + simpl in GET. congruence.
Qed.

Lemma untag_data_implies_dmem_refinement mem :
  RefinementAS.refine_dmemory valid_jmp
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
     destruct (get mem addr) eqn:GET'; rewrite GET'.
     + destruct a as [val tg]. 
       simpl in GET.
       destruct tg as [[id|]|]; simpl in GET.
       * congruence.
       * congruence.
       * inv GET. reflexivity.
     + simpl in GET. congruence.
Qed.

Definition is_instr (a : atom (word t) (@cfi_tag t)) := 
  match common.tag a with
    | INSTR _ => true
    | DATA => false
  end.

Lemma untag_instr_implies_imem_refinement mem :
  RefinementAS.refine_imemory valid_jmp
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
     destruct (get mem addr) eqn:GET'; rewrite GET'.
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

Program Instance cfi_refinementAS  : 
  (machine_refinement amachine smachine) := {
    refine_state st st' := RefinementAS.refine_state stable st st';

    check st st' := true
}.
Next Obligation.
  split; 
  [intros; 
    destruct (backwards_simulation _ REF STEP) 
    as [? [? ?]];
   eexists; split; eauto | discriminate].
Qed.
Next Obligation.
  destruct (RefinementAS.backwards_simulation_attacker ast REF STEPA);
  eexists; eauto.
Qed.

Import ListNotations.

Require Import Classical.

Program Instance cfi_refinementAS_specs :
  machine_refinement_specs cfi_refinementAS.
Next Obligation. (*step or no step*)
  by apply classic. 
Qed.
Next Obligation. (*initial state*)
  destruct H as [TPC [ITG [VTG ETG]]].
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
  destruct asi as [imem dmem aregs apc b], 
           asj as [imem' dmem' aregs' apc' b'].
  destruct csi as [mem regs [spc tpc] int].
  destruct csj as [mem' regs' [spc' tpc'] int'].
  destruct H as [REFI [REFD [REFR [REFPC ?]]]].
  destruct H0 as [REFI' [REFD' [REFR' [REFPC' ?]]]].
  unfold Abs.succ in H2.
  unfold RefinementAS.refine_pc in REFPC; simpl in REFPC; 
  destruct REFPC as [? TPC];
  unfold RefinementAS.refine_pc in REFPC'; simpl in REFPC'; 
  destruct REFPC' as [? TPC'];
  subst.
  unfold Sym.ssucc; simpl.
  destruct (get imem spc) eqn:GET.
  + destruct (decode_instr s) eqn:INST.
    - destruct i eqn:DECODE;
      apply REFI in GET;
      destruct GET as [id GET'];
      rewrite GET'; simpl;
      rewrite INST; try assumption. 
    - discriminate.
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
Next Obligation.
  assert (ST := Abs.step_succ_violation H0 H1).
  intro CONTRA.
  destruct CONTRA. discriminate.
Qed.
Next Obligation.
  unfold Abs.succ in H1. 
  destruct ast as [imem dmem aregs apc b],
           ast' as [imem' dmem' aregs' apc' b'].
  destruct cst as [mem reg [pc tpc] int].
  destruct cst' as [mem' reg' [pc' tpc'] int'].
  destruct H as [REFI [REFD [REFR [REFPC CORRECT]]]],
           H0 as [REFI' [REFD' [REFR' [REFPC' CORRECT']]]].
  unfold RefinementAS.refine_pc in *.
  simpl in REFPC; simpl in REFPC'; destruct REFPC as [? TPC],
                                            REFPC' as [? TPC'].
  subst.
  unfold Sym.ssucc.    
  destruct (get imem pc) eqn:GET.
  { apply REFI in GET.
    destruct GET as [id GET].
    destruct (decode_instr s) eqn:INST.
    { destruct i;
      simpl; rewrite GET; simpl; rewrite INST; auto. 
    }
    { simpl. rewrite GET. rewrite INST. assumption. }
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
Next Obligation.
  unfold Abs.stopping in H4.
  unfold Sym.stopping.
  destruct H4 as [s [EQ NOSTEP]].
  inversion EQ; subst.
  inversion H3; subst.
  - exists csj. split; auto.
    intro CONTRA. destruct CONTRA as [s' CONTRA].
    destruct (backwards_refinement_normal _ _ _ H6 CONTRA).
    unfold check in H4. simpl in H4.
    destruct (H4 erefl) as [ast' [ASTEP REF]].
    assert (ESTEP : exists s', Abs.step atable valid_jmp s s')
      by (eexists; eauto).
    auto.
  - unfold check in H9. simpl in H9. discriminate.
Qed.
        
End Refinement.
