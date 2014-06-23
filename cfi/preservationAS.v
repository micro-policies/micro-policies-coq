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
        {opss : machine_ops_spec ops}
        
        {ap : Abs.abstract_params t}
        {aps : Abs.params_spec ap}

        {smemory : Type}
        {sm : partial_map smemory (word t) (atom (word t) (@cfi_tag t))}
        {smems : axioms sm}
        {smemory_map : Map.mappable sm (@Abs.dmem_class t ap)}
        {smemory_filter : Filter.filterable sm}

        {sregisters : Type}
        {sr : partial_map sregisters (reg t) (atom (word t) (@cfi_tag t))}
        {sregs : axioms sr}
        {sregs_map : Map.mappable sr (@Abs.reg_class t ap)}.

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

Hypothesis syscalls_backwards_simulation :
  forall ast sst addr sc sst',
    refine_sc ->
    Symbolic.get_syscall stable addr = Some sc ->
    RefinementAS.refine_state stable ast sst ->
    Symbolic.run_syscall sc sst = Some sst' ->
    exists ac ast',
      Abs.get_syscall atable addr = Some ac /\
      Abs.sem ac ast = Some ast' /\
      RefinementAS.refine_state stable ast' sst'.

Hypothesis syscall_sem :
  forall ac ast ast',
    Abs.sem ac ast = Some ast' ->
       let '(imem,dmem,aregs,pc,b) := ast in
       let '(imem',dmem',aregs',pc',b') := ast' in
         imem = imem' /\ b' = b.

Hypothesis jump_tagged :
  forall pc i (mem : @Symbolic.memory t sym_params) r itg,
    get mem pc = Some i@(INSTR itg) ->
    decode_instr i = Some (Jump _ r) ->
    itg = Some pc.

Hypothesis jal_tagged :
  forall pc i (mem : @Symbolic.memory t sym_params) r itg,
    get mem pc = Some i@(INSTR itg) ->
    decode_instr i = Some (Jal _ r) ->
    itg = Some pc.

Hypothesis jump_target_tagged :
  forall pc w (mem : @Symbolic.memory t sym_params) i i0 id r reg 
         (tr ti : @Symbolic.tag t sym_params),
    get mem pc = Some i@(INSTR (Some id)) ->
    decode_instr i = Some (Jump _ r) ->
    get reg r = Some w@tr ->
    get mem w = Some i0@ti ->
    ti = INSTR (Some w).

Hypothesis jal_target_tagged :
  forall pc w (mem : @Symbolic.memory t sym_params) i i0 id r reg 
         (tr ti : @Symbolic.tag t sym_params),
    get mem pc = Some i@(INSTR (Some id)) ->
    decode_instr i = Some (Jal _ r) ->
    get reg r = Some w@tr ->
    get mem w = Some i0@ti ->
    ti = INSTR (Some w).

Hypothesis jump_entry_tagged :
  forall pc w (mem : @Symbolic.memory t sym_params) i id r reg sc
         (tr : @Symbolic.tag t sym_params),
    get mem pc = Some i@(INSTR (Some id)) ->
    decode_instr i = Some (Jump _ r) ->
    get reg r = Some w@tr ->
    get mem w = None ->
    Symbolic.get_syscall stable w = Some sc ->
    (Symbolic.entry_tag sc) = INSTR (Some w).

Hypothesis jal_entry_tagged :
  forall pc w (mem : @Symbolic.memory t sym_params) i id r reg sc
         (tr : @Symbolic.tag t sym_params),
    get mem pc = Some i@(INSTR (Some id)) ->
    decode_instr i = Some (Jal _ r) ->
    get reg r = Some w@tr ->
    get mem w = None ->
    Symbolic.get_syscall stable w = Some sc ->
    (Symbolic.entry_tag sc) = INSTR (Some w).


Definition backwards_simulation := 
  RefinementAS.backwards_simulation ref_sc_correct syscalls_backwards_simulation
                                    syscall_sem jump_tagged jal_tagged
                                    jump_target_tagged jal_target_tagged
                                    jump_entry_tagged jal_entry_tagged.

Program Instance cfi_refinementAS  : 
  (@machine_refinement t amachine smachine) := {
    refine_state st st' := RefinementAS.refine_state stable st st';

    visible st st' := true
}.
Next Obligation.
  split; 
  [intros; 
    destruct (backwards_simulation _ REF STEP) 
    as [? [? ?]];
   eexists; split; eauto | discriminate].
Qed.
Next Obligation.
  destruct (RefinementAS.backwards_simulation_attacker stable ast REF STEPA);
  eexists; eauto.
Qed.
  
Definition astop (xs : list (@property.state t amachine)) :=
  Abs.S atable valid_jmp xs.

Definition sstop (xs : list (@property.state t smachine)) := 
  Sym.S stable xs.

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

Import ListNotations.

Require Import Classical.

Program Instance cfi_refinementAS_specs :
  machine_refinement_specs astop sstop cfi_refinementAS.
Next Obligation. (*step or no step*)
  by apply classic. Qed.
Next Obligation. (*initial state*)
  Admitted. (* TODO: using map/filter mechanism now used for attacker *)
Next Obligation.
  destruct asi as [[[[imem dmem] aregs] apc] b], 
           asj as [[[[imem' dmem'] aregs'] apc'] b'].
  destruct csi as [mem regs [spc tpc] int].
  destruct csj as [mem' regs' [spc' tpc'] int'].
  destruct H as [REFI [REFD [REFR [REFPC CORRECTNESS]]]].
  destruct H0 as [REFI' [REFD' [REFR' [REFPC' CORRECTNESS']]]].
  unfold Abs.succ in H1.
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
        unfold refine_sc in *. 
        destruct ref_sc_correct as [CALLDOMAINS ?].
        assert (EGETCALL: exists ac, Abs.get_syscall atable spc = Some ac)
          by (eexists; eauto).
        apply CALLDOMAINS in EGETCALL.
        destruct EGETCALL as [sc GETCALL'].
        rewrite GETCALL'. reflexivity.
      }
    - destruct (get dmem spc); discriminate.
Qed.
Next Obligation.
  assert (ST := Abs.step_succ_violation H H0).
  intro CONTRA.
  destruct CONTRA. discriminate.
Qed.
Next Obligation.
  unfold Abs.succ in H1. 
  destruct ast as [[[[imem dmem] aregs] apc] b],
           ast' as [[[[imem' dmem'] aregs'] apc'] b'].
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
        destruct ref_sc_correct as [SCDOMAINS ?].
        apply RefinementAS.same_domain_total with (addr' := pc) in SCDOMAINS.
        apply SCDOMAINS in GETCALL. rewrite GETCALL. reflexivity.
      }
    }
  }
Qed.
Next Obligation.
  unfold astop in H0. unfold Abs.S in H0.
  unfold sstop. unfold Sym.S.
  destruct H0 as [s [EQ NOSTEP]].
  inversion EQ; subst.
  inversion H; subst.
  - exists cst. split; auto.
    intro CONTRA. destruct CONTRA as [s' CONTRA].
    destruct (backwards_refinement_normal _ _ _ H2 CONTRA).
    unfold visible in H1. simpl in H1.
    destruct (H1 erefl) as [ast' [ASTEP REF]].
    assert (ESTEP : exists s', Abs.step atable valid_jmp s s')
      by (eexists; eauto).
    auto.
  - unfold visible in H4. simpl in H4. discriminate.
Qed.
        
End Refinement.