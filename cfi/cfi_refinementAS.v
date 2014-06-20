Require Import cfi.cfi_refinement.
Require Import cfi.abstract.
Require Import cfi.symbolic.
Require Import cfi.refinementAS.
Require Import cfi.cfi_rules.
Require Import symbolic.symbolic.
Require Import common.common.
Require Import lib.utils.
Require Import lib.partial_maps.
Require Import lib.Coqlib.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Set Implicit Arguments.

Import PartMaps.
 
Section Refinement.

Context {t : machine_types}
        {ops : machine_ops t}
        {opss : machine_ops_spec ops}
        
        {ap : Abstract.abstract_params t}
        {aps : Abstract.params_spec ap}

        {smemory : Type}
        {sm : partial_map smemory (word t) (atom (word t) (@cfi_tag t))}
        {smems : axioms sm}
        {smemory_map : Map.mappable sm (@Abstract.dmem_class t ap)}
        {smemory_filter : Filter.filterable sm}

        {sregisters : Type}
        {sr : partial_map sregisters (reg t) (atom (word t) (@cfi_tag t))}
        {sregs : axioms sr}
        {sregs_map : Map.mappable sr (@Abstract.reg_class t ap)}.

Variable valid_jmp : word t -> word t -> bool.

Definition sym_params := SymbolicCFI.sym_cfi valid_jmp.

Variable atable : list (Abstract.syscall t).
Variable stable : list (@Symbolic.syscall t sym_params).

Definition amachine :=  Abstract.abstract_cfi_machine atable valid_jmp.
Definition smachine := SymbolicCFI.symbolic_cfi_machine stable.

Program Instance cfi_refinementAS  : 
  (@machine_refinement t amachine smachine) := {
    refine_state st st' := RefinementAS.refine_state st st';

    visible st st' := true
}.
Next Obligation.
  split; 
  [intros; destruct (RefinementAS.backwards_simulation atable ast REF STEP) 
    as [? [? ?]];
   eexists; split; eauto | discriminate].
Qed.
Next Obligation.
  destruct (RefinementAS.backwards_simulation_attacker ast REF STEPA);
  eexists; eauto.
Qed.
  
Definition astop (xs : list (@cfi.state t amachine)) := Abstract.S atable valid_jmp xs.

Definition sstop (xs : list (@cfi.state t smachine)) := 
  SymbolicCFI.S stable xs.

Hypothesis refine_syscalls_correct : RefinementAS.refine_syscalls atable stable.

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

Program Instance cfi_refinementAS_specs :
  machine_refinement_specs astop sstop cfi_refinementAS.
Next Obligation. (*step or no step*)
  Admitted.
Next Obligation. (*initial state*)
  Admitted.
Next Obligation.
  destruct asi as [[[[imem dmem] aregs] apc] b], 
           asj as [[[[imem' dmem'] aregs'] apc'] b'].
  destruct csi as [mem regs [spc tpc] int].
  destruct csj as [mem' regs' [spc' tpc'] int'].
  destruct H as [REFI [REFD [REFR [REFPC CORRECTNESS]]]].
  destruct H0 as [REFI' [REFD' [REFR' [REFPC' CORRECTNESS']]]].
  unfold Abstract.succ in H1.
  unfold RefinementAS.refine_pc in REFPC; simpl in REFPC; 
  destruct REFPC as [? TPC];
  unfold RefinementAS.refine_pc in REFPC'; simpl in REFPC'; 
  destruct REFPC' as [? TPC'];
  subst.
  unfold SymbolicCFI.ssucc; simpl.
  destruct (get imem spc) eqn:GET.
  + destruct (decode_instr s) eqn:INST.
    - destruct i eqn:DECODE;
      apply REFI in GET;
      destruct GET as [id GET'];
      rewrite GET'; simpl;
      rewrite INST; try assumption. 
      (*syscall case*)
  (* + discriminate. *)
Admitted.
Next Obligation.
  assert (ST := Abstract.step_succ_violation H H0).
  intro CONTRA.
  destruct CONTRA. discriminate.
Qed.
Next Obligation.
  unfold Abstract.succ in H1.
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
  unfold SymbolicCFI.ssucc.    
  destruct (get imem pc) eqn:GET.
  { apply REFI in GET.
    destruct GET as [id GET].
    destruct (decode_instr s) eqn:INST.
    { destruct i;
      simpl; rewrite GET; simpl; rewrite INST; auto. 
    }
    { simpl. rewrite GET. rewrite INST. assumption. }
  }
  { destruct (Abstract.get_syscall atable pc) eqn:GETCALL.
    { discriminate. }
    { simpl. 
      destruct (get mem pc) eqn:GET'.
      { destruct a. destruct tag.
        { assert (EGET' : exists id, get mem pc = Some val@(INSTR id)) 
               by (eexists; eauto). 
          apply REFI in EGET'. congruence.
        }
        { rewrite GET'. reflexivity. } 
      } rewrite GET'. reflexivity. }
  }
Qed.
Next Obligation.
  unfold astop in H0. unfold Abstract.S in H0.
  unfold sstop. unfold SymbolicCFI.S.
  destruct H0 as [s [EQ NOSTEP]].
  inversion EQ; subst.
  inversion H; subst.
  - exists cst. split; auto.
    intro CONTRA. destruct CONTRA as [s' CONTRA].
    destruct (backwards_refinement_normal _ _ _ H2 CONTRA).
Admitted. (*stuck?*)
        
End Refinement.