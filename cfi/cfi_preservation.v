Require Import common.common.
Require Import lib.utils.
Require Import cfi.cfi.
Require Import cfi.cfi_refinement.

Set Implicit Arguments.

Section Preservation.

Context {mt : machine_types}
        {ops : machine_ops mt}
        {opss : machine_ops_spec ops}.

Variable machine1 : cfi_machine mt.
Variable machine2 : cfi_machine mt.
Variable S1 : (list (@state mt machine1)) -> Prop.

Variable S2 : (list (@state mt machine2)) -> Prop.

Context {rf : machine_refinement machine1 machine2}.
Context {rfs : machine_refinement_specs S1 S2 rf}.

Theorem backwards_refinement_preserves_cfi :

  cfi machine1 S1 ->
  cfi machine2 S2. 
Proof. Admitted.
(*
 intros CFI1 cst cst' cxs INIT2 INTERM2.
  destruct (initial_refine cst INIT2) as [ast [INIT1 INITREF]].
  destruct (backwards_refinement_with_v _ _ INITREF INTERM2) 
    as [axs [[ast' INTERMR1] [INTSTATES HSPLIT]]].
  destruct (intermr_implies_interm INTERMR1) as [INTERM1 | [EQ LST]].
  { (*machine1  steps*)
    destruct (CFI1 ast ast' axs INIT1 INTERM1) as [TSAFE1 | VIOLATED].
    - (*machine1 has CFI at all steps*)
      unfold trace_has_cfi in TSAFE1.
      left. intros csi csj IN2 STEPN2.
      destruct (visible csi csj) eqn:VISIBLE.
      + (*case it's a visible step*)
        destruct (INTSTATES _ _ IN2 STEPN2 VISIBLE) 
          as [asi [asj [IN2' [STEPN1 [REFI REFJ]]]]].
        assert (SUCC := TSAFE1 asi asj IN2' STEPN1).
        apply (cfg_equiv asi asj csi csj REFI REFJ SUCC).
      + (*case it's an invisible step*)
        apply (cfg_invisible _ _ STEPN2 VISIBLE).
         apply (cfg_kernel _ _ STEPN2 VISIBLE).
     - destruct VIOLATED 
         as [asi [asj [ahs [atl [ALST [[ASTEP AV] [TSAFE1 [TSAFE2 STOP1]]]]]]]].
       right. 
       destruct (HSPLIT _ _ _ _ ALST ASTEP) 
         as [csi [csj [chs [ctl [REFI [REFJ [CLST [STEP2 [INTHEAD INTTAIL]]]]]]]]].
       exists csi; exists csj; exists chs; exists ctl.
       split; auto.
       split. split; [assumption | eapply av_implies_cv; eauto].
       split.
       {(*cfi for head trace*)
        intros csi' csj' IN2 STEP2'.
        destruct (visible csi' csj') eqn:VIS.
        - destruct (INTHEAD _ _ IN2 STEP2' VIS) 
            as [asi' [asj' [IN2' [ASTEP' [REFI' REFJ']]]]].
          assert (SUCC := TSAFE1 _ _ IN2' ASTEP').
          apply (cfg_equiv1 _ _ _ _ REFI' REFJ' SUCC). 
        - apply (cfg_kernel _ _ STEP2' VIS).
       }
       { split.
         + (*cfi for tail trace*)
           intros csi' csj' IN2 STEP2'.
           destruct (visible csi' csj') eqn:VIS.
           - destruct (INTTAIL _ _ IN2 STEP2' VIS) 
             as [asi' [asj' [IN2' [ASTEP' [REFI' REFJ']]]]].
             assert (SUCC := TSAFE2 _ _ IN2' ASTEP').
             apply (cfg_equiv1 _ _ _ _ REFI' REFJ' SUCC). 
           - apply (cfg_kernel _ _ STEP2' VIS).
         + eapply as_implies_cs; eauto.
       }
  }
  { (*machine1 doesn't step at all*)
    subst.
    left.
    intros csi csj IN2 STEP2.
    destruct (visible csi csj) eqn:VIS.
    - (*case the step is visible - contradiction*)
      destruct (INTSTATES _ _ IN2 STEP2 VIS) as [? [? [CONTRA ?]]].
      destruct CONTRA.
    - (*case the step is invisible*)
      apply (cfg_kernel _ _ STEP2 VIS).
  }
Qed.
*)
End Preservation.

