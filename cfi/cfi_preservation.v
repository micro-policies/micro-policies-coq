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
Variable V1 : (@state mt machine1) -> (@state mt machine1) -> Prop.
Variable S1 : (list (@state mt machine1)) -> Prop.

Variable V2 : (@state mt machine2) -> (@state mt machine2) -> Prop.
Variable S2 : (list (@state mt machine2)) -> Prop.

Context {rf : machine_refinement machine1 machine2}.
Context {rfs : machine_refinement_specs V1 S1 V2 S2 rf}.

Theorem backwards_refinement_preserves_cfi :
  cfi machine1 V1 S1 ->
  cfi machine2 V2 S2. 
Proof.
  intros CFI1 cst cst' cxs INIT2 INTERM2.
  destruct (initial_refine cst INIT2) as [ast [INIT1 INITREF]].
(*
  destruct (backwards_refinement _ _ INITREF INTERM2) 
    as [ast' [axs [INTERMR1 [FINALREF INTSTATES]]]].
  destruct (intermr_implies_interm INTERMR1) as [INTERM1 | [EQ LST]].
  { (*machine1  steps*)
    destruct (CFI1 ast ast' axs INIT1 INTERM1) as [TSAFE1 | VIOLATED].
    - (*machine1 has CFI at all steps*)
      unfold trace_has_cfi in TSAFE1.
      left. intros csi csj IN2 STEPN2.
      destruct (visible csi csj) eqn:VISIBLE.
      + (*case it's a visible step*)
        destruct (INTSTATES _ _ IN2 STEPN2 VISIBLE) as [asi [asj [IN2' [STEPN1 [REFI REFJ]]]]].
        assert (SUCC := TSAFE1 asi asj IN2' STEPN1).
        apply (cfg_equiv asi asj csi csj REFI REFJ SUCC).
      + (*case it's an invisible step*)
         apply (cfg_invisible _ _ STEPN2 VISIBLE).
   - 
        

*)
Admitted. 
  (*
  intros CFI1 cst cst' cxs INIT2 INTERM2.
  destruct (initial_refine cst INIT2) as [ast [INIT1 INITREF]].
  destruct (backwards_refinement' rf ast INITREF INTERM2) 
    as [ast' [axs [INTERMR1 [FINALREF [INTSTATES SPLITS]]]]].
  destruct (intermr_implies_interm INTERMR1) as [INTERM1 | [EQ LST]].
  + (* machine1 steps*)
    destruct (CFI1 ast ast' axs INIT1 INTERM1) as [TSAFE1 | H].
    - (*machine1 has CFI at all steps*)
      unfold trace_has_cfi in TSAFE1.
      left.
      intros csi csj IN2.
      destruct (INTSTATES csi csj IN2) as [asi [asj [IN2' [REFI REFJ]]]].
      destruct IN2' as [[VISIBLE IN2'] | [INVISIBLE  [EQ IN]]].
      * (*case it's a visible STEP and In2 for machine1 is true*)
        destruct (TSAFE1 asi asj IN2') as [[STEPA ?] | SUCC].
        { left; split; [idtac | apply attacker_pc]; eapply astep_implies_cstep; eauto. }
        { assert (STEP1: cfi_step machine1 asi asj) by (eapply interm_in2_step; eauto).
          destruct STEP1 as [STEPA | STEPN].
          - left.
            eapply astep_implies_cstep in STEPA; eauto.
            split; [assumption | erewrite attacker_pc; eauto].
          - right. apply (cfg_equiv asi asj csi csj REFI REFJ STEPN SUCC). }
      * (*case it's an invisible STEP*)
        subst.
        assert (STEP2: cfi_step machine2 csi csj) by (eapply interm_in2_step; eauto).
        destruct STEP2 as [? | STEPN2].
        left; erewrite attacker_pc; eauto.
        destruct (cfg_invisible asj csi csj STEPN2 INVISIBLE); auto.
    - (*machine1 has a violation*)
      destruct H as [asi [asj [ahs [atl [TRACE [VIOLATES1 [CFIH [CFIT STOPS1]]]]]]]].
      destruct (SPLITS asi asj ahs atl TRACE) as [csi [csj [chs [ctl [REFI [REFJ [CTRACE [INTHEAD INTAIL]]]]]]]].
      right.
      exists csi; exists csj; exists chs; exists ctl.
      split. assumption.
      split. 
      eapply av_implies_cv; eauto.
      split.
      { (* trace_has_cfi chs++[csi] *)
        intros csi' csj' IN2. 
        destruct (INTHEAD csi' csj' IN2) as [asi' [asj' [IN2' [REFI' REFJ']]]].
        destruct IN2' as [[VISIBLE IN2'] | [INVISIBLE  [EQ IN]]].
        * (*machine2 takes a visible step*)
          destruct (CFIH asi' asj' IN2') as [[STEPA ?] | SUCC]. 
          { left; split; [idtac | apply attacker_pc]; eapply astep_implies_cstep; eauto. }
          { assert (STEP1: cfi_step machine1 asi' asj'). 
            { eapply interm_in2_step. eauto. rewrite TRACE. 
              replace (ahs ++ asi :: asj :: atl) with ((ahs++[asi])++asj::atl). 
              apply in2_strengthen'. assumption.
              simpl; rewrite <- app_assoc; reflexivity. }
            destruct STEP1 as [STEPA | STEPN]; 
              [ left; erewrite attacker_pc; eapply astep_implies_cstep in STEPA; eauto |
                right; apply (cfg_equiv asi' asj' csi' csj' REFI' REFJ' STEPN); assumption ].
          }
        * (*machine2 takes an invisible step*)
          subst.
          assert (STEP2: cfi_step machine2 csi' csj').
          { eapply interm_in2_step in INTERM2.
            eauto. replace (chs ++ csi :: csj :: ctl) with ((chs ++ [csi]) ++ (csj :: ctl)).
            apply in2_strengthen'. assumption.
            rewrite <- app_assoc. reflexivity.
          }
          destruct STEP2 as [STEPA | STEPN].
          { left; split; [idtac | apply attacker_pc]; eauto. }
          { right; eapply cfg_invisible; eauto. }
      }
      { (*trace has cfi csj :: ctl and will halt *)
        split.
        + (*tail has cfi*)
          intros csi' csj' IN2.
          destruct (INTAIL csi' csj' IN2) as [asi' [asj' [IN2' [REFI' REFJ']]]].
          destruct IN2' as [[VISIBLE IN2'] | [INVISIBLE  [EQ IN]]].
          - (*visible step*)
            destruct (CFIT asi' asj' IN2') as [[STEPA ?] | SUCC].
            * left; split; [idtac | apply attacker_pc]; eapply astep_implies_cstep; eauto.
            * assert (STEP1: cfi_step machine1 asi' asj').
              { eapply interm_in2_step; eauto. rewrite TRACE.
                apply in2_strengthen with (ys := (ahs ++ [asi])) in IN2'.
                rewrite <- app_assoc in IN2'; auto.
              }
              destruct STEP1 as [STEPA | STEPN];
              [ left; erewrite attacker_pc; eapply astep_implies_cstep in STEPA; eauto |
                right; apply (cfg_equiv asi' asj' csi' csj' REFI' REFJ' STEPN); assumption ].
          - (*invisible step*)
            subst.
            assert (STEP2: cfi_step machine2 csi' csj').
            { eapply interm_in2_step in INTERM2.
              eauto. replace (chs ++ csi :: csj :: ctl) with ((chs ++ [csi]) ++ (csj :: ctl)).
              apply in2_strengthen. assumption.
              rewrite <- app_assoc. reflexivity.
            }
            destruct STEP2 as [STEPA | STEPN].
            { left; split; [idtac | apply attacker_pc]; eauto. }
            { right; eapply cfg_invisible; eauto. }
         + eapply as_implies_cs; eauto.
     }
  + (* machine1 doesn't step at all*)   
    subst. left.
    intros csi csj IN2.
    destruct (INTSTATES csi csj IN2) as [asi [asj [IN2' [REFI REFJ]]]].
    destruct IN2' as [[VISIBLE IN2'] | [INVISIBLE  [EQ IN]]].
    * (*case machine1 takes a step*)
      destruct IN2'.
    * (*case machine1 does not take a step*)
      subst.
      destruct (interm_in2_step INTERM2 IN2).
      - left; erewrite attacker_pc; eauto.
      - right; eapply cfg_invisible; eauto.*)

(*
Theorem backwards_refinement_preserves_cfi :
  cfi machine1 V1 S1 ->
  cfi machine2 V2 S2. 
Proof.
  intros CFI1 cst cst' cxs INIT2 INTERM2.
  destruct (initial_refine cst INIT2) as [ast [INIT1 INITREF]].
  destruct (backwards_refinement' rf ast INITREF INTERM2) 
    as [ast' [axs [INTERMR1 [FINALREF [INTSTATES SPLITS]]]]].
  destruct (intermr_implies_interm INTERMR1) as [INTERM1 | [EQ LST]].
  + (* machine1 steps*)
    destruct (CFI1 ast ast' axs INIT1 INTERM1) as [TSAFE1 | H].
    - (*machine1 has CFI at all steps*)
      unfold trace_has_cfi in TSAFE1.
      left.
      intros csi csj IN2.
      destruct (INTSTATES csi csj IN2) as [asi [asj [IN2' [REFI REFJ]]]].
      destruct IN2' as [[VISIBLE IN2'] | [INVISIBLE  [EQ IN]]].
      * (*case it's a visible STEP and In2 for machine1 is true*)
        destruct IN2' as [IN2' [[STEPN2 STEPN1] | [STEPA2 STEPA1]]].
        { (*case it's a normal step*)
          destruct (TSAFE1 asi asj IN2') as [SAFE_STEPA SAFE_STEP].
          split; [apply attacker_pc | idtac].
           apply SAFE_STEP in STEPN1.
           intro.
           apply (cfg_equiv asi asj csi csj REFI REFJ STEPN1).
        }
        { (*case it's an attacker step*)
          destruct (TSAFE1 asi asj IN2') as [SAFE_STEPA SAFE_STEP].
          split; [apply attacker_pc | idtac].
          destruct (succ csi csj) eqn:SUCC.
          + auto.
          + intro STEPN2.
            destruct (vio_noattacker csi csj SUCC STEPN2). assumption.
        } 
      * (*case it's an invisible STEP*)
        subst.
        split.
        apply attacker_pc.
        intro STEPN2.
        destruct (cfg_invisible asj csi csj STEPN2 INVISIBLE); auto.
    - (*machine1 has a violation*) 
      destruct H as [asi [asj [ahs [atl [TRACE [VIOLATES [CFIH [CFIT STOPS1]]]]]]]].
      destruct (SPLITS asi asj ahs atl TRACE) as [csi [csj [chs [ctl [REFI [REFJ [CTRACE [INTHEAD INTAIL]]]]]]]].
      right.
      exists csi; exists csj; exists chs; exists ctl.
      split. assumption.
      split. 
      assert (IN2 : In2 csi csj cxs) by (rewrite CTRACE; apply in2_trivial).
      apply INTSTATES in IN2.
      destruct IN2 as [asi' [asj' [[[VISIBLE [IN2 [[STEPN2' STEPN1'] | [STEPA2' STEPA1']]]] 
                             | [INVISIBLE [EQ IN]]] REFS]]].
      - split; auto.
        destruct VIOLATES as [? VIOLATES].
        eapply av_implies_cv; eauto.
      - destruct VIOLATES as [? VIOLATES].
        assert (VIOLATION2: V2 csi csj) by (eapply av_implies_cv; eauto).
        
      split.
      { (* trace_has_cfi chs++[csi] *)
        intros csi' csj' IN2. 
        destruct (INTHEAD csi' csj' IN2) as [asi' [asj' [IN2' [REFI' REFJ']]]].
        destruct IN2' as [[VISIBLE IN2'] | [INVISIBLE  [EQ IN]]].
        * (*machine2 takes a visible step*)
          destruct (CFIH asi' asj' IN2') as [[STEPA ?] | SUCC]. 
          { left; split; [idtac | apply attacker_pc]; eapply astep_implies_cstep; eauto. }
          { assert (STEP1: cfi_step machine1 asi' asj'). 
            { eapply interm_in2_step. eauto. rewrite TRACE. 
              replace (ahs ++ asi :: asj :: atl) with ((ahs++[asi])++asj::atl). 
              apply in2_strengthen'. assumption.
              simpl; rewrite <- app_assoc; reflexivity. }
            destruct STEP1 as [STEPA | STEPN]; 
              [ left; erewrite attacker_pc; eapply astep_implies_cstep in STEPA; eauto |
                right; apply (cfg_equiv asi' asj' csi' csj' REFI' REFJ' STEPN); assumption ].
          }
        * (*machine2 takes an invisible step*)
          subst.
          assert (STEP2: cfi_step machine2 csi' csj').
          { eapply interm_in2_step in INTERM2.
            eauto. replace (chs ++ csi :: csj :: ctl) with ((chs ++ [csi]) ++ (csj :: ctl)).
            apply in2_strengthen'. assumption.
            rewrite <- app_assoc. reflexivity.
          }
          destruct STEP2 as [STEPA | STEPN].
          { left; split; [idtac | apply attacker_pc]; eauto. }
          { right; eapply cfg_invisible; eauto. }
      }
      { (*trace has cfi csj :: ctl and will halt *)
        split.
        + (*tail has cfi*)
          intros csi' csj' IN2.
          destruct (INTAIL csi' csj' IN2) as [asi' [asj' [IN2' [REFI' REFJ']]]].
          destruct IN2' as [[VISIBLE IN2'] | [INVISIBLE  [EQ IN]]].
          - (*visible step*)
            destruct (CFIT asi' asj' IN2') as [[STEPA ?] | SUCC].
            * left; split; [idtac | apply attacker_pc]; eapply astep_implies_cstep; eauto.
            * assert (STEP1: cfi_step machine1 asi' asj').
              { eapply interm_in2_step; eauto. rewrite TRACE.
                apply in2_strengthen with (ys := (ahs ++ [asi])) in IN2'.
                rewrite <- app_assoc in IN2'; auto.
              }
              destruct STEP1 as [STEPA | STEPN];
              [ left; erewrite attacker_pc; eapply astep_implies_cstep in STEPA; eauto |
                right; apply (cfg_equiv asi' asj' csi' csj' REFI' REFJ' STEPN); assumption ].
          - (*invisible step*)
            subst.
            assert (STEP2: cfi_step machine2 csi' csj').
            { eapply interm_in2_step in INTERM2.
              eauto. replace (chs ++ csi :: csj :: ctl) with ((chs ++ [csi]) ++ (csj :: ctl)).
              apply in2_strengthen. assumption.
              rewrite <- app_assoc. reflexivity.
            }
            destruct STEP2 as [STEPA | STEPN].
            { left; split; [idtac | apply attacker_pc]; eauto. }
            { right; eapply cfg_invisible; eauto. }
         + eapply as_implies_cs; eauto.
     }
  + (* machine1 doesn't step at all*)   
    subst. left.
    intros csi csj IN2.
    destruct (INTSTATES csi csj IN2) as [asi [asj [IN2' [REFI REFJ]]]].
    destruct IN2' as [[VISIBLE IN2'] | [INVISIBLE  [EQ IN]]].
    * (*case machine1 takes a step*)
      destruct IN2'.
    * (*case machine1 does not take a step*)
      subst.
      destruct (interm_in2_step INTERM2 IN2).
      - left; erewrite attacker_pc; eauto.
      - right; eapply cfg_invisible; eauto.
*)


End Preservation.

