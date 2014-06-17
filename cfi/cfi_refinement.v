Require Import Coq.Lists.List Coq.Bool.Bool.
Require Import common.common. 
Require Import lib.utils.
Require Import cfi.cfi.

Set Implicit Arguments.

Import ListNotations.

(* Refinement for two generic (cfi) machines *)

Section Refinement.

Context {t : machine_types}
        {ops : machine_ops t}
        {opss : machine_ops_spec ops}.

Variable machine1 : cfi_machine t.
Variable machine2 : cfi_machine t.

Variable V1 : (@state t machine1) -> (@state t machine1) -> Prop.
Variable S1 : (list (@state t machine1)) -> Prop.

Variable V2 : (@state t machine2) -> (@state t machine2) -> Prop.
Variable S2 : (list (@state t machine2)) -> Prop.

(* General notion of refinement between two machines*)
Class machine_refinement (machine1 : cfi_machine t) (machine2 : cfi_machine t) := {
  refine_state : ((@state t) machine1) -> ((@state t) machine2) -> Prop;
 
  visible : ((@state t) machine2) -> ((@state t) machine2) -> bool;

(* Q:
      visible cst cst' = false -> 
      cfi_step cst cst' ->
      step cst cst' (or even ~step_a cst cst')
*)

  (* a better way to state this is as 3 properties (diagrams): a-a n-0 n-n *)
  backwards_refinement_normal :  
    forall ast cst cst'
      (REF: refine_state ast cst)
      (STEP: step cst cst'),
      (visible cst cst' = true -> exists ast', step ast ast' /\ refine_state ast' cst')
      /\ (visible cst cst' = false -> refine_state ast cst');

  backwards_refinement_attacker :  
    forall ast cst cst'
      (REF: refine_state ast cst)
      (STEP: step_a cst cst'),
      exists ast', step_a ast ast'  /\ refine_state ast' cst';

  backwards_refinement_single : 
    forall ast cst cst'
      (REF: refine_state ast cst)
      (STEP: cfi_step machine2 cst cst'),
      (visible cst cst' = true /\
       exists ast', cfi_step machine1 ast ast' (* <- implied by line below *)  /\ refine_state ast' cst' /\ 
                    ((step cst cst' /\ step ast ast') \/ (step_a cst cst' /\ step_a ast ast'))) 
      \/
      (visible cst cst' = false /\
       refine_state ast cst')
                                                
 }.


(* Broken lemma: it seems that this does not follow from
   backwards_refinement_normal and backwards_refinement_attacker

Section Try.

Context (rf : machine_refinement machine1 machine2).

Lemma backwards_refinement_single' : 
    forall ast cst cst'
      (REF: refine_state ast cst)
      (STEP: cfi_step machine2 cst cst'),
      (exists ast', refine_state ast' cst' /\ 
                    ((step cst cst' -> step ast ast') /\
                     (step_a cst cst' -> step_a ast ast')))
      \/
      (step cst cst' /\ refine_state ast cst').
Proof.
  intros. destruct STEP.
  - destruct (backwards_refinement_attacker _ _ _ REF H) as [ast' [H1 H2]].
    left. exists ast'. split. assumption. split; intro.
    intuition.
  - destruct (backwards_refinement_normal _ _ _ REF H).

End Try.
*)

Class machine_refinement_specs (rf : (machine_refinement machine1 machine2)) := {
  initial_refine : forall (cst : @state t machine2),
    initial cst ->
    exists (ast : @state t machine1), initial ast /\ refine_state ast cst;

  cfg_kernel : forall csi csj, 
    step csi csj ->
    visible csi csj = false ->
    succ csi csj = true;
  (* if we drop visible then we could return to something like this: *)
  backwards_refinement_normal_zero_step :  
    forall ast cst cst'
      (REF: refine_state ast cst)
      (STEP: step cst cst'),
      refine_state ast cst' ->
      succ cst cst' = true;

  cfg_equiv1 : forall (asi asj : @state t machine1) csi csj,
    refine_state asi csi ->
    refine_state asj csj ->
    succ asi asj = true ->
    succ csi csj = true;

  (* Why for concrete machine too??? If we could avoid this, we should.
     Try to do proof below without it! *)
  vio_noattacker : forall (csi csj : @state t machine2),
    succ csi csj = false ->
    step csi csj ->
    ~ step_a csi csj;

  av_no_attacker : forall (asi asj : @state t machine1),
    V1 asi asj ->
    step asi asj ->
    ~ step_a asi asj;

  av_implies_cv : forall ast ast' cst cst', refine_state ast cst -> refine_state ast' cst' -> V1 ast ast' -> V2 cst cst';

  as_implies_cs : forall ast cst axs cxs, refine_state ast cst -> S1 (ast::axs) -> S2 (cst::cxs)

}.

Context (rf : machine_refinement machine1 machine2).
Context (rfs : machine_refinement_specs rf).

(* This should follow from from backwards_refinement_normal and
   backwards_refinement_attacker *)
Lemma backwards_refinement_on_traces_ignoring_violations
    (ast : @state t machine1) cst cst' cxs :
  refine_state ast cst ->
  intermstep machine2 cxs cst cst' ->
  exists ast', exists axs,
    intermrstep machine1 axs ast ast' /\
    refine_state ast' cst' /\
    (forall csi csj,
       In2 csi csj cxs ->
       step csi csj ->
       visible cst cst' = true ->
         exists asi asj,
           In2 asi asj axs /\ step asi asj
           /\ refine_state asi csi /\ refine_state asj csj).
Admitted.

Lemma backwards_refinement' (ast : @state t machine1) cst cst' cxs :
  refine_state ast cst ->
  intermstep machine2 cxs cst cst' ->
  exists ast', exists axs,
    intermrstep machine1 axs ast ast' /\
    refine_state ast' cst' /\
    (forall csi csj, In2 csi csj cxs -> exists asi asj, 
                                         (visible csi csj = true /\ In2 asi asj axs /\
                                          ((step csi csj /\ step asi asj) \/ 
                                           (step_a csi csj /\ step_a asi asj))
                                          \/ visible csi csj = false /\ asi = asj /\ In asi axs)
                                         /\ refine_state asi csi
                                         /\ refine_state asj csj) /\
    (* about violations -- why in the same property? *)
    (* stated in reverse wrt above *)
    (forall asi asj ahs atl, axs = ahs ++ asi :: asj :: atl ->
                             step asi asj ->
                             V1 asi asj ->
                            exists csi csj chs ctl,
                              refine_state asi csi /\ refine_state asj csj /\
                              cxs = chs ++ csi :: csj :: ctl /\
                              step csi csj /\
                              (forall csi' csj', In2 csi' csj' (chs ++ [csi]) -> exists asi' asj', 
                                         (visible csi' csj' = true /\ In2 asi' asj' (ahs ++ [asi]) 
                                          \/ visible csi' csj' = false /\ asi' = asj' /\ In asi' (ahs ++ [asi]))
                                         /\ refine_state asi' csi'
                                         /\ refine_state asj' csj') /\
                              (forall csi' csj', In2 csi' csj' (csj :: ctl) -> exists asi' asj', 
                                          (visible csi' csj' = true /\ In2 asi' asj' (asj :: atl) 
                                          \/ visible csi' csj' = false /\ asi' = asj' /\ In asi' (asj :: atl))
                                         /\ refine_state asi' csi'
                                         /\ refine_state asj' csj')).
Proof. 
 (* intros INITREF INTERM2.
  generalize dependent ast.
  induction INTERM2 as [cst cst' STEP2 | cst cst'' cst' cxs' STEP2 INTERM2']; intros.
  + destruct (backwards_refinement_single ast INITREF STEP2) 
      as [[VISIBLE [ast' [STEP1 [FINALREF [[STEPN2 STEPN1] | [STEPA2 STEPA1]]]]]] 
         | [INVISIBLE FINALREF]].
    * (* case machine2 takes a visible normal step *)
      exists ast'; exists [ast;ast']; split; [ eapply intermr_multi; eauto; constructor | split].
      assumption.
      split.
      { intros csi csj IN2.
        destruct IN2 as [[EQ1 EQ2] | CONTRA]; subst.
        - exists ast; exists ast'; split; [left; split; simpl; auto | auto].
        - destruct CONTRA.
      }
      { intros asi asj ahs atl ALST.
        destruct ahs.
        - simpl in ALST. destruct atl; inversion ALST; subst. 
          exists cst; exists cst'; exists []; exists [].
          simpl. repeat (split; auto);
          intros csi' csj' CONTRA; destruct CONTRA.
        - repeat (destruct ahs; inversion ALST).
      } 
    * (* case machine2 takes a visible attacker step *)
      exists ast'; exists [ast;ast']; split; [ eapply intermr_multi; eauto; constructor | split].
      assumption.
      split.
      { intros csi csj IN2.
        destruct IN2 as [[EQ1 EQ2] | CONTRA]; subst.
        - exists ast; exists ast'; split; [left; split; simpl; auto | auto].
        - destruct CONTRA.
      }
      { intros asi asj ahs atl ALST STEPN1 VIO1.
        destruct ahs.
        - simpl in ALST. destruct atl; inversion ALST; subst. 
          exists cst; exists cst'; exists []; exists [].
          simpl. repeat (split; auto).
          destruct (av_no_attacker VIO1 STEPN1); auto.
          intros csi' csj' CONTRA; destruct CONTRA.
          intros csi' csj' CONTRA; destruct CONTRA.
        - repeat (destruct ahs; inversion ALST).
      }   
    * (* case machine2 takes an invisible step *) 
      eexists; eexists; split; [constructor | split].
      assumption.
      split.
      { intros csi csj IN2.
        destruct IN2 as [[EQ1 EQ2] | CONTRA]; subst.
        - exists ast; exists ast; split; [right; split; simpl; auto | auto].
        - destruct CONTRA.
      }
      { intros asi asj ahs atl ALST. repeat (destruct ahs; inversion ALST). }
   + destruct (backwards_refinement_single ast INITREF STEP2)
       as [[VISIBLE [ast'' [STEP1 [REF'' [[STEPN2 STEPN1] | [STEPA2 STEPA1]]]]]] 
          | [INVISIBLE REF'']].
       * (* case machine2 takes a visible normal step*)
         destruct (IHINTERM2' ast'' REF'') as [ast' [axs [INTERMR1 [REFFINAL [INTSTATES IHSPLIT]]]]].
         eexists; eexists; split; eauto.
         eapply intermr_multi; eauto.
         split. assumption.
         split.
         { intros csi csj IN2.
           destruct cxs'; [inversion INTERM2' | idtac].
           apply interm_first_step in INTERM2'. subst.
           destruct IN2 as [[EQ1 EQ2] | IN2']; subst.
           - destruct axs; [inversion INTERMR1 | apply intermr_first_step in INTERMR1; subst].
             exists ast; exists ast''.
             split; [left; simpl; auto | auto].
           - destruct (INTSTATES csi csj IN2') 
               as [asi [asj [[[VISIBLE' [IN2 [[STEPN2' STEPN1'] | [STEPA2' STEPA1']]]] 
                             | [INVISIBLE [EQ IN]]] REFS]]]. 
             { exists asi; exists asj; split; [left; split; auto | auto].
               change (ast :: axs) with ([ast] ++ axs).
               split.
               - apply in2_strengthen. assumption. 
               - auto. }
             { exists asi; exists asj; split; [left; split; auto | auto].
               change (ast :: axs) with ([ast] ++ axs).
               split.
               - apply in2_strengthen. assumption. 
               - auto. }
             { subst. exists asj; exists asj. split; [right; split; [assumption | split; simpl; auto] | auto]. }
         }
         {(*violation case *)
           intros asi asj ahs atl ALST stepn1.
           destruct ahs.
           - simpl in ALST.
             inversion ALST; subst.
             apply intermr_first_step in INTERMR1. subst.
             inversion INTERM2'; subst.
             exists cst; exists cst''; exists []; exists [cst'].
             repeat(split; auto).
             intros csi' csj' CONTRA; destruct CONTRA.
             intros csi' csj' IN2.
             apply INTSTATES in IN2. 
             destruct IN2 
               as [asi' [asj' [[[VISIBLE' [IN2 [? | ?]]] | [VISIBLE' [EQ IN]]] REF]]].
             exists asi'; exists asj'. split; auto.
             exists asi'; exists asj'; split; auto.
             subst.
             exists asj'; exists asj'; split; auto.
             exists cst; exists cst''; exists []; exists xs.
             repeat(split; auto).
             intros csi' csj' CONTRA; destruct CONTRA. 
             intros csi' csj' IN2.
             apply INTSTATES in IN2. 
             destruct IN2 
               as [asi' [asj' [[[VISIBLE' [IN2 [? | ?]]] | [VISIBLE' [EQ IN]]] REF]]].
             exists asi'; exists asj'. split; auto.
             exists asi'; exists asj'; split; auto.
             subst.
             exists asj'; exists asj'; split; auto.
           - inversion ALST. subst s.
             destruct (IHSPLIT asi asj ahs atl) 
               as [csi [csj [chs [ctl [REFI [REFJ [CLST [INTHEAD INTTAIL]]]]]]]].
             assumption.
             exists csi; exists csj; exists (cst :: chs); exists ctl.
             repeat (split; auto).
             rewrite CLST. reflexivity.
             intros csi' csj' IN2.
             rewrite H1 in INTERMR1.
             destruct chs; 
             destruct IN2 as [[EQ1 EQ2] | IN2']; subst.
             { apply interm_first_step in INTERM2'. subst.
               exists ast; exists ast''.
               split. left. split; auto.
               destruct ahs; apply intermr_first_step in INTERMR1; subst; simpl; auto.
               auto.
             } 
             { destruct IN2'. }
             { apply interm_first_step in INTERM2'. subst.
               exists ast; exists ast''.
               split. left. split; auto.
               destruct ahs; apply intermr_first_step in INTERMR1; subst; simpl; auto.
               auto.
             }
             { destruct (INTHEAD csi' csj' IN2') as 
                   [asi' [asj' [[[VISIBLE' IN2] | [INVISIBLE [EQ IN]]] REFS]]].
               eexists; eexists; split; eauto.
               left; split; auto. simpl. destruct (ahs ++ [asi]); [destruct IN2 | right; auto].
               eexists; eexists; split; eauto.
               right; repeat (split; auto). simpl. 
               destruct (ahs ++ [asi]); [destruct IN | right; auto].
             }
         }
       * (* case machine2 takes a visible attacker step*)
         destruct (IHINTERM2' ast'' REF'') as [ast' [axs [INTERMR1 [REFFINAL [INTSTATES IHSPLIT]]]]].
         eexists; eexists; split; eauto.
         eapply intermr_multi; eauto.
         split. assumption.
         split.
         { intros csi csj IN2.
           destruct cxs'; [inversion INTERM2' | idtac].
           apply interm_first_step in INTERM2'. subst.
           destruct IN2 as [[EQ1 EQ2] | IN2']; subst.
           - destruct axs; [inversion INTERMR1 | apply intermr_first_step in INTERMR1; subst].
             exists ast; exists ast''.
             split; [left; simpl; auto | auto].
           - destruct (INTSTATES csi csj IN2') 
               as [asi [asj [[[VISIBLE' [IN2 [[STEPN2' STEPN1'] | [STEPA2' STEPA1']]]] 
                             | [INVISIBLE [EQ IN]]] REFS]]]. 
             { exists asi; exists asj; split; [left; split; auto | auto].
               change (ast :: axs) with ([ast] ++ axs).
               split.
               - apply in2_strengthen. assumption. 
               - auto. }
             { exists asi; exists asj; split; [left; split; auto | auto].
               change (ast :: axs) with ([ast] ++ axs).
               split.
               - apply in2_strengthen. assumption. 
               - auto. }
             { subst. exists asj; exists asj. split; [right; split; [assumption | split; simpl; auto] | auto]. }
         }
         {(*violation case *)
           intros asi asj ahs atl ALST.
           destruct ahs.
           - simpl in ALST.
             inversion ALST; subst.
             apply intermr_first_step in INTERMR1. subst.
             inversion INTERM2'; subst.
             exists cst; exists cst''; exists []; exists [cst'].
             repeat(split; auto).
             intros csi' csj' CONTRA; destruct CONTRA.
             intros csi' csj' IN2.
             apply INTSTATES in IN2. 
             destruct IN2 
               as [asi' [asj' [[[VISIBLE' [IN2 [? | ?]]] | [VISIBLE' [EQ IN]]] REF]]].
             exists asi'; exists asj'. split; auto.
             exists asi'; exists asj'; split; auto.
             subst.
             exists asj'; exists asj'; split; auto.
             exists cst; exists cst''; exists []; exists xs.
             repeat(split; auto).
             intros csi' csj' CONTRA; destruct CONTRA. 
             intros csi' csj' IN2.
             apply INTSTATES in IN2. 
             destruct IN2 
               as [asi' [asj' [[[VISIBLE' [IN2 [? | ?]]] | [VISIBLE' [EQ IN]]] REF]]].
             exists asi'; exists asj'. split; auto.
             exists asi'; exists asj'; split; auto.
             subst.
             exists asj'; exists asj'; split; auto.
           - inversion ALST. subst s.
             destruct (IHSPLIT asi asj ahs atl) 
               as [csi [csj [chs [ctl [REFI [REFJ [CLST [INTHEAD INTTAIL]]]]]]]].
             assumption.
             exists csi; exists csj; exists (cst :: chs); exists ctl.
             repeat (split; auto).
             rewrite CLST. reflexivity.
             intros csi' csj' IN2.
             rewrite H1 in INTERMR1.
             destruct chs; 
             destruct IN2 as [[EQ1 EQ2] | IN2']; subst.
             { apply interm_first_step in INTERM2'. subst.
               exists ast; exists ast''.
               split. left. split; auto.
               destruct ahs; apply intermr_first_step in INTERMR1; subst; simpl; auto.
               auto.
             } 
             { destruct IN2'. }
             { apply interm_first_step in INTERM2'. subst.
               exists ast; exists ast''.
               split. left. split; auto.
               destruct ahs; apply intermr_first_step in INTERMR1; subst; simpl; auto.
               auto.
             }
             { destruct (INTHEAD csi' csj' IN2') as 
                   [asi' [asj' [[[VISIBLE' IN2] | [INVISIBLE [EQ IN]]] REFS]]].
               eexists; eexists; split; eauto.
               left; split; auto. simpl. destruct (ahs ++ [asi]); [destruct IN2 | right; auto].
               eexists; eexists; split; eauto.
               right; repeat (split; auto). simpl. 
               destruct (ahs ++ [asi]); [destruct IN | right; auto].
             }
         }
        * (* case machine2 takes an invisible step *)
          destruct (IHINTERM2' ast REF'') as [ast' [axs [INTERMR1 [REFFINAL [INTSTATES IHSPLIT]]]]].
          eexists; eexists; split; eauto.
          split. assumption.
          split.
          { (*proof for steps in cxs*)
            intros csi csj IN2.
            destruct cxs'; [inversion INTERM2' | apply interm_first_step in INTERM2'; subst].
            destruct IN2 as [[EQ1 EQ2] | IN2']; subst.
            - eexists; eexists; split; [right | eauto].
              split; [assumption | split; [reflexivity | idtac]].
              apply intermr_in_first_last in INTERMR1.
              destruct INTERMR1; auto.
            - destruct (INTSTATES csi csj IN2') as [asi [asj [[[VISIBLE IN2] | [INVISIBLE' [EQ IN]]] REFS]]].
              {exists asi; exists asj. split; [left; split; auto | assumption]. }
              {subst. exists asj; exists asj; split; [right; split; auto | auto]. }
          }
          { (*proof for splitted lists*)
            intros asi asj ahs atl ALST.
            destruct (IHSPLIT asi asj ahs atl ALST) as 
                [csi [csj [chs [ctl [REFI [REFJ [CLST [INTHEAD INTTAIL]]]]]]]].
            exists csi; exists csj; exists (cst :: chs); exists ctl.
            repeat (split; auto).
            rewrite CLST. reflexivity.
            intros csi' csj' IN2.
            destruct ahs.
            - simpl in ALST.
              rewrite ALST in INTERMR1.
              apply intermr_first_step in INTERMR1. subst.
              destruct chs. 
              + destruct IN2 as [[EQ1 EQ2] | CONTRA]; subst.
                * apply interm_first_step in INTERM2'; subst.
                  exists ast; exists ast.
                  split; auto.
                  right. repeat(split;simpl;auto).
                * destruct CONTRA.
              + destruct IN2 as [[EQ1 EQ2] | IN2']; subst.
                * apply interm_first_step in INTERM2'; subst.
                  exists ast; exists ast.
                  split; auto.
                  right; repeat(split;simpl;auto).
                * apply INTHEAD. assumption.
            - rewrite ALST in INTERMR1. apply intermr_first_step in INTERMR1; subst.
              destruct chs.
              + destruct IN2 as [[EQ1 EQ2] | CONTRA]; subst.
                * apply interm_first_step in INTERM2'; subst.
                  exists ast; exists ast.
                  split; auto.
                  right. repeat(split;simpl;auto).
                * destruct CONTRA.
              + destruct IN2 as [[EQ1 EQ2] | IN2']; subst.
                * apply interm_first_step in INTERM2'; subst.
                  exists ast; exists ast.
                  split; auto.
                  right; repeat(split;simpl;auto).
                * apply INTHEAD. assumption.
          }
Qed.  
*) Admitted.
      
End Refinement.

