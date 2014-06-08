Require Import Coq.Lists.List Bool.
Require Import common utils Coqlib.
Require Import cfi.

Set Implicit Arguments.

Import ListNotations.

(* Refinement for two generic (cfi) machines *)

Section Refinement.

Context {mt : machine_types}
        {ops : machine_ops mt}
        {opss : machine_ops_spec ops}.

Variable machine1 : cfi_machine mt.
Variable machine2 : cfi_machine mt.

Variable V1 : (@state mt machine1) -> (@state mt machine1) -> Prop.
Variable S1 : (list (@state mt machine1)) -> Prop.

Variable V2 : (@state mt machine2) -> (@state mt machine2) -> Prop.
Variable S2 : (list (@state mt machine2)) -> Prop.

(* General notion of refinement between two machines*)
Class machine_refinement (machine1 : cfi_machine mt) (machine2 : cfi_machine mt) := {
  refine_state : ((@state mt) machine1) -> ((@state mt) machine2) -> Prop;
 
  visible : ((@state mt) machine2) -> ((@state mt) machine2) -> bool;
  
  backwards_refinement_single : 
    forall ast cst cst',
      refine_state ast cst ->
      cfi_step machine2 cst cst' ->
      (visible cst cst' = true /\
       exists ast', cfi_step machine1 ast ast' /\ refine_state ast' cst') \/
      (visible cst cst' = false /\
       refine_state ast cst')
                                                                               
 }.

Class machine_refinement_specs (rf : (machine_refinement machine1 machine2)) := {
  initial_refine : forall (cst : @state mt machine2),
    initial cst ->
    exists (ast : @state mt machine1), initial ast /\ refine_state ast cst;

  astep_implies_cstep : forall asi asj csi csj,
    step_a asi asj ->
    refine_state asi csi ->
    refine_state asj csj ->
    step_a csi csj;

  cfg_kernel : forall (asi : @state mt machine1) csi csj, 
    step csi csj ->
    visible csi csj = false ->
    succ csi csj = true;

  cfg_equiv1 : forall (asi asj : @state mt machine1) csi csj,
    refine_state asi csi ->
    refine_state asj csj ->
    step asi asj ->
    succ asi asj = true ->
    succ csi csj = true;

  av_implies_cv : forall ast ast' cst cst', refine_state ast cst -> refine_state ast' cst' -> V1 ast ast' -> V2 cst cst';

  as_implies_cs : forall ast cst axs cxs, refine_state ast cst -> S1 (ast::axs) -> S2 (cst::cxs)

}.

Context (rf : machine_refinement machine1 machine2).
Context (rfs : machine_refinement_specs rf).

Lemma backwards_refinement (ast : @state mt machine1) cst cst' cxs :
  refine_state ast cst ->
  intermstep machine2 cxs cst cst' ->
  exists ast', exists axs,
    intermrstep machine1 axs ast ast' /\
    refine_state ast' cst' /\
    forall csi csj, In2 csi csj cxs -> exists asi asj, 
                                         (visible csi csj = true /\ In2 asi asj axs 
                                          \/ visible csi csj = false /\ asi = asj /\ In asi axs)
                                         /\ refine_state asi csi
                                         /\ refine_state asj csj.
Proof. 
  intros INITREF INTERM2.
  generalize dependent ast.
  induction INTERM2 as [cst cst' STEP2 | cst cst'' cst' cxs' STEP2 INTERM2']; intros.
  + destruct (backwards_refinement_single ast INITREF STEP2) 
      as [[VISIBLE [ast' [STEP1 FINALREF]]] | [INVISIBLE FINALREF]].
    * (* case machine2 takes a visible step *)
      exists ast'; exists [ast;ast']; split; [ eapply intermr_multi; eauto; constructor | split].
      assumption.
      intros csi csj IN2.
      destruct IN2 as [[EQ1 EQ2] | CONTRA]; subst.
      - exists ast; exists ast'; split; [left; split; simpl; auto | auto].
      - destruct CONTRA.
    * (* case machine2 takes an invisible step *) 
      eexists; eexists; split; [constructor | split].
      assumption.
      intros csi csj IN2.
      destruct IN2 as [[EQ1 EQ2] | CONTRA]; subst.
      - exists ast; exists ast; split; [right; split; simpl; auto | auto].
      - destruct CONTRA.
   + destruct (backwards_refinement_single ast INITREF STEP2)
       as [[VISIBLE [ast'' [STEP1 REF'']]] | [INVISIBLE REF'']].
       * (* case machine2 takes a visible step*)
         destruct (IHINTERM2' ast'' REF'') as [ast' [axs [INTERMR1 [REFFINAL INTSTATES]]]].
         eexists; eexists; split; eauto.
         eapply intermr_multi; eauto.
         split. assumption.
         intros csi csj IN2.
         destruct cxs'; [inversion INTERM2' | idtac].
         apply interm_first_step in INTERM2'. subst.
         destruct IN2 as [[EQ1 EQ2] | IN2']; subst.
         - destruct axs; [inversion INTERMR1 | apply intermr_first_step in INTERMR1; subst].
           exists ast; exists ast''.
           split; [left; simpl; auto | auto].
         - destruct (INTSTATES csi csj IN2') as [asi [asj [[[VISIBLE' IN2] | [INVISIBLE [EQ IN]]] REFS]]]. 
           { exists asi; exists asj; split; [left; split; auto | auto].
             change (ast :: axs) with ([ast] ++ axs).
             apply in2_strengthen. assumption. }
           { subst. exists asj; exists asj; split; [right; split; [assumption | split; simpl; auto] | auto]. }
      * (* case machine2 takes an invisible step *)
         destruct (IHINTERM2' ast REF'') as [ast' [axs [INTERMR1 [REFFINAL INTSTATES]]]].
         eexists; eexists; split; eauto.
         split. assumption.
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
Qed.

Lemma backwards_refinement' (ast : @state mt machine1) cst cst' cxs :
  refine_state ast cst ->
  intermstep machine2 cxs cst cst' ->
  exists ast', exists axs,
    intermrstep machine1 axs ast ast' /\
    refine_state ast' cst' /\
    (forall csi csj, In2 csi csj cxs -> exists asi asj, 
                                         (visible csi csj = true /\ In2 asi asj axs 
                                          \/ visible csi csj = false /\ asi = asj /\ In asi axs)
                                         /\ refine_state asi csi
                                         /\ refine_state asj csj) /\
    (forall asi asj ahs atl, axs = ahs ++ asi :: asj :: atl -> 
                            exists csi csj chs ctl,
                              refine_state asi csi /\ refine_state asj csj /\
                              cxs = chs ++ csi :: csj :: ctl /\
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
  intros INITREF INTERM2.
  generalize dependent ast.
  induction INTERM2 as [cst cst' STEP2 | cst cst'' cst' cxs' STEP2 INTERM2']; intros.
  + destruct (backwards_refinement_single ast INITREF STEP2) 
      as [[VISIBLE [ast' [STEP1 FINALREF]]] | [INVISIBLE FINALREF]].
    * (* case machine2 takes a visible step *)
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
       as [[VISIBLE [ast'' [STEP1 REF'']]] | [INVISIBLE REF'']].
       * (* case machine2 takes a visible step*)
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
           - destruct (INTSTATES csi csj IN2') as [asi [asj [[[VISIBLE' IN2] | [INVISIBLE [EQ IN]]] REFS]]]. 
             { exists asi; exists asj; split; [left; split; auto | auto].
               change (ast :: axs) with ([ast] ++ axs).
               apply in2_strengthen. assumption. }
             { subst. exists asj; exists asj; split; [right; split; [assumption | split; simpl; auto] | auto]. }
         }
         { intros asi asj ahs atl ALST.
           destruct ahs.
           - simpl in ALST.
             inversion ALST; subst.
             apply intermr_first_step in INTERMR1. subst.
             inversion INTERM2'; subst.
             exists cst; exists cst''; exists []; exists [cst'].
             repeat(split; auto).
             intros csi' csj' CONTRA; destruct CONTRA.
             exists cst; exists cst''; exists []; exists xs.
             repeat(split; auto).
             intros csi' csj' CONTRA; destruct CONTRA.
           - inversion ALST. subst s.
             destruct (IHSPLIT asi asj ahs atl) as [csi [csj [chs [ctl [REFI [REFJ [CLST [INTHEAD INTTAIL]]]]]]]].
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
      
End Refinement.

