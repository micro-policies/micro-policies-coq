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

Variable amachine : cfi_machine t.
Variable cmachine : cfi_machine t.

Variable AV : (@state t amachine) -> (@state t amachine) -> Prop.
Variable AS : (list (@state t amachine)) -> Prop.

Variable CV : (@state t cmachine) -> (@state t cmachine) -> Prop.
Variable CS : (list (@state t cmachine)) -> Prop.

(* General notion of refinement between two machines*)
Class machine_refinement (amachine : cfi_machine t) (cmachine : cfi_machine t) := {
  refine_state : ((@state t) amachine) -> ((@state t) cmachine) -> Prop;
 
  visible : ((@state t) cmachine) -> ((@state t) cmachine) -> bool;

  (* a better way to state this is as 3 properties (diagrams): a-a n-0 n-n *)
  backwards_refinement_normal :  
    forall ast cst cst'
      (REF: refine_state ast cst)
      (STEP: step cst cst'),
      (visible cst cst' = true ->
       exists ast', step ast ast' /\ refine_state ast' cst')
      /\ (visible cst cst' = false -> refine_state ast cst');

  backwards_refinement_attacker :  
    forall ast cst cst'
      (REF: refine_state ast cst)
      (STEP: step_a cst cst'),
      exists ast', step_a ast ast' /\ refine_state ast' cst';

  (* old, get rid of this *)
  backwards_refinement_single : 
    forall ast cst cst'
      (REF: refine_state ast cst)
      (STEP: cfi_step cmachine cst cst'),
      (visible cst cst' = true /\
       exists ast', cfi_step amachine ast ast' (* <- implied by line below *)  /\ refine_state ast' cst' /\ 
                    ((step cst cst' /\ step ast ast') \/ (step_a cst cst' /\ step_a ast ast'))) 
      \/
      (visible cst cst' = false /\
       refine_state ast cst')

}.

Class machine_refinement_specs (rf : (machine_refinement amachine cmachine)) := {

  step_classic : forall cst cst',
    (step cst cst') \/ (~step cst cst');
  (* in a hurry it can be instantiated with classic axiom from Classical *)

  initial_refine : forall (cst : @state t cmachine),
    initial cst ->
    exists (ast : @state t amachine), initial ast /\ refine_state ast cst;

  cfg_invisible : forall csi csj, 
    step csi csj ->
    visible csi csj = false ->
    succ csi csj = true;

  cfg_equiv : forall (asi asj : @state t amachine) csi csj,
    refine_state asi csi ->
    refine_state asj csj ->
    succ asi asj = true ->
    succ csi csj = true;

  (* Why for concrete machine too??? If we could avoid this, we should.
     Try to do proof below without it! *)
  (* No longer used, remove *)
  vio_noattacker : forall (csi csj : @state t cmachine),
    succ csi csj = false ->
    step csi csj ->
    ~ step_a csi csj;
  
  (* No longer used, remove? *)
  av_no_attacker : forall (asi asj : @state t amachine),
    AV asi asj ->
    step asi asj ->
    ~ step_a asi asj;

  av_implies_cv : forall ast ast' cst cst',
    refine_state ast cst ->
    refine_state ast' cst' ->
    AV ast ast' ->
    CV cst cst';

  (* CH: first premise is a bit strange, stopping is a property of
         whole trace tails not only their first step, still premise
         only talks about first step ...  backwards_refinement_traces
         lemma below extends that to whole traces *)
  as_implies_cs : forall ast cst axs cxs,
    refine_state ast cst ->
    AS (ast::axs) ->
    CS (cst::cxs)

}.

Context (rf : machine_refinement amachine cmachine).
Context (rfs : machine_refinement_specs rf).


Inductive refine_traces :
  list (@state t amachine) -> list (@state t cmachine) -> Prop :=
| TRNil : refine_traces [] []
| TRNormal0 : forall ast cst cst' axs cxs,
    step cst cst' ->
    visible cst cst' = false ->
    refine_state ast cst ->
    refine_state ast cst' ->
    refine_traces (ast :: axs) (cst :: cxs) ->
    refine_traces (ast :: axs) (cst :: cst' :: cxs)
| TRNormal1 : forall ast ast' cst cst' axs cxs,
    step cst cst' ->
    visible cst cst' = true ->
    step ast ast' ->
    refine_state ast cst ->
    refine_state ast' cst' ->
    refine_traces (ast' :: axs) (cst' :: cxs) ->
    refine_traces (ast :: ast' :: axs) (cst :: cst' :: cxs)
| TRAttacker : forall ast ast' cst cst' axs cxs,
    ~step cst cst' ->
    step_a cst cst' ->
    step_a ast ast' ->
    refine_state ast cst ->
    refine_state ast' cst' ->
    refine_traces (ast' :: axs) (cst' :: cxs) ->
    refine_traces (ast :: ast' :: axs) (cst :: cst' :: cxs).

Lemma backwards_refinement_traces_stronger
    (ast : @state t amachine) cst cst' cxs :
  refine_state ast cst ->
  intermstep cmachine cxs cst cst' ->
  exists axs,
    (exists ast', intermrstep amachine axs ast ast') /\
    refine_traces axs cxs.
Admitted.

Lemma refine_traces_weaken_backward : forall axs cxs,
  refine_traces axs cxs ->
    (forall csi csj,
       In2 csi csj cxs ->
       step csi csj ->
       visible csi csj = true ->
         exists asi asj,
           In2 asi asj axs /\ step asi asj
           /\ refine_state asi csi /\ refine_state asj csj).
Admitted.

Lemma refine_traces_weaken_forward : forall axs cxs,
  refine_traces axs cxs ->
  forall asi asj,
    In2 asi asj axs ->
    step asi asj ->
    exists csi csj,
      In2 csi csj cxs /\ step csi csj
      /\ refine_state asi csi /\ refine_state asj csj.
Admitted.

Lemma refine_traces_preserves_cfi_trace : forall axs cxs,
  refine_traces axs cxs ->
  trace_has_cfi amachine axs ->
  trace_has_cfi cmachine cxs.
Admitted.

(* Q: Do we have anything like this? Maybe a weaker variant?
   Might be useful for the split_refine_traces? *)
Lemma refine_traces_unique_proof : forall axs cxs
  (H1 : refine_traces axs cxs)
  (H2 : refine_traces axs cxs),
  H1 = H2.
Admitted.

Lemma split_refine_traces : forall axs cxs asi asj csi csj,
  refine_traces axs cxs ->
  In2 asi asj axs ->
  In2 csi csj cxs ->
  refine_state asi csi ->
  refine_state asj csj ->
  exists apre cpre asuff csuff,
    refine_traces apre cpre /\
    refine_traces asuff csuff /\
    axs = apre ++ asi :: asj :: asuff /\
    cxs = cpre ++ csi :: csj :: csuff.
Admitted.

(* General advice: split off lemmas with recurring proof goals *)

(* We're still missing the part about violations *)
Lemma backwards_refinement_traces
    (ast : @state t amachine) cst cst' cxs :
  refine_state ast cst ->
  intermstep cmachine cxs cst cst' ->
  exists axs,
    (exists ast', intermrstep amachine axs ast ast') /\
    (forall csi csj,
       In2 csi csj cxs ->
       step csi csj ->
       visible csi csj = true ->
         exists asi asj,
           In2 asi asj axs /\ step asi asj
           /\ refine_state asi csi /\ refine_state asj csj).
Proof.
  intros INITREF INTERM2.
  generalize dependent ast.
  induction INTERM2 as [cst cst' STEP2 | cst cst'' cst' cxs' STEP2 INTERM2']; intros.
  {
    destruct (step_classic cst cst') as [STEPN | NST].
  - destruct (backwards_refinement_normal _ _ _ INITREF STEPN) as [VIS INVIS].
    destruct (visible cst cst') eqn:VISIBLE.
    + destruct (VIS eq_refl) as [ast' [ASTEP AREF]]. clear INVIS VIS.
      exists [ast;ast']. split.
      * exists ast'. eapply intermr_multi. right. eassumption. now constructor.
      * intros csi csj IN STEPij VIS.
        exists ast. exists ast'. split. simpl. tauto. split.
        assumption. destruct IN as [[H1 H2]| H]. subst. split; now trivial.
        now destruct H.
    + specialize (INVIS eq_refl). clear VIS.
      (* trivial instantiation *)
      exists [ast]. split. exists ast. now constructor.
      intros csi csj IN STEPij VIS. destruct IN as [[H1 H2]| H]. subst.
      congruence. now destruct H.
  - (* trivial instantiation *)
    exists [ast]. split. exists ast. now constructor.
    intros ? ? IN HC. destruct IN as [[H1 H2]| H]. subst; tauto. now destruct H.    
  }
  { destruct (step_classic cst cst'') as [STEPN | NST].
    - destruct (backwards_refinement_normal _ _ _ INITREF STEPN) as [VIS INVIS].
      destruct (visible cst cst'') eqn:VISIBLE.
      + destruct (VIS eq_refl) as [ast'' [ASTEP AREF]]. clear INVIS VIS.
        destruct (IHINTERM2' ast'' AREF) as [axs [[ast' INTERMR1] IH]].
        exists (ast :: axs); split.
        assert (INTERMR1' : intermrstep amachine (ast :: axs) ast ast').
        { eapply intermr_multi. right; eauto. assumption. }
        eexists; now eassumption.
        intros csi csj IN2 STEP VISIBLE'.
        destruct cxs'; [inversion INTERM2' | idtac].
        apply interm_first_step in INTERM2'; subst.
        destruct IN2 as [[? ?] | IN2]; subst.
        * destruct axs; [inversion INTERMR1 | idtac].
          apply intermr_first_step in INTERMR1; subst.
          exists ast; exists ast''. repeat(split;simpl;auto).
        * destruct (IH _ _ IN2 STEP VISIBLE') as [asi [asj [IN2' [STEP' [REFI REFJ]]]]].
          exists asi; exists asj. split. change (ast :: axs) with ([ast] ++ axs).
          apply in2_strengthen. now assumption.
          repeat (split; auto).
      + specialize (INVIS eq_refl). clear VIS.
        destruct (IHINTERM2' ast INVIS) as [axs [[ast' INTERMR1] IH]].
        (* trivial instantiation *)
        exists axs. split. exists ast'; now assumption.
        intros csi csj IN2 step VIS.
        destruct cxs'; [destruct IN2 | idtac].
        apply interm_first_step in INTERM2'; subst.
        destruct IN2 as [[? ?] | IN2]; subst; [congruence | eapply IH; eauto].
    - (* NG: this gets a little more complicated than the base case,
         because we need a refine_state ast cst'' in order to apply
         the IH. CH: Indeed, it would have been odd not to use
         backwards_refinement_attacker at all. *)
      destruct STEP2 as [STEPA | STEPN]; [| tauto].
      destruct (backwards_refinement_attacker _ _ _ INITREF STEPA)
        as [ast'' [ASTEPA REF]].
      destruct (IHINTERM2' ast'' REF) as [axs [[ast' INTERMR1] IH]].
      exists (ast :: axs). split.  exists ast'.
        eapply intermr_multi; eauto. left. now assumption.
      intros csi csj IN2 STEP VISIBLE. destruct cxs'; [inversion INTERM2' | idtac].
      apply interm_first_step in INTERM2'; subst.
      destruct IN2 as [[? ?] | IN2]; subst.
      * tauto.
      * destruct (IH _ _ IN2 STEP VISIBLE) as [asi [asj [IN2' [ASTEP [REFI REFJ]]]]].
        exists asi; exists asj. split.
        change (ast :: axs) with ([ast] ++ axs). apply in2_strengthen.
        assumption. repeat(split;auto).
  }
Qed.
      
End Refinement.

