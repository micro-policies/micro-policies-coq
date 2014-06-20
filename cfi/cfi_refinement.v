Require Import Coq.Lists.List Coq.Bool.Bool.
Require Import common.common. 
Require Import lib.utils lib.Coqlib.
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

Variable AS : (list (@state t amachine)) -> Prop.

Variable CS : (list (@state t cmachine)) -> Prop.

(* General notion of refinement between two machines*)
Class machine_refinement (amachine : cfi_machine t) (cmachine : cfi_machine t) := {
  refine_state : ((@state t) amachine) -> ((@state t) cmachine) -> Prop;
 
  visible : ((@state t) cmachine) -> ((@state t) cmachine) -> bool;

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
      (STEPA: step_a cst cst'),
    exists ast', step_a ast ast' /\ refine_state ast' cst'

}.

Context (rf : machine_refinement amachine cmachine).

Inductive refine_traces :
  list (@state t amachine) -> list (@state t cmachine) -> Prop :=
| TRNil : forall ast cst, 
            refine_state ast cst -> 
            refine_traces [ast] [cst]
| TRNormal0 : forall ast cst cst' axs cxs,
    step cst cst' ->
    visible cst cst' = false ->
    refine_state ast cst ->
    refine_state ast cst' ->
    refine_traces (ast :: axs) (cst' :: cxs) ->
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

Class machine_refinement_specs := {

  step_classic : forall st st',
    (step st st') \/ (~step st st');
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

  
  av_no_attacker : forall (asi asj : @state t amachine),
    succ asi asj = false ->
    step asi asj ->
    ~ step_a asi asj;

  av_implies_cv : forall ast ast' cst cst',
    refine_state ast cst ->
    refine_state ast' cst' ->
    succ ast ast' = false ->
    visible cst cst' = true ->
    succ cst cst' = false;

  as_implies_cs : forall axs cxs,
    refine_traces axs cxs ->
    AS axs ->
    CS cxs

}.

Context (rfs : machine_refinement_specs).

(* nit: the final state is irrelevant for both intermstep and
        intermrstep, can we remove it and get of useless existentials? no :P *)
Lemma backwards_refinement_traces_stronger
    (ast : @state t amachine) cst cst' cxs :
  refine_state ast cst ->
  intermstep cmachine cxs cst cst' ->
  exists axs,
    (exists ast', intermrstep amachine axs ast ast') /\
    refine_traces axs cxs.
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
      * apply TRNormal1; auto.
        constructor(assumption).
    + specialize (INVIS eq_refl); clear VIS.
      exists [ast]; split; [exists ast; constructor | apply TRNormal0; auto].
      now constructor(assumption).
  - destruct STEP2 as [STEP2A | STEP2N]; [idtac | tauto].
    destruct (backwards_refinement_attacker _ _ _ INITREF STEP2A) as [ast' [STEPA REF]].
    exists [ast;ast']; split;
    [exists ast' | apply TRAttacker; auto; constructor(assumption)].
    eapply intermr_multi; eauto. left; eassumption. now constructor.
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
        destruct axs; [inversion IH | destruct cxs'].
        * inversion IH.
        * apply intermr_first_step in INTERMR1; apply interm_first_step in INTERM2';
          subst.
          apply TRNormal1; auto.
      + (*invisible step case*)
        specialize (INVIS eq_refl); clear VIS.
        destruct (IHINTERM2' ast INVIS) as [axs [[ast' INTERMR1] IH]].
        exists axs. split.
        exists ast'; now assumption.
        destruct axs; 
          [inversion INTERMR1 | apply intermr_first_step in INTERMR1; subst].
        destruct cxs'; 
          [inversion INTERM2' | apply interm_first_step in INTERM2'; subst].
        apply TRNormal0; auto.
      + destruct STEP2 as [STEP2A | STEP2N]; subst.
        { (*case it's an attacker step*)
          destruct (backwards_refinement_attacker _ _ _ INITREF STEP2A) 
          as [ast'' [ASTEP REF]].
        destruct (IHINTERM2' _ REF) as [axs [[ast' INTERMR1] IH]].
        exists (ast::axs).
        split. exists ast'. eapply intermr_multi; eauto. 
        left; now assumption.
        destruct axs; 
          [inversion INTERMR1 | apply intermr_first_step in INTERMR1; subst].
        destruct cxs'; 
          [inversion INTERM2' | apply interm_first_step in INTERM2'; subst].
        apply TRAttacker; auto.
        }
        { (*case it's a normal step*)
          tauto. 
        }
  }
Qed.
  
Lemma refine_traces_weaken_backward : forall axs cxs,
  refine_traces axs cxs ->
    (forall csi csj,
       In2 csi csj cxs ->
       step csi csj ->
       visible csi csj = true ->
         exists asi asj,
           In2 asi asj axs /\ step asi asj
           /\ refine_state asi csi /\ refine_state asj csj).
Proof.
  intros axs cxs RTRACE csi csj IN2 CSTEP VISIBLE.
  induction RTRACE 
    as [ast cst REF | ast cst cst' axs' cxs' STEP VIS ASTEP' REF REF' RTRACE' | 
        ast ast' cst cst' axs cxs STEP VIS ASTEP' REF REF' RTRACE'|
        ast ast' cst cst' axs cxs NSTEP STEP ASTEP' REF REF' RTRACE']; subst.
  - destruct IN2.
  - destruct IN2 as [[? ?] | IN2]; subst.
    + congruence.
    + auto.
  - destruct IN2 as [[? ?] | IN2]; subst.
    + exists ast; exists ast'; repeat(split;simpl;auto).
    + apply IHRTRACE' in IN2.
      destruct IN2 as [asi [asj [IN2' [ASTEP [REFI REFJ]]]]].
      exists asi; exists asj.
      split. simpl. right. auto.
      repeat(split;auto).
  - destruct IN2 as [[? ?] | IN2]; subst.
    + tauto.
    + apply IHRTRACE' in IN2.
      destruct IN2 as [asi' [asj' [IN2' [? [? ?]]]]].
      exists asi'; exists asj'.
      split. simpl; right; auto.
      repeat (split; auto).
Qed.

Lemma refine_traces_weaken_forward : forall axs cxs,
  refine_traces axs cxs ->
  forall asi asj,
    In2 asi asj axs ->
    step asi asj ->
    succ asi asj = false ->
    exists csi csj,
      In2 csi csj cxs /\ step csi csj /\ visible csi csj = true
      /\ refine_state asi csi /\ refine_state asj csj.
Proof.
  intros axs cxs RTRACE asi asj IN2 ASTEP SUCC.
  induction RTRACE 
    as [ast cst REF | ast cst cst' axs' cxs' STEP VIS ASTEP' REF REF' RTRACE' | 
        ast ast' cst cst' axs cxs STEP VIS ASTEP' REF REF' RTRACE'|
        ast ast' cst cst' axs cxs NSTEP STEP ASTEP' REF REF' RTRACE']; subst.
  - destruct IN2.
  - destruct (RTRACE' IN2) as [csi [csj [IN2' [STEP' [REFI REFJ]]]]].
    exists csi; exists csj. split.
    change (cst :: cst' :: cxs') with ([cst] ++ (cst' :: cxs')).
    apply in2_strengthen. now assumption.
    repeat(split; auto).
  - destruct IN2 as [[? ?] | IN2]; subst.
    * exists cst; exists cst'.
      split. simpl; auto.
      repeat (split; auto).
    * destruct (IHRTRACE' IN2) as [csi [csj [IN2' [STEP' [REFI REFJ]]]]].
      exists csi; exists csj.
      split. change (cst :: cst' :: cxs) with ([cst] ++ (cst' :: cxs)).
      apply in2_strengthen. now assumption.
      repeat (split; auto).
  - destruct IN2 as [[? ?] | IN2]; subst.
    * destruct (av_no_attacker _ _ SUCC ASTEP). now assumption.
    * apply IHRTRACE' in IN2. 
      destruct IN2 as [csi [csj [IN2' [STEPN [REFI REFJ]]]]].
      exists csi; exists csj.
      split. change (cst :: cst' :: cxs) with ([cst] ++ (cst' :: cxs)).
      apply in2_strengthen. now assumption.
      repeat (split; auto).
Qed.

Lemma refine_traces_preserves_cfi_trace : forall axs cxs,
  refine_traces axs cxs ->
  trace_has_cfi amachine axs ->
  trace_has_cfi cmachine cxs.
Proof.
  intros axs cxs RTRACE TSAFE csi csj IN2 CSTEP.
  induction RTRACE 
    as [ast cst REF | ast cst cst' axs' cxs' STEP VIS ASTEP' REF RTRACE' | 
        ast ast' cst cst' axs cxs STEP VIS ASTEP' REF REF' RTRACE'|
        ast ast' cst cst' axs cxs NSTEP STEP ASTEP' REF REF' RTRACE']; subst.
  - destruct IN2.
  - destruct IN2 as [[? ?] | IN2]; subst.
    * apply (cfg_invisible _ _ CSTEP VIS).
    * apply IHRTRACE'; assumption.
  - destruct IN2 as [[? ?] | IN2]; subst.
    * assert (SUCC: succ ast ast' = true).
      { apply TSAFE; simpl; auto. }
      apply (cfg_equiv _ _ _ _ REF REF' SUCC).
    * apply IHRTRACE'. 
      destruct axs.
      + intros ? ? CONTRA; destruct CONTRA.
      + intros asi asj IN2'. unfold trace_has_cfi in TSAFE.
        apply in2_strengthen with (ys := [ast]) in IN2'. 
        change ([ast] ++ ast' :: s :: axs ) 
        with (ast :: ast' :: s :: axs) in IN2'.
        apply TSAFE. now assumption.
        now assumption.
  - destruct IN2 as [[? ?] | IN2]; subst.
    * tauto.
    * apply IHRTRACE'. 
      destruct axs.
      + intros ? ? CONTRA; destruct CONTRA.
      + intros asi asj IN2'. unfold trace_has_cfi in TSAFE.
        apply in2_strengthen with (ys := [ast]) in IN2'. 
        change ([ast] ++ ast' :: s :: axs ) 
        with (ast :: ast' :: s :: axs) in IN2'.
        apply TSAFE. now assumption.
        now assumption.
Qed.

Lemma refine_traces_split axs ahd atl asi asj cxs :
  axs = ahd ++ asi :: asj :: atl ->
  refine_traces axs cxs ->
  step asi asj ->
  succ asi asj = false ->
  exists chd csi csj ctl,
    step csi csj /\
    visible csi csj = true /\
    refine_state asi csi /\
    refine_state asj csj /\
    refine_traces (ahd ++ [asi]) (chd ++ [csi]) /\
    refine_traces (asj :: atl) (csj :: ctl) /\
    cxs = chd ++ csi :: csj :: ctl.
Proof.
  intros eqaxs ref astep viol.
  gdep viol. gdep astep. gdep ahd. gdep asi. gdep asj. gdep atl.
  induction ref; intros.
  - by repeat (destruct ahd; inversion eqaxs).
  - edestruct IHref as [chd [csi [csj [ctl [CSTEP [VIS [REFI [REFJ [RTHD [RTT CLST]]]]]]]]]]; eauto.
    exists (cst :: chd); repeat eexists; eauto. simpl.
    destruct chd; destruct ahd; simpl in *; inv CLST; inv eqaxs; apply TRNormal0; eauto.
    rewrite CLST. reflexivity.
  - destruct ahd; simpl in *.
    + inv eqaxs. clear IHref.
      exists []. exists cst. exists cst'. exists cxs.
      repeat split; eauto. by constructor(assumption).
    + inv eqaxs.
      edestruct IHref as [chd [csi [csj [ctl [CSTEP [VIS [REFI [REFJ [RTHD [RTT CLST]]]]]]]]]]; eauto.
      clear IHref.
      exists (cst :: chd). exists csi. exists csj. exists ctl.
      repeat split; eauto. 
      * destruct chd; destruct ahd; simpl in *; inv CLST; inv H6;
         apply TRNormal1; eauto.
        rewrite CLST. reflexivity.
  - destruct ahd; simpl in *; inv eqaxs.
    apply False_ind. by eapply av_no_attacker; eauto.
    edestruct IHref as [chd [csi [csj [ctl [CSTEP [VIS [REFI [REFJ [RTHD [RTT CLST]]]]]]]]]]; eauto.
    exists (cst :: chd); repeat eexists; eauto. simpl.
    destruct chd; destruct ahd; simpl in *; inv CLST; inv H6;
    apply TRAttacker; eauto.
    rewrite CLST. reflexivity.
Qed.   

End Refinement.
