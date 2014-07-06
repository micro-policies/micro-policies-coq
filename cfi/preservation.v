Require Import Coq.Lists.List Coq.Bool.Bool.
Require Import common.common.
Require Import lib.utils lib.Coqlib.
Require Import cfi.property.

Set Implicit Arguments.

Import ListNotations.

(* CFI preserved by refinement for two generic (cfi) machines *)

Section Preservation.

Context {t : machine_types}
        {ops : machine_ops t}
        {opss : machine_ops_spec ops}.

Variable amachine : cfi_machine.
Variable cmachine : cfi_machine.

(* General notion of refinement between two machines*)
Class machine_refinement (amachine : cfi_machine) (cmachine : cfi_machine) := {
  refine_state : (@state amachine) -> (@state cmachine) -> Prop;

  check : (@state cmachine) -> (@state cmachine) -> bool;

  backwards_refinement_normal :
    forall ast cst cst'
      (REF: refine_state ast cst)
      (STEP: step cst cst'),
      (check cst cst' = true ->
       exists ast', step ast ast' /\ refine_state ast' cst')
      /\ (check cst cst' = false ->
          refine_state ast cst' \/
          exists ast', step ast ast' /\ refine_state ast' cst');

  backwards_refinement_attacker :
    forall ast cst cst'
      (REF: refine_state ast cst)
      (STEPA: step_a cst cst'),
    exists ast', step_a ast ast' /\ refine_state ast' cst'

}.

Context (rf : machine_refinement amachine cmachine).

Inductive refine_traces :
  list (@state amachine) -> list (@state cmachine) -> Prop :=
| TRNil : forall ast cst,
            refine_state ast cst ->
            refine_traces [ast] [cst]
| TRNormal0 : forall ast cst cst' axs cxs,
    step cst cst' ->
    check cst cst' = false ->
    refine_state ast cst ->
    refine_state ast cst' ->
    refine_traces (ast :: axs) (cst' :: cxs) ->
    refine_traces (ast :: axs) (cst :: cst' :: cxs)
| TRNormal1 : forall ast ast' cst cst' axs cxs,
    step cst cst' ->
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

Lemma refine_traces_single ast cst cst' cxs :
  refine_traces [ast] (cst :: cst' :: cxs) ->
  forall csi csj, 
    In2 csi csj (cst :: cst' :: cxs) -> 
    check csi csj = false.
Proof.
  intros REF csi csj IN2.
  inv REF.
  destruct IN2 as [[E1 E2] | IN2]; subst.
  - assumption.
  - induction (cst' :: cxs).
    + destruct IN2.
    + inv H8.
      * destruct IN2.
      * destruct IN2 as [[E1 E2] | IN2]; subst;
        by auto.
Qed.

Lemma refine_traces_execution ast cst cst' cxs :
  refine_traces [ast] (cst :: cxs) ->
  In cst' (cst :: cxs) ->
  exec step cst cst'.
Proof.
  intros RTRACES IN.
  gdep cst.
  induction cxs; intros.
  - destruct IN as [? | CONTRA]; subst.
    + econstructor(eauto).
    + destruct CONTRA.
  - destruct IN as [EQ | IN]; subst.
    + econstructor(eauto).
    + destruct IN as [? | IN]; subst.
      inv RTRACES. 
      eapply re_step; eauto; econstructor(auto).
    + inv RTRACES.
      assert (IN' : In cst' (a :: cxs)) by (right; auto).
      specialize (IHcxs _ H8 IN').
      eapply restricted_exec_trans; eauto.
      eapply re_step; eauto.
      econstructor(auto).
Qed.
      
Class machine_refinement_specs := {

  step_classic : forall (cst cst': @state cmachine),
    (step cst cst') \/ (~step cst cst');
  (* in a hurry it can be instantiated with classic axiom from Classical *)

  initial_refine : forall (cst : @state cmachine),
    initial cst ->
    exists (ast : @state amachine), initial ast /\ refine_state ast cst;

  cfg_nocheck : forall asi csi csj,
    refine_state asi csi ->
    step csi csj ->
    check csi csj = false ->
    succ csi csj = true;

  (* We should merge this with av_implies_cv, as we did in the paper *)
  cfg_equiv : forall (asi asj : @state amachine) csi csj,
    refine_state asi csi ->
    refine_state asj csj ->
    step asi asj -> (*needed to strengthen this for syscalls, may only need concrete step though*)
    succ asi asj = true ->
    step csi csj ->
    succ csi csj = true;

  (* We discharge this for abstract and symbolic machine without
     making any assumptions on the shape of the CFG *)
  av_no_attacker : forall (asi asj : @state amachine) csi,
    refine_state asi csi ->
    succ asi asj = false ->
    step asi asj ->
    ~ step_a asi asj;

  av_implies_cv : forall ast ast' cst cst',
    refine_state ast cst ->
    refine_state ast' cst' ->
    succ ast ast' = false ->
    check cst cst' = true ->
    step cst cst' ->
    succ cst cst' = false;

  (* Q: Can this be simplified to if we were to show that
     backwards_refinement_traces_stronger produces _unique_ axs?
     Doesn't seem easy to state! *)
  (* CH: not clear how possible it was before, but this is clearly not
     possible with the new way to define backwards_refinement_normal *)
  as_implies_cs : forall axs cxs asi asj csi csj,
    check csi csj = true ->
    succ asi asj = false ->
    step asi asj ->
    refine_state asi csi ->
    refine_traces (asj :: axs) (csj :: cxs) ->
    stopping (asj :: axs) ->
    stopping (csj :: cxs)

}.

Context (rfs : machine_refinement_specs).

(* nit: the final state is irrelevant for both intermstep and
        intermrstep, can we remove it and get of useless existentials? no :P *)
Lemma backwards_refinement_traces_stronger
    (ast : @state amachine) cst cst' cxs :
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
    destruct (check cst cst') eqn:CHECK.
    + destruct (VIS eq_refl) as [ast' [ASTEP AREF]]. clear INVIS VIS.
      exists [ast;ast']. split.
      * exists ast'. eapply intermr_multi. right. eassumption. now constructor.
      * apply TRNormal1; auto.
        constructor(assumption).
    + specialize (INVIS eq_refl); clear VIS.
      destruct INVIS as [ZERO | [ast' [STEP REF]]].
      * exists [ast]; split; [exists ast; constructor | apply TRNormal0; auto].
        now constructor(assumption).
      * exists [ast; ast'].
        { split.
          - exists ast'.
            econstructor; first by (right; eauto).
            constructor.
          - apply TRNormal1; eauto.
            by constructor. }
  - destruct STEP2 as [STEP2A | STEP2N]; [idtac | tauto].
    destruct (backwards_refinement_attacker _ _ _ INITREF STEP2A) as [ast' [STEPA REF]].
    exists [ast;ast']; split;
    [exists ast' | apply TRAttacker; auto; constructor(assumption)].
    eapply intermr_multi; eauto. left; eassumption. now constructor.
  }
  { destruct (step_classic cst cst'') as [STEPN | NST].
    - destruct (backwards_refinement_normal _ _ _ INITREF STEPN) as [VIS INVIS].
      destruct (check cst cst'') eqn:CHECK.
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
      + (*nocheck step case*)
        specialize (INVIS eq_refl); clear VIS.
        destruct INVIS as [ZERO | [ast' [STEP REF]]].
        * destruct (IHINTERM2' ast ZERO) as [axs [[ast' INTERMR1] IH]].
          exists axs. split.
          exists ast'; now assumption.
          destruct axs;
            [inversion INTERMR1 | apply intermr_first_step in INTERMR1; subst].
          destruct cxs';
            [inversion INTERM2' | apply interm_first_step in INTERM2'; subst].
          apply TRNormal0; auto.
        * destruct (IHINTERM2' _ REF) as [axs [[ast'' INTERMR1] IH]].
          exists (ast :: axs).
          { split.
            - exists ast''. econstructor; eauto. by right.
            - destruct axs; first by inversion IH.
              destruct cxs'; first by inversion IH.
              apply interm_first_step in INTERM2'. subst.
              apply intermr_first_step in INTERMR1. subst.
              by eapply TRNormal1; eauto. }
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

Lemma refine_traces_preserves_cfi_trace : forall axs cxs,
  refine_traces axs cxs ->
  trace_has_cfi amachine axs ->
  trace_has_cfi cmachine cxs.
Proof.
  intros axs cxs RTRACE TSAFE csi csj IN2 CSTEP.
  induction RTRACE
    as [ast cst REF | ast cst cst' axs' cxs' STEP VIS REF REF' RTRACE' |
        ast ast' cst cst' axs cxs STEP ASTEP' REF REF' RTRACE'|
        ast ast' cst cst' axs cxs NSTEP STEP ASTEP' REF REF' RTRACE']; subst.
  - destruct IN2.
  - destruct IN2 as [[? ?] | IN2]; subst.
    * apply (cfg_nocheck _ _ _ REF CSTEP VIS).
    * apply IHRTRACE'; assumption.
  - destruct IN2 as [[? ?] | IN2]; subst.
    * assert (SUCC: succ ast ast' = true).
      { apply TSAFE; simpl; auto. }
      apply (cfg_equiv _ _ _ _ REF REF' ASTEP' SUCC STEP).
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
  - edestruct IHref as [chd [csi [csj [ctl [CSTEP [REFI [REFJ [RTHD [RTT CLST]]]]]]]]]; eauto.
    exists (cst :: chd); repeat eexists; eauto. simpl.
    destruct chd; destruct ahd; simpl in *; inv CLST; inv eqaxs; apply TRNormal0; eauto.
    rewrite CLST. reflexivity.
  - destruct ahd; simpl in *.
    + inv eqaxs. clear IHref.
      exists []. exists cst. exists cst'. exists cxs.
      repeat split; eauto. by constructor(assumption).
    + inv eqaxs.
      edestruct IHref as [chd [csi [csj [ctl [CSTEP [REFI [REFJ [RTHD [RTT CLST]]]]]]]]]; eauto.
      clear IHref.
      exists (cst :: chd). exists csi. exists csj. exists ctl.
      repeat split; eauto.
      * destruct chd; destruct ahd; simpl in *; inv CLST; inv H5;
         apply TRNormal1; eauto.
        rewrite CLST. reflexivity.
  - destruct ahd; simpl in *; inv eqaxs.
    apply False_ind. by eapply av_no_attacker; eauto.
    edestruct IHref as [chd [csi [csj [ctl [CSTEP [REFI [REFJ [RTHD [RTT CLST]]]]]]]]]; eauto.
    exists (cst :: chd); repeat eexists; eauto. simpl.
    destruct chd; destruct ahd; simpl in *; inv CLST; inv H6;
    apply TRAttacker; eauto.
    rewrite CLST. reflexivity.
Qed.

(*Preservation Theorem*)

Theorem backwards_refinement_preserves_cfi :
  cfi amachine ->
  cfi cmachine.
Proof.
  intros CFI1 cst cst' cxs INIT2 INTERM2.
  destruct (initial_refine cst INIT2) as [ast [INIT1 INITREF]].
  destruct (backwards_refinement_traces_stronger ast INITREF INTERM2)
    as [axs [[ast' INTERMR1] RTRACE]].
  destruct (intermr_implies_interm INTERMR1) as [INTERM1 | [EQ LST]].
  { (*machine1  steps*)
    clear INTERMR1.
    destruct (CFI1 ast ast' axs INIT1 INTERM1) as [TSAFE1 | VIOLATED].
    - (*machine1 has CFI at all steps*)
      left. apply (refine_traces_preserves_cfi_trace RTRACE TSAFE1).
    - (*machine1 has a violation*)
      destruct VIOLATED
         as [asi [asj [ahs [atl [ALST [[ASTEP AV] [TSAFE1 [TSAFE2 STOP1]]]]]]]].
      assert (IN2: In2 asi asj axs) by (rewrite ALST; apply in2_trivial).
      destruct (refine_traces_split ahs atl asi asj ALST RTRACE ASTEP AV)
        as [chs [csi [csj [ctl [CSTEP [REFI [REFJ [RHT [RTT CLST]]]]]]]]].
      destruct (check csi csj) eqn:VIS.
      + right.
        exists csi; exists csj; exists chs; exists ctl.
        split. now assumption.
        split. split; 
               [assumption | apply (av_implies_cv asi asj csi csj REFI REFJ AV VIS CSTEP)].
        split. now apply (refine_traces_preserves_cfi_trace RHT TSAFE1).
        split. now apply (refine_traces_preserves_cfi_trace  RTT TSAFE2).
        apply (as_implies_cs asi csi VIS AV ASTEP REFI RTT STOP1).
      + left.
        intros csi' csj' IN2' STEP'.
        subst cxs.
        apply In2_inv in IN2'.
        destruct IN2' as [IN2' | [[E1 E2] | IN2']].
        * by apply (refine_traces_preserves_cfi_trace RHT TSAFE1).
        * subst. by eauto using cfg_nocheck.
        * by apply (refine_traces_preserves_cfi_trace  RTT TSAFE2).
  }
  { (*machine1 no step*)
    subst. left.
    intros csi csj IN2 CSTEP.
    simpl in INTERMR1; apply intermr_first_step in INTERMR1; subst.
    destruct cxs. inversion INTERM2.
    apply interm_first_step in INTERM2; subst.
    clear INIT1. clear INIT2. clear INITREF.
    generalize dependent cst.
    induction cxs; intros.
    - destruct IN2.
    - destruct IN2 as [[? ?] | IN2]; subst.
      * inversion RTRACE as [|? ? ? ? ? STEP CHECK REF REF' RTRACE'| |]; subst.
        apply (cfg_nocheck _ _ _ REF STEP CHECK).
      * inversion RTRACE as [|? ? ? ? ? STEP CHECK REF REF' RTRACE'| |]; subst.
        now apply (IHcxs _ RTRACE' IN2).
  }
Qed.

End Preservation.
