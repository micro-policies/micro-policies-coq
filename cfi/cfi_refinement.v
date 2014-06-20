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

  (* The stronger variant in comments might be true and helpful,
     but doesn't seem trivial to show, so let's try to do without it *)
  backwards_refinement_attacker :  
    forall ast cst cst'
      (REF: refine_state ast cst)
      (STEPA: step_a cst cst'),
(*      (NOSTEP: ~step cst cst'), *)
      exists ast', step_a ast ast' /\ refine_state ast' cst'
        (* /\ ~step ast ast' *)

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
(*    ~step ast ast' -> *)
    step_a ast ast' ->
    refine_state ast cst ->
    refine_state ast' cst' ->
    refine_traces (ast' :: axs) (cst' :: cxs) ->
    refine_traces (ast :: ast' :: axs) (cst :: cst' :: cxs).

(* Hint Constructors refine_traces. *)

Inductive refine_traces_eq : forall ast1 ast2 cst1 cst2
  (H1 : refine_traces ast1 cst1) (H2 : refine_traces ast2 cst2), Prop :=
  | EqNil : forall ast cst H1 H1',
      refine_traces_eq (TRNil ast cst H1) (TRNil ast cst H1')
  | EqNormal0 : forall ast cst cst' axs cxs H1 H2 H3 H4 H5 H1' H2' H3' H4' H5',
      refine_traces_eq H5 H5' ->
      refine_traces_eq (@TRNormal0 ast cst cst' axs cxs H1 H2 H3 H4 H5)
                       (@TRNormal0 ast cst cst' axs cxs H1' H2' H3' H4' H5')
  (* ... *)
.

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

  (* CH: first premise is a bit strange, stopping is a property of
         whole trace tails not only their first step, still premise
         only talks about first step ...  backwards_refinement_traces
         lemma below extends that to whole traces *)
  as_implies_cs : forall axs cxs,
    refine_traces axs cxs ->
    AS axs ->
    CS cxs

}.

Context (rfs : machine_refinement_specs).

(* nit: the final state is irrelevant for both intermstep and
        intermrstep, can we remove it and get of useless existentials? *)
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


    

(* Q: Do we have anything like this? Maybe a weaker variant?
   Might be useful for the split_refine_traces? *)
Lemma refine_traces_unique_proof : forall axs cxs
  (H1 : refine_traces axs cxs)
  (H2 : refine_traces axs cxs),
  H1 = H2.
Admitted.

(* If adding explicit equalities we need to use JMeq, otherwise
The term "H2" has type "refine_traces axs2 cxs2"
 while it is expected to have type "refine_traces axs1 cxs1".
*)
Require Import JMeq.
Lemma refine_traces_unique_proof' : forall axs1 cxs1 axs2 cxs2
  (H1 : refine_traces axs1 cxs1)
  (H2 : refine_traces axs2 cxs2)
  (eqa : axs1 = axs2)
  (eqc : cxs1 = cxs2),
  JMeq H1 H2.
Proof.
  intros. destruct H1; destruct H2; try congruence;
          inversion eqa; inversion eqc; subst; clear eqa eqc.
  - admit. (* requires uniqueness of refine_state proofs, do we have it? *)
Admitted. (* doesn't seem this is going to work *)

Lemma refine_traces_unique_proof'' : forall axs1 cxs1 axs2 cxs2
  (H1 : refine_traces axs1 cxs1)
  (H2 : refine_traces axs2 cxs2)
  (eqa : axs1 = axs2)
  (eqc : cxs1 = cxs2),
  refine_traces_eq H1 H2.
Proof.
  intros. destruct H1; destruct H2; try congruence;
          inversion eqa; inversion eqc; subst; clear eqa eqc.
  - by apply EqNil.
  - apply EqNormal0. admit. (* needs IH *)
Admitted.

Lemma new_lemma axs ahd atl asi asj cxs :
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
  - edestruct IHref as [chd [csi [csj [ctl [? [? [? [? [? ?]]]]]]]]]; eauto.
    exists (cst :: chd); repeat eexists; eauto. simpl.
    destruct chd; destruct ahd; simpl in *; inv H8; inv eqaxs;
      apply TRNormal0; eauto.
    rewrite H8. reflexivity.
  - destruct ahd; simpl in *.
    + inv eqaxs. clear IHref.
      exists []. exists cst. exists cst'. exists cxs.
      repeat split; eauto. by constructor(assumption).
    + inv eqaxs.
      edestruct IHref as [chd [csi [csj [ctl [? [? [? [? [? ?]]]]]]]]]; eauto.
      clear IHref.
      exists (cst :: chd). exists csi. exists csj. exists ctl.
      repeat split; eauto. 
      * destruct chd; destruct ahd; simpl in *; inv H10; inv H6;
         apply TRNormal1; eauto.
      rewrite H10. reflexivity.
  - destruct ahd; simpl in *; inv eqaxs.
    apply False_ind. by eapply av_no_attacker; eauto.
    edestruct IHref as [chd [csi [csj [ctl [? [? [? [? [? ?]]]]]]]]]; eauto.
    exists (cst :: chd); repeat eexists; eauto. simpl.
    destruct chd; destruct ahd; simpl in *; inv H10; inv H6;
      apply TRAttacker; eauto.
    rewrite H10. reflexivity.
Qed.      

(* Attempt with Arthur
Lemma split_refine_traces_aux apre aprel apost cpre cprel cpost asi asj csi csj :
  refine_traces (apre ++ [aprel]) (cpre ++ [cprel]) ->
  refine_traces (aprel :: apost) (cprel :: cpost) ->
  In2 asi asj apost ->
  In2 csi csj cpost ->
  visible csi csj = true ->
  refine_state asi csi ->
  refine_state asj csj ->
  exists chs ctl ahs atl,
    refine_traces (apre ++ aprel :: ahs ++ [asi]) 
                  (cpre ++ cprel :: chs ++ [csi]) /\
    refine_traces (asj :: atl) (csj :: ctl) /\
    cpost = chs ++ csi :: csj :: ctl.
Admitted.

Lemma split_refine_traces' ahs atl cxs asi asj csi csj :
  refine_traces (ahs ++ asi :: asj :: atl) cxs ->
  In2 csi csj cxs ->
  visible csi csj = true ->
  refine_state asi csi ->
  refine_state asj csj ->
  exists chs ctl,
    refine_traces (ahs ++ [asi]) (chs ++ [csi]) /\
    refine_traces (asj :: atl) (csj :: ctl) /\
    cxs = chs ++ csi :: csj :: ctl.
Proof.
  intros reft in2 vis refsi refsj.
  remember (ahs ++ asi :: asj :: atl) as axs.
  destruct reft. destruct in2.
  destruct ahs.
  - simpl in Heqaxs. inversion Heqaxs. subst.
    inversion reft; subst; clear reft.
*)
  

(*
Lemma split_refine_traces_aux axs cxs ahs atl asi :
  axs = ahs ++ asi :: atl ->
  refine_traces axs cxs ->
  exists csi,
    refine_state asi csi /\
    In csi cxs /\
    exists chs, refine_traces (ahs ++ [asi]) (chs ++ [csi]).
Proof.
  intros ALST RTRACE.
  induction RTRACE.*)


Lemma split_refine_traces' axs ahs atl cxs asi asj csi csj :
  axs = ahs ++ asi :: asj :: atl ->
  refine_traces axs cxs ->
  In2 csi csj cxs ->
  visible csi csj = true ->
  step asi asj ->
  step csi csj ->
  refine_state asi csi ->
  refine_state asj csj ->
  exists chs ctl,
    refine_traces (ahs ++ [asi]) (chs ++ [csi]) /\
    refine_traces (asj :: atl) (csj :: ctl) /\
    cxs = chs ++ csi :: csj :: ctl.
Proof.
  intros ALST RTRACE IN2 VIS ASTEP CSTEP REFI REFJ.
  (* generalize dependent asi. generalize dependent asj.
     maybe generalize over all ahs, asi, asj, atl?*)
    induction RTRACE
    as [ast cst REF | ast cst cst' axs' cxs' CSTEP' VIS' REF REF' RTRACE' | 
        ast ast' cst cst' axs cxs STEP VIS' ASTEP' REF REF' RTRACE'|
        ast ast' cst cst' axs cxs NSTEP STEP ASTEP' REF REF' RTRACE']; subst; intros.
  - destruct IN2.
  - destruct IN2 as [[? ?] | IN2]; subst.
    + congruence.
    + destruct (IHRTRACE' ALST IN2) as [chs [ctl [RHEAD [RTAIL CLST]]]].
      exists (cst :: chs); exists ctl.
      split. 
      { destruct chs.
        { simpl in CLST; inversion CLST; subst. 
          inversion RHEAD. subst.
          destruct ahs.
          { inversion H; subst.
            inversion ALST; subst.
            apply TRNormal0; auto. 
          }
          { destruct ahs; inversion H. }
        }
        { inversion CLST; subst.
          destruct ahs.
          { inversion ALST; subst.
            simpl.
            apply TRNormal0; auto.
          }
          { inversion ALST; subst.
            apply TRNormal0; auto.
          }
        }
      }
      { split; auto. rewrite CLST. reflexivity. }
   - (*case TRNormal1*)
     destruct IN2 as [[? ?] | IN2]; subst.
     { 
Admitted.
 
Lemma split_refine_traces cst cst' ast ast' axs ahs atl cxs asi asj csi csj :
  axs = ahs ++ asi :: asj :: atl ->
  refine_traces axs cxs ->
  In2 csi csj cxs ->
  visible csi csj = true ->
  intermstep amachine axs ast ast' -> 
  intermstep cmachine cxs cst cst' ->
  refine_state ast cst ->
  refine_state asi csi ->
  refine_state asj csj ->
  exists chs ctl,
    refine_traces (ahs ++ [asi]) (chs ++ [csi]) /\
    refine_traces (asj :: atl) (csj :: ctl) /\
    cxs = chs ++ csi :: csj :: ctl.
Proof.
  (*intros ALST RTRACE IN2 VISIBLE INTERM1 INTERM2 REFI REFJ INITREF FINALREF.
  (* generalize dependent csi. generalize dependent csj. *)
  generalize dependent ahs. generalize dependent cst.
  induction RTRACE
    as [? ? REF | ? ? ? axs' cxs' STEP VIS ASTEP' REF RTRACE' | 
        ? ? ? ? axs cxs STEP VIS ASTEP' REF REF' RTRACE'|
        ? ? ? ? axs cxs NSTEP STEP ASTEP' REF REF' RTRACE']; subst; intros.
  - destruct IN2.
  - destruct IN2 as [[? ?] | IN2]; subst.
    + congruence.
    + inversion INTERM2; subst.
      * destruct IN2.
      * 
        assert (EQ :  y = cst'0) by (apply interm_first_step in H4; auto). subst.
        assert (EQ : ast0 = ast) by (apply interm_first_step in INTERM1; auto); subst.
        destruct (IHRTRACE' IN2 INTERM1 _ H4 REF _ ALST) as [chs [ctl [HTRACE [TTRACE CLST]]]].
        exists (cst0 :: chs); exists ctl. split.
      { (*case trace refinement for head list*)
        destruct ahs as [|s ahs].
        - inversion ALST; subst.
          destruct chs.
          + simpl. inversion CLST; subst. apply TRNormal0; auto.
          + inversion CLST; subst. 
            apply TRNormal0; auto.
        - simpl in ALST; inversion ALST; subst.
          destruct chs as [|s' chs]; inversion CLST; subst.
          + apply TRNormal0; auto.
          + apply TRNormal0; auto.
      }
      split; auto.
      rewrite CLST. auto.
  - (*TRNormal1*)
    assert (EQ : ast0 = ast) by (apply interm_first_step in INTERM1; auto); subst.
    assert (EQ : cst = cst0) by (apply interm_first_step in INTERM2; auto); subst.
    destruct IN2 as [[? ?] | IN2]; subst.
    + 
      destruct ahs.
      * exists []; exists cxs. split. constructor(assumption).
        split. simpl in ALST; inversion ALST; subst.
        now assumption. 
        reflexivity.
      * simpl in ALST; inversion ALST; subst s.*)
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
