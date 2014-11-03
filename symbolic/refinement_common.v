Require Import List NPeano Arith Bool.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Require Import lib.hlist lib.Integers lib.utils lib.Coqlib lib.partial_maps.
Require Import common.common.
Require Import concrete.concrete.
Require Import concrete.exec.
Require Import symbolic.symbolic.
Require Import symbolic.exec.
Require Import symbolic.rules.

Open Scope nat_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import ListNotations.

Hint Constructors restricted_exec.
Hint Unfold exec.
Hint Resolve restricted_exec_trans.

Section Refinement.

Context {mt : machine_types}
        {ops : machine_ops mt}
        {opss : machine_ops_spec ops}
        {sp : Symbolic.params}
        {e : encodable mt Symbolic.ttypes}.

Definition refine_memory (amem : Symbolic.memory mt _) (cmem : Concrete.memory mt) :=
  (forall w x ctg atg,
     decode Symbolic.M cmem ctg = Some (USER atg) ->
     PartMaps.get cmem w = Some x@ctg ->
     PartMaps.get amem w = Some x@atg) /\
  (forall w x atg,
     PartMaps.get amem w = Some x@atg ->
     exists2 ctg,
       decode Symbolic.M cmem ctg = Some (USER atg) &
       PartMaps.get cmem w = Some x@ctg).

Definition refine_registers (areg : Symbolic.registers mt _)
                            (creg : Concrete.registers mt)
                            (cmem : Concrete.memory mt) :=
  (forall r x ctg atg,
     decode Symbolic.R cmem ctg = Some (USER atg) ->
     PartMaps.get creg r = Some x@ctg ->
     PartMaps.get areg r = Some x@atg) /\
  (forall r x atg,
     PartMaps.get areg r = Some x@atg ->
     exists2 ctg,
       decode Symbolic.R cmem ctg = Some (USER atg) &
       PartMaps.get creg r = Some x@ctg).

Definition in_kernel (st : Concrete.state mt) :=
  Concrete.is_kernel_tag (Concrete.pct st).
Hint Unfold in_kernel.

Definition in_user st :=
  oapp (fun x => is_user x) false (decode Symbolic.P (Concrete.mem st) (Concrete.pct st)).
Hint Unfold in_user.

Definition cache_correct cache cmem :=
  forall cmvec crvec,
    Concrete.cache_lookup cache masks cmvec = Some crvec ->
    oapp (fun x => is_user x) false (decode Symbolic.P cmem (Concrete.ctpc cmvec)) ->
    exists ivec ovec,
      [/\ decode_ivec e cmem cmvec = Some ivec,
          decode_ovec e (Symbolic.op ivec) cmem crvec = Some ovec &
          Symbolic.transfer ivec = Some ovec ].

Definition in_mvec addr := In addr (Concrete.mvec_fields mt).

Definition mvec_in_kernel (cmem : Concrete.memory mt) :=
  forall addr,
    in_mvec addr ->
    exists w : (word mt), PartMaps.get cmem addr = Some w@Concrete.TKernel.

Lemma store_mvec_mvec_in_kernel cmem cmem' mvec :
  Concrete.store_mvec cmem mvec = Some cmem' ->
  mvec_in_kernel cmem'.
Proof.
  unfold Concrete.store_mvec, mvec_in_kernel, in_mvec.
  intros H addr IN.
  destruct (PartMaps.get_upd_list_in H IN)
    as (v' & IN' & GET).
  rewrite GET.
  simpl in IN'.
  repeat match goal with
  | H : _ \/ _ |- _ => destruct H as [E | ?]; [inv E|]
  | H : False |- _ => destruct H
  end; eauto.
Qed.

Lemma mvec_in_kernel_store_mvec cmem mvec :
  mvec_in_kernel cmem ->
  exists cmem',
    Concrete.store_mvec cmem mvec = Some cmem'.
Proof.
  unfold mvec_in_kernel, in_mvec, Concrete.mvec_fields, Concrete.store_mvec.
  intros DEF.
  eapply PartMaps.upd_list_defined; eauto; try apply word_map_axioms.
  simpl map. intros addr IN.
  apply DEF in IN.
  destruct IN.
  eauto.
Qed.

(* CH: kernel_invariant only holds when kernel starts executing, can
   be broken during kernel execution, but has to be restored before
   returning to user mode. It doesn't necessarily have to hold at all
   intermediate kernel steps. Right? *)
(* CH: I find the way the "kernel invariant" is stated rather
   indirect. Is there no direct way to define this? *)
(* AAA: We need to add the cache as an argument here, since we don't
   assume anything about ground rules right now *)

Record kernel_invariant : Type := {
  kernel_invariant_statement :> Concrete.memory mt ->
                                Concrete.registers mt ->
                                Concrete.rules (word mt) ->
                                Symbolic.internal_state -> Prop;

  kernel_invariant_upd_mem :
    forall regs mem1 mem2 cache addr w1 ct ut w2 int
           (KINV : kernel_invariant_statement mem1 regs cache int)
           (GET : PartMaps.get mem1 addr = Some w1@ct)
           (DEC : decode Symbolic.M mem1 ct = Some (USER ut))
           (UPD : PartMaps.upd mem1 addr w2 = Some mem2),
      kernel_invariant_statement mem2 regs cache int;

  kernel_invariant_upd_reg :
    forall mem regs1 regs2 cache r w1 ct1 ut1 w2 ct2 ut2 int
           (KINV : kernel_invariant_statement mem regs1 cache int)
           (GET : PartMaps.get regs1 r = Some w1@ct1)
           (DEC1 : decode Symbolic.R mem ct1 = Some (USER ut1))
           (UPD : PartMaps.upd regs1 r w2@ct2 = Some regs2)
           (DEC2 : decode Symbolic.R mem ct2 = Some (USER ut2)),
      kernel_invariant_statement mem regs2 cache int;

  kernel_invariant_store_mvec :
    forall mem mem' mvec regs cache int
           (KINV : kernel_invariant_statement mem regs cache int)
           (MVEC : Concrete.store_mvec mem mvec = Some mem'),
      kernel_invariant_statement mem' regs cache int
}.

Hint Resolve kernel_invariant_upd_mem.
Hint Resolve kernel_invariant_upd_reg.
Hint Resolve kernel_invariant_store_mvec.

Variable ki : kernel_invariant.

Lemma in_user_in_kernel :
  forall st, in_user st -> ~~ in_kernel st.
Proof.
  move=> st.
  rewrite /in_user /in_kernel /Concrete.is_kernel_tag.
  apply contraTN=> /eqP ->.
  by rewrite decode_kernel_tag.
Qed.

Variable table : list (Symbolic.syscall mt).

Definition is_nop (i : word mt) : bool :=
  match decode_instr i with
  | Some Nop => true
  | _ => false
  end.

Lemma is_nopP : forall i, is_nop i <-> decode_instr i = Some (Nop _).
Proof.
  rewrite /is_nop.
  move => i.
  by case: (decode_instr i) => [[]|] //=.
Qed.

Definition wf_entry_points (cmem : Concrete.memory mt) :=
  forall addr t,
    (exists2 sc, Symbolic.get_syscall table addr = Some sc &
                 Symbolic.entry_tag sc = t) <->
    is_true match PartMaps.get cmem addr with
            | Some i@it => is_nop i && (decode Symbolic.M cmem it == Some (ENTRY t))
            | None => false
            end.

Lemma wf_entry_points_if cmem addr sc :
  wf_entry_points cmem ->
  Symbolic.get_syscall table addr = Some sc ->
  exists i it,
  [/\ PartMaps.get cmem addr = Some i@it,
      decode Symbolic.M cmem it = Some (ENTRY (Symbolic.entry_tag sc)) &
      is_nop i ].
Proof.
  move => WFENTRYPOINTS GETCALL.
  have: exists2 sc', Symbolic.get_syscall table addr = Some sc' &
                     Symbolic.entry_tag sc' = Symbolic.entry_tag sc by eauto.
  move/WFENTRYPOINTS.
  case: (PartMaps.get cmem addr) => [[i it]|] //.
  move/andP => [H1 H2]. exists i, it.
  split; trivial.
  by apply/eqP.
Qed.

Lemma wf_entry_points_only_if cmem addr i it t :
  wf_entry_points cmem ->
  PartMaps.get cmem addr = Some i@it ->
  decode Symbolic.M cmem it = Some (ENTRY t) ->
  is_nop i ->
  exists2 sc,
    Symbolic.get_syscall table addr = Some sc &
    Symbolic.entry_tag sc = t.
Proof.
  move => WF GET DEC ISNOP.
  apply/WF.
  by rewrite GET DEC eqxx andb_true_r.
Qed.

Lemma entry_point_undefined cmem smem addr v it t :
  refine_memory smem cmem ->
  PartMaps.get cmem addr = Some v@it ->
  decode Symbolic.M cmem it = Some (ENTRY t) ->
  PartMaps.get smem addr = None.
Proof.
  move => REFM GET DEC.
  case GET': (PartMaps.get smem addr) => [[v' t']|] //.
  move/(proj2 REFM): GET'.
  rewrite GET. case=> it' H1 [? ?]. subst v' it'. congruence.
Qed.

Inductive refine_state (sst : Symbolic.state mt) (cst : Concrete.state mt) : Prop := RefineState {
  rs_pc : Symbolic.pcv sst = Concrete.pcv cst;
  rs_pct : decode Symbolic.P (Concrete.mem cst) (Concrete.pct cst) =
           Some (USER (Symbolic.pct sst));
  rs_refm : refine_memory (Symbolic.mem sst) (Concrete.mem cst);
  rs_refr : refine_registers (Symbolic.regs sst) (Concrete.regs cst) (Concrete.mem cst);
  rs_cache : cache_correct (Concrete.cache cst) (Concrete.mem cst);
  rs_mvec : mvec_in_kernel (Concrete.mem cst);
  rs_entry_points : wf_entry_points (Concrete.mem cst);
  rs_kinv : ki (Concrete.mem cst) (Concrete.regs cst)
               (Concrete.cache cst) (Symbolic.internal sst)
}.

Lemma refine_state_in_user sst cst :
  refine_state sst cst ->
  in_user cst.
Proof.
  case=> ? DEC *.
  by rewrite /in_user DEC.
Qed.

(* MOVE *)
Lemma decode_ivec_monotonic cmem cmem' addr x y ct st ct' st' :
  PartMaps.get cmem addr = Some x@ct ->
  decode Symbolic.M cmem ct = Some (USER st) ->
  PartMaps.upd cmem addr y@ct' = Some cmem' ->
  decode Symbolic.M cmem ct' = Some (USER st') ->
  decode_ivec e cmem' =1 decode_ivec e cmem.
Proof.
  admit.
Qed.

Lemma decode_ovec_monotonic cmem cmem' op addr x y ct st ct' st' :
  PartMaps.get cmem addr = Some x@ct ->
  decode Symbolic.M cmem ct = Some (USER st) ->
  PartMaps.upd cmem addr y@ct' = Some cmem' ->
  decode Symbolic.M cmem ct' = Some (USER st') ->
  decode_ovec e op cmem' =1 decode_ovec e op cmem.
Proof.
  admit.
Qed.

Lemma refine_memory_upd cache aregs cregs amem cmem cmem' addr v v' ct t ct' t' :
  cache_correct cache cmem ->
  refine_registers aregs cregs cmem ->
  refine_memory amem cmem ->
  PartMaps.get cmem addr = Some v@ct ->
  decode Symbolic.M cmem ct = Some (USER t) ->
  PartMaps.upd cmem addr v'@ct' = Some cmem' ->
  decode Symbolic.M cmem ct' = Some (USER t') ->
  exists amem',
    [/\ PartMaps.upd amem addr v'@t' = Some amem',
        cache_correct cache cmem',
        refine_registers aregs cregs cmem' &
        refine_memory amem' cmem'].
Proof.
  move=> Hcache Hregs Hmem Hget Hdec Hupd Hdec'.
  have Hget' := proj1 Hmem _ _ _ _ Hdec Hget.
  have [amem' Hupd'] := PartMaps.upd_defined v'@t' Hget'.
  have Hdec_eq := decode_monotonic _ Hget Hdec Hupd Hdec'.
  exists amem'. split; trivial.
  - move=> cmvec crvec Hlookup.
    case Hdec_pc: (decode _ _ _) => [pct|] //= Hpct_user.
    rewrite Hdec_eq in Hdec_pc.
    have := Hcache cmvec crvec Hlookup.
    rewrite Hdec_pc => /(_ Hpct_user) [ivec [ovec [Hdec_ivec Hdec_ovec Htrans]]].
    rewrite -(decode_ivec_monotonic Hget Hdec Hupd Hdec') in Hdec_ivec.
    rewrite -(decode_ovec_monotonic _ Hget Hdec Hupd Hdec') in Hdec_ovec.
    by eauto using And3.
  - split.
    + move=> w x ct'' st'' Hdec_ct' Hget''.
      rewrite Hdec_eq in Hdec_ct'.
      by eapply (proj1 Hregs); eauto.
    + move=> w x st'' /(proj2 Hregs _ _ _) [ct'' Hdec_ct'' Hget''].
      rewrite -Hdec_eq in Hdec_ct''.
      by eauto.
  - split.
    + move=> w x ct'' st'' Hdec_ct' Hget''.
      rewrite Hdec_eq in Hdec_ct'.
      have [Heq|Hneq] := w =P addr.
      * subst w.
        rewrite (PartMaps.get_upd_eq Hupd) in Hget''.
        rewrite (PartMaps.get_upd_eq Hupd').
        case: Hget'' => ? ?. subst. congruence.
      * rewrite (PartMaps.get_upd_neq Hneq Hupd) in Hget''.
        rewrite (PartMaps.get_upd_neq Hneq Hupd').
        by eapply (proj1 Hmem); eauto.
    + move=> w x st Hget''.
      have [Heq|Hneq] := w =P addr.
      * subst w.
        rewrite (PartMaps.get_upd_eq Hupd') in Hget''.
        case: Hget'' => ? ?. subst x st.
        exists ct'=> //.
          by rewrite Hdec_eq.
        by rewrite (PartMaps.get_upd_eq Hupd).
      * rewrite (PartMaps.get_upd_neq Hneq Hupd') in Hget''.
        have [ct'' Hdec_ct'' Hget_ct''] := proj2 Hmem _ _ _ Hget''.
        rewrite -(PartMaps.get_upd_neq Hneq Hupd) in Hget_ct''.
        rewrite -Hdec_eq in Hdec_ct''.
        by eauto.
Qed.

Lemma wf_entry_points_user_upd cmem cmem' addr v v' ct t ct' t' :
  wf_entry_points cmem ->
  PartMaps.get cmem addr = Some v@ct ->
  decode Symbolic.M cmem ct = Some (USER t) ->
  PartMaps.upd cmem addr v'@ct' = Some cmem' ->
  decode Symbolic.M cmem ct' = Some (USER t') ->
  wf_entry_points cmem'.
Proof.
  move=> Hwf Hget Hdec Hupd Hdec' addr' t''.
  rewrite (PartMaps.get_upd Hupd) Hwf.
  have [-> {addr'}|_] := altP (addr' =P addr).
    by rewrite Hget (decode_monotonic _ Hget Hdec Hupd Hdec') Hdec Hdec' !andbF.
  case: (PartMaps.get _ _) => [[i ti]|] //.
  by rewrite (decode_monotonic _ Hget Hdec Hupd Hdec').
Qed.

Lemma mvec_in_kernel_user_upd cmem cmem' addr v v' ct t ct' t' :
  mvec_in_kernel cmem ->
  PartMaps.get cmem addr = Some v@ct ->
  decode Symbolic.M cmem ct = Some (USER t) ->
  PartMaps.upd cmem addr v'@ct' = Some cmem' ->
  decode Symbolic.M cmem ct' = Some (USER t') ->
  mvec_in_kernel cmem'.
Proof.
  intros MVEC GET DEC UPD DEC'.
  intros addr' H.
  specialize (MVEC addr' H). destruct MVEC as [w' KER].
  assert (NEQ : addr' <> addr).
  { intros E. subst addr'.
    have CONTRA : Concrete.TKernel = ct by congruence. subst ct.
    by rewrite decode_kernel_tag in DEC. }
  rewrite (PartMaps.get_upd_neq NEQ UPD).
  eauto.
Qed.

Lemma mvec_in_kernel_kernel_upd cmem cmem' addr w :
  mvec_in_kernel cmem ->
  PartMaps.upd cmem addr w@Concrete.TKernel = Some cmem' ->
  mvec_in_kernel cmem'.
Proof.
  intros MVEC UPD addr' IN.
  have [?|/eqP NEQ] := altP (addr' =P addr); simpl in *; subst.
  - erewrite PartMaps.get_upd_eq; eauto. now apply word_map_axioms.
  - rewrite (PartMaps.get_upd_neq NEQ UPD).
    now apply MVEC.
Qed.

Lemma refine_memory_upd' cache aregs cregs amem amem' cmem addr v ct t :
  cache_correct cache cmem ->
  refine_registers aregs cregs cmem ->
  refine_memory amem cmem ->
  PartMaps.upd amem addr v@t = Some amem' ->
  decode Symbolic.M cmem ct = Some (USER t) ->
  exists cmem',
    [/\ PartMaps.upd cmem addr v@ct = Some cmem',
        cache_correct cache cmem',
        refine_registers aregs cregs cmem' &
        refine_memory amem' cmem' ].
Proof.
  move=> Hcache Hregs Hmem Hupd Hdec.
  have [[x t'] Hget] := PartMaps.upd_inv Hupd.
  have [ct' Hdec' Hget'] := proj2 Hmem _ _ _ Hget.
  have [cmem' Hupd'] := PartMaps.upd_defined v@ct Hget'.
  have Hdec_eq := decode_monotonic _ Hget' Hdec' Hupd' Hdec.
  rewrite Hupd'. eexists. split; eauto.
  - move=> cmvec crvec Hlookup.
    rewrite Hdec_eq.
    move=> /(Hcache _ _ Hlookup) [ivec [ovec [Hdec_i Hdec_o Htrans]]].
    rewrite -(decode_ivec_monotonic Hget' Hdec' Hupd' Hdec) in Hdec_i.
    rewrite -(decode_ovec_monotonic _ Hget' Hdec' Hupd' Hdec) in Hdec_o.
    by eauto using And3.
  - split.
    + move=> r x'' ct'' st'' Hdec_ct'' Hget''.
      rewrite Hdec_eq in Hdec_ct''.
      by apply (proj1 Hregs _ _ _ _ Hdec_ct'' Hget'').
    + move=> r x'' st'' /(proj2 Hregs) [ct'' Hdec_ct'' Hget''].
      rewrite -Hdec_eq in Hdec_ct''.
      by eauto.
  - split.
    + move=> w x'' ct'' st''.
      rewrite Hdec_eq (PartMaps.get_upd Hupd) (PartMaps.get_upd Hupd').
      have [_ {w}|_] := altP (w =P addr).
        move=> Hdec_ct'' [Hv Hct]. move: Hv Hct Hdec_ct'' => <- <- {x'' ct''}.
        by rewrite Hdec; move => [->].
      by apply (proj1 Hmem).
    + move=> w x' st'.
      rewrite (PartMaps.get_upd Hupd) (PartMaps.get_upd Hupd').
      case: (w == addr) => [{w} [<- <-] {x' st'}|].
        exists ct=> //.
        by rewrite Hdec_eq.
      move=> /(proj2 Hmem) [ct'' Hdec_ct'' Hget''].
      exists ct''=> //.
      by rewrite Hdec_eq.
Qed.

Lemma refine_registers_upd areg creg creg' cmem r v v' ct t ct' t' :
  refine_registers areg creg cmem ->
  PartMaps.get creg r = Some v@ct ->
  decode Symbolic.R cmem ct = Some (USER t) ->
  PartMaps.upd creg r v'@ct' = Some creg' ->
  decode Symbolic.R cmem ct' = Some (USER t') ->
  exists2 areg',
    PartMaps.upd areg r v'@t' = Some areg' &
    refine_registers areg' creg' cmem.
Proof.
  move=> Hregs Hget Hdec Hupd Hdec'.
  have Hget' := proj1 Hregs _ _ _ _ Hdec Hget.
  have [areg' Hupd'] := PartMaps.upd_defined v'@t' Hget'.
  exists areg'=> //. split.
  - move=> r' x ct'' st''.
    rewrite (PartMaps.get_upd Hupd) (PartMaps.get_upd Hupd').
    case: (r' == r) => [Hdec'' [Hx Hct'']|].
      move: Hx Hct'' Hdec'' => <- <-.
      by rewrite Hdec'=> [[->]].
    by apply (proj1 Hregs).
  - move=> r' x st''.
    rewrite (PartMaps.get_upd Hupd) (PartMaps.get_upd Hupd').
    case: (r' == r) => [[<- <-] {x st''}|]; first by eauto.
    by apply (proj2 Hregs).
Qed.

Lemma refine_registers_upd' areg areg' creg cmem r v ct t :
  refine_registers areg creg cmem ->
  PartMaps.upd areg r v@t = Some areg' ->
  decode _ cmem ct = Some (USER t) ->
  exists2 creg',
    PartMaps.upd creg r v@ct = Some creg' &
    refine_registers areg' creg' cmem.
Proof.
  move=> Hregs Hupd Hdec.
  have [[v0 t0] Hget] := PartMaps.upd_inv Hupd.
  have [ct0 Hdec' Hget'] := proj2 Hregs _ _ _ Hget.
  have [creg' Hupd'] := PartMaps.upd_defined v@ct Hget'.
  exists creg'=> //.
  split.
  - move=> r' x ct' st'.
    rewrite (PartMaps.get_upd Hupd) (PartMaps.get_upd Hupd').
    case: (r' == r) => [Hdec_ct' [Hx Hct']|].
      move: Hx Hct' Hdec_ct' => <- <- {x ct'}.
      by rewrite Hdec => [[<-]].
    by apply (proj1 Hregs).
  - move=> r' x st'.
    rewrite (PartMaps.get_upd Hupd) (PartMaps.get_upd Hupd').
    case: (r' == r) => [[<- <-] {x st'}|]; first by rewrite -Hdec; eauto.
    by apply (proj2 Hregs).
Qed.

Inductive hit_step cst cst' : Prop :=
| hs_intro (USER : in_user cst)
           (USER' : in_user cst')
           (STEP : Concrete.step _ masks cst cst').

Definition kernel_exec kst kst' :=
  restricted_exec (Concrete.step _ masks)
                  (fun s => in_kernel s)
                  kst kst'.
Hint Unfold kernel_exec.

Definition kernel_user_exec kst st : Prop :=
  exec_until (Concrete.step _ masks)
             (fun s => in_kernel s)
             (fun s => ~~ in_kernel s)
             kst st.

Inductive user_kernel_user_step cst cst' : Prop :=
| ukus_intro kst
             (USER : in_user cst)
             (STEP : Concrete.step _ masks cst kst)
             (EXEC : kernel_user_exec kst cst').

Lemma user_kernel_user_step_weaken cst cst' :
  user_kernel_user_step cst cst' ->
  exec (Concrete.step _ masks) cst cst'.
Proof.
  move => [cst'' ? ? ?].
  eapply re_step; trivial; try eassumption.
  eapply exec_until_weaken; eassumption.
Qed.

Definition user_step cst cst' :=
  hit_step cst cst' \/ user_kernel_user_step cst cst'.

Lemma analyze_cache cache cmem cmvec crvec op :
  cache_correct cache cmem ->
  Concrete.cache_lookup cache masks cmvec = Some crvec ->
  oapp (fun x => is_user x) false (decode Symbolic.P cmem (Concrete.ctpc cmvec)) ->
  Concrete.cop cmvec = op_to_word op ->
  if Symbolic.privileged_op op then False else
  exists tpc : Symbolic.ttypes Symbolic.P, decode _ cmem (Concrete.ctpc cmvec) = Some (USER tpc) /\
  ((exists (ti : Symbolic.ttypes Symbolic.M)
           (ts : hlist Symbolic.ttypes (Symbolic.inputs op))
           (rtpc : Symbolic.ttypes Symbolic.P)
           (rt : Symbolic.type_of_result Symbolic.ttypes (Symbolic.outputs op)),
    let ovec := Symbolic.mkOVec rtpc rt in
    [/\ decode _ cmem (Concrete.cti cmvec) = Some (USER ti) ,
        decode_ovec e op cmem crvec = Some ovec ,
        Symbolic.transfer (Symbolic.mkIVec op tpc ti ts) = Some ovec &
        decode_fields e _ cmem (Concrete.ct1 cmvec, Concrete.ct2 cmvec, Concrete.ct3 cmvec) =
        Some (hmap (fun k x => Some (USER x)) ts) ]) \/
   exists t : Symbolic.ttypes Symbolic.M,
     [/\ op = NOP ,
         decode _ cmem (Concrete.cti cmvec) = Some (ENTRY t) &
         Concrete.ctrpc crvec = Concrete.TKernel ]).
Proof.
  case: cmvec => op' tpc ti t1 t2 t3 /= CACHE LOOKUP INUSER EQ. subst op'.
  case: (CACHE _ crvec LOOKUP INUSER) =>
        [[op' tpc' ti' ts] /= [ovec /= [/decode_ivec_inv /= [E1|E1] E2 E3]]];
  rewrite op_to_wordK in E1; last first.
    case: E1 => [[?] ? -> ->]. subst op op'.
    move: E2 => /=.
    have [-> _| //] := (Concrete.ctrpc _ =P _).
    by eauto 11 using And3.
  case: E1 => op'' [? [Hpriv [?] -> ->]]. subst op' op'' => ->.
  rewrite (negbTE Hpriv). eexists. split; eauto.
  case: ovec E2 E3 => trpc tr /=.
  case: (decode _ cmem _) => [[trpc'|?]|] //= DEC.
  by eauto 11 using And4.
Qed.

Lemma miss_state_not_user st st' mvec :
  Concrete.miss_state st mvec = Some st' ->
  in_user st' ->
  False.
Proof.
  intros MISS INUSER.
  apply in_user_in_kernel in INUSER.
  unfold Concrete.miss_state in MISS.
  unfold in_kernel, Concrete.is_kernel_tag in INUSER.
  by match_inv.
Qed.

(*
(* Need to double-check that is_true is not affecting the match below *)
Ltac analyze_cache :=
  match goal with
  | LOOKUP : Concrete.cache_lookup ?cache _ ?mvec = Some ?rvec,
    PC     : PartMaps.get _ ?pc = Some ?i@_,
    INST   : decode_instr ?i = Some _,
    INUSER : in_user (Concrete.mkState _ _ _ ?pc@_ _),
    CACHE  : cache_correct ?cache |- _ =>
    unfold in_user in INUSER; simpl in INUSER;
    assert (CACHEHIT := analyze_cache mvec CACHE LOOKUP INUSER (erefl _));
    simpl in CACHEHIT;
    repeat match type of CACHEHIT with
    | exists _, _ => destruct CACHEHIT as [? CACHEHIT]
    | _ /\ _ => destruct CACHEHIT as [? CACHEHIT]
    | _ \/ _ => destruct CACHEHIT as [CACHEHIT | CACHEHIT]
    | False => destruct CACHEHIT
    end;
    subst mvec; simpl in *; subst;
    try match goal with
    | H : context[decode (encode _)] |- _ =>
      rewrite decodeK in H; simpl in *; subst
    end
  | MISS   : Concrete.miss_state _ _ = Some ?st',
    INUSER : in_user ?st' |- _ =>
    destruct (miss_state_not_user _ _ MISS INUSER)
  end.
*)

Lemma valid_initial_user_instr_tags cst cst' v ti :
  cache_correct (Concrete.cache cst) (Concrete.mem cst) ->
  in_user cst ->
  in_user cst' ->
  Concrete.step _ masks cst cst' ->
  PartMaps.get (Concrete.mem cst) (Concrete.pcv cst) = Some v@ti ->
  oapp (fun x => is_user x) false (decode Symbolic.M (Concrete.mem cst) ti).
Proof.
  move=> Hcache Huser Huser' Hstep Hget.
  have [cmvec [Hcmvec]] := step_lookup_success_or_fault Hstep.
  case Hlookup: (Concrete.cache_lookup _ _ _) => [crvec|].
    have := Hcache _ _ Hlookup.
    rewrite (build_cmvec_ctpc Hcmvec) => /(_ Huser) [ivec [ovec [Hdec_i Hdec_o Htrans]]] Hpc_cst'.
    have := build_cmvec_cop_cti Hcmvec.
    rewrite Hget => [[i [instr [[<- -> {i}] _ _]]]].
    have [[? [? [? ? ? ->]]] //|[_ Hservice _ _]] := decode_ivec_inv Hdec_i.
    move: ovec Huser' {Htrans} Hdec_o.
    rewrite /in_user {}Hservice /= -{}Hpc_cst' => [[]].
    have [->|//] := (_ =P _).
    by rewrite decode_kernel_tag.
  case: (Concrete.store_mvec _ _) => [cmem'|//] Hcst'.
  move: Huser'.
  by rewrite /in_user {}Hcst' /= decode_kernel_tag.
Qed.

Lemma valid_pcs st st' :
  Concrete.step _ masks st st' ->
  cache_correct (Concrete.cache st) (Concrete.mem st) ->
  in_user st ->
  (exists t,
     decode Symbolic.P (Concrete.mem st') (Concrete.pct st') = Some (USER t)) \/
  Concrete.pct st' = Concrete.TKernel.
Proof.
  move=> Hstep Hcache Huser.
  have [cmvec [Hcmvec]] := step_lookup_success_or_fault Hstep.
  case Hlookup: (Concrete.cache_lookup _ _ _) => [crvec|].
    have := Hcache _ _ Hlookup.
    rewrite (build_cmvec_ctpc Hcmvec) => /(_ Huser) [ivec [ovec [Hdec_i Hdec_o Htrans]]] Hpc_st'.
    have [[op [Hop [Hpriv _ _ _ _]]]|] := decode_ivec_inv Hdec_i.
      move: ovec {Htrans} Hdec_o.
      rewrite Hop /= -{}Hpc_st' => ovec.
      case Hdec: (decode Symbolic.P (Concrete.mem st) _) => [[st''|]|] //.
      by admit.
    rewrite {}Hpc_st'.
    case=> _ Hop _ _.
    move: ovec {Htrans} Hdec_o.
    rewrite {}Hop /= => [[]].
    by have [->|//] := _ =P Concrete.TKernel; auto.
  by case: (Concrete.store_mvec _ _) => [cmem'|] // ->; auto.
Qed.

Hint Unfold Symbolic.next_state.
Hint Unfold Symbolic.next_state_reg_and_pc.
Hint Unfold Symbolic.next_state_pc.
Hint Unfold Symbolic.next_state_reg.

Definition user_tags_unchanged cmem cmem' :=
  forall ctg tk stg,
    decode tk cmem ctg = Some stg <->
    decode tk cmem' ctg = Some stg.

Definition user_mem_unchanged (cmem cmem' : Concrete.memory mt) :=
  forall addr (w : word mt) ct t,
    decode Symbolic.M cmem ct = Some t ->
    (PartMaps.get cmem addr = Some w@ct <->
     PartMaps.get cmem' addr = Some w@ct).

Definition user_regs_unchanged (cregs cregs' : Concrete.registers mt) cmem :=
  forall r (w : word mt) ct t,
    decode Symbolic.R cmem ct = Some t ->
    (PartMaps.get cregs r = Some w@ct <->
     PartMaps.get cregs' r = Some w@ct).

Import DoNotation.

(* Returns true iff our machine is at the beginning of a system call
and the cache says it is allowed to execute. To simplify this
definition, we assume that system calls are only allowed to begin with
Nop, which is consistent with how we've defined our symbolic handler
in rules.v. *)
Definition cache_allows_syscall (cst : Concrete.state mt) : bool :=
  match Symbolic.get_syscall table (Concrete.pcv cst) with
  | Some _ =>
    match build_cmvec cst with
    | Some cmvec => Concrete.cache_lookup (Concrete.cache cst) masks cmvec
    | None => false
    end
  | None => false
  end.

Class kernel_code_correctness : Prop := {

(* BCP: Added some comments -- please check! *)
  handler_correct_allowed_case :
  forall mem mem' cmvec ivec ovec reg cache old_pc int,
    (* If kernel invariant holds... *)
    ki mem reg cache int ->
    (* and calling the handler on the current m-vector succeeds and returns rvec... *)
    decode_ivec e mem cmvec = Some ivec ->
    Symbolic.transfer ivec = Some ovec ->
    (* and storing the concrete representation of the m-vector yields new memory mem'... *)
    Concrete.store_mvec mem cmvec = Some mem' ->
    (* and the concrete rule cache is correct (in the sense that every
       rule it holds is exactly the concrete representations of
       some (mvec,rvec) pair in the relation defined by the [handler]
       function) ... *)
    cache_correct cache mem ->
    (* THEN if we start the concrete machine in kernel mode (i.e.,
       with the PC tagged TKernel) at the beginning of the fault
       handler (and with the current memory, and with the current PC
       in the return-addr register epc)) and let it run until it
       reaches a user-mode state st'... *)
    exists st' crvec,
      kernel_user_exec
        (Concrete.mkState mem' reg cache
                          (Concrete.fault_handler_start _)@Concrete.TKernel
                          old_pc)
        st' /\
      (* then the new cache is still correct... *)
      cache_correct (Concrete.cache st') (Concrete.mem st') /\
      (* and the new cache now contains a rule mapping mvec to rvec... *)
      Concrete.cache_lookup (Concrete.cache st') masks cmvec = Some crvec /\
      decode_ovec e (Symbolic.op ivec) (Concrete.mem st') crvec = Some ovec /\
      (* and the mvec has been tagged as kernel data (BCP: why is this important??) *)
      mvec_in_kernel (Concrete.mem st') /\
      (* and we've arrived at the return address that was in epc with
         unchanged user memory and registers... *)
      user_tags_unchanged mem (Concrete.mem st') /\
      user_mem_unchanged mem (Concrete.mem st') /\
      user_regs_unchanged reg (Concrete.regs st') mem /\
      Concrete.pc st' = old_pc /\
      (* and the system call entry points are all tagged ENTRY (BCP:
         Why do we care, and if we do then why isn't this part of the
         kernel invariant?  Could user code possibly change it?) *)
      wf_entry_points (Concrete.mem st') /\
      (* and the kernel invariant still holds. *)
      ki (Concrete.mem st') (Concrete.regs st') (Concrete.cache st') int;

  handler_correct_disallowed_case :
  forall mem mem' cmvec reg cache old_pc int st',
    (* If kernel invariant holds... *)
    ki mem reg cache int ->
    (* and calling the handler on mvec FAILS... *)
    match decode_ivec e mem cmvec with
    | Some ivec => ~~ Symbolic.transfer ivec
    | None => true
    end ->
    (* and storing the concrete representation of the m-vector yields new memory mem'... *)
    Concrete.store_mvec mem cmvec = Some mem' ->
    (* then if we start the concrete machine in kernel mode and let it
       run, it will never reach a user-mode state. *)
    ~~ in_kernel st' ->
    ~ exec (Concrete.step _ masks)
      (Concrete.mkState mem' reg cache
                        (Concrete.fault_handler_start _)@Concrete.TKernel
                        old_pc)
      st';

  syscalls_correct_allowed_case :
  forall amem areg apc atpc int
         amem' areg' apc' atpc' int'
         cmem creg cache ctpc epc sc,
    (* and the kernel invariant holds... *)
    ki cmem creg cache int ->
    (* and the USER-tagged portion of the concrete memory cmem
       corresponds to the abstract (symbolic??) memory amem... *)
    refine_memory amem cmem ->
    (* and the USER-tagged concrete registers in creg correspond to
       the abstract register set areg... *)
    refine_registers areg creg cmem ->
    (* and the rule cache is correct... *)
    cache_correct cache cmem ->
    (* and the mvec has been tagged as kernel data (BCP: again, why is this
       important... and why is it now part of the premises whereas
       upstairs it was part of the conclusion??) *)
    mvec_in_kernel cmem ->
    (* and the symbolic system call at addr is the function
       sc... (BCP: This would make more sense after the next
       hypothesis) *)
    Symbolic.get_syscall table apc = Some sc ->
    (* and running sc on the current abstract machine state reaches a
       new state with primes on everything... *)
    Symbolic.run_syscall sc (Symbolic.State amem areg apc@atpc int) = Some (Symbolic.State amem' areg' apc'@atpc' int') ->
    decode _ cmem ctpc = Some (USER atpc) ->
    let cst := Concrete.mkState cmem
                                creg
                                cache
                                apc@ctpc epc in

    cache_allows_syscall cst ->

    (* THEN if we start the concrete machine in kernel mode at the
       beginning of the corresponding system call code and let it run
       until it reaches a user-mode state with primes on everything... *)

    exists cmem' creg' cache' ctpc' epc',
      user_kernel_user_step cst
                            (Concrete.mkState cmem' creg' cache'
                                              apc'@ctpc' epc') /\

      (* then the new concrete state is in the same relation as before
         with the new abstract state and the same invariants
         hold (BCP: Plus one more about ra!). *)
      decode Symbolic.P cmem' ctpc' = Some (USER atpc') /\
      refine_memory amem' cmem' /\
      refine_registers areg' creg' cmem' /\
      cache_correct cache' cmem' /\
      mvec_in_kernel cmem' /\
      wf_entry_points cmem' /\
      ki cmem' creg' cache' int';

  syscalls_correct_disallowed_case :
  forall amem areg apc atpc int
         cmem creg cache ctpc epc sc
         cst',
    ki cmem creg cache int ->
    refine_memory amem cmem ->
    refine_registers areg creg cmem ->
    cache_correct cache cmem ->
    mvec_in_kernel cmem ->
    wf_entry_points cmem ->
    Symbolic.get_syscall table apc = Some sc ->
    Symbolic.run_syscall sc (Symbolic.State amem areg apc@atpc int) = None ->
    decode _ cmem ctpc = Some (USER atpc) ->
    let cst := Concrete.mkState cmem
                                creg
                                cache
                                apc@ctpc epc in
    cache_allows_syscall cst ->
    ~ user_kernel_user_step cst cst'

}.

End Refinement.
