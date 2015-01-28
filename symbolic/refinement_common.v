Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import hseq word partmap.

Require Import lib.utils.
Require Import common.types.
Require Import concrete.concrete.
Require Import concrete.exec.
Require Import symbolic.symbolic.
Require Import symbolic.exec.
Require Import symbolic.rules.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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
     cmem w = Some x@ctg ->
     amem w = Some x@atg) /\
  (forall w x atg,
     amem w = Some x@atg ->
     exists2 ctg,
       decode Symbolic.M cmem ctg = Some (USER atg) &
       cmem w = Some x@ctg).

Definition refine_registers (areg : Symbolic.registers mt _)
                            (creg : Concrete.registers mt)
                            (cmem : Concrete.memory mt) :=
  (forall r x ctg atg,
     decode Symbolic.R cmem ctg = Some (USER atg) ->
     creg r = Some x@ctg ->
     areg r = Some x@atg) /\
  (forall r x atg,
     areg r = Some x@atg ->
     exists2 ctg,
       decode Symbolic.R cmem ctg = Some (USER atg) &
       creg r = Some x@ctg).

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

Definition in_mvec addr := addr \in Concrete.mvec_fields mt.

Definition mvec_in_kernel (cmem : Concrete.memory mt) :=
  forall addr,
    in_mvec addr ->
    exists w : mword mt, cmem addr = Some w@Concrete.TKernel.

Lemma store_mvec_mvec_in_kernel cmem mvec :
  mvec_in_kernel (Concrete.store_mvec cmem mvec).
Proof.
move=> k; rewrite /Concrete.store_mvec getm_union.
set m := mkpartmap _.
rewrite -[isSome (m k)]/(k \in m) mem_mkpartmap /in_mvec /Concrete.mvec_fields.
move=> E; rewrite E; have: k \in m by rewrite mem_mkpartmap.
rewrite inE {E}; case E: (m k) => [v|] // _.
move/getm_mkpartmap': E; rewrite !inE.
do !(case/orP=> [/eqP [_ ->]|]; eauto).
by move/eqP => [_ ->]; eauto.
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
                                Concrete.rules (mword mt) ->
                                Symbolic.internal_state -> Prop;

  kernel_invariant_upd_mem :
    forall regs mem1 mem2 cache addr w1 ct ut w2 int
           (KINV : kernel_invariant_statement mem1 regs cache int)
           (GET : mem1 addr = Some w1@ct)
           (DEC : decode Symbolic.M mem1 ct = Some (USER ut))
           (UPD : updm mem1 addr w2 = Some mem2),
      kernel_invariant_statement mem2 regs cache int;

  kernel_invariant_upd_reg :
    forall mem regs1 regs2 cache r w1 ct1 ut1 w2 ct2 ut2 int
           (KINV : kernel_invariant_statement mem regs1 cache int)
           (GET : regs1 r = Some w1@ct1)
           (DEC1 : decode Symbolic.R mem ct1 = Some (USER ut1))
           (UPD : updm regs1 r w2@ct2 = Some regs2)
           (DEC2 : decode Symbolic.R mem ct2 = Some (USER ut2)),
      kernel_invariant_statement mem regs2 cache int;

  kernel_invariant_store_mvec :
    forall mem mvec regs cache int
           (KINV : kernel_invariant_statement mem regs cache int),
      kernel_invariant_statement (Concrete.store_mvec mem mvec)
                                 regs cache int
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

Definition is_nop (i : mword mt) : bool :=
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
    is_true match cmem addr with
            | Some i@it => is_nop i && (decode Symbolic.M cmem it == Some (ENTRY t))
            | None => false
            end.

Lemma wf_entry_points_if cmem addr sc :
  wf_entry_points cmem ->
  Symbolic.get_syscall table addr = Some sc ->
  exists i it,
  [/\ cmem addr = Some i@it,
      decode Symbolic.M cmem it = Some (ENTRY (Symbolic.entry_tag sc)) &
      is_nop i ].
Proof.
  move => WFENTRYPOINTS GETCALL.
  have: exists2 sc', Symbolic.get_syscall table addr = Some sc' &
                     Symbolic.entry_tag sc' = Symbolic.entry_tag sc by eauto.
  move/WFENTRYPOINTS.
  case: (cmem addr) => [[i it]|] //.
  move/andP => [H1 H2]. exists i, it.
  split; trivial.
  by apply/eqP.
Qed.

Lemma wf_entry_points_only_if cmem addr i it t :
  wf_entry_points cmem ->
  cmem addr = Some i@it ->
  decode Symbolic.M cmem it = Some (ENTRY t) ->
  is_nop i ->
  exists2 sc,
    Symbolic.get_syscall table addr = Some sc &
    Symbolic.entry_tag sc = t.
Proof.
  move => WF GET DEC ISNOP.
  apply/WF.
  by rewrite GET DEC eqxx andbT.
Qed.

Lemma entry_point_undefined cmem smem addr v it t :
  refine_memory smem cmem ->
  cmem addr = Some v@it ->
  decode Symbolic.M cmem it = Some (ENTRY t) ->
  smem addr = None.
Proof.
  move => REFM GET DEC.
  case GET': (smem addr) => [[v' t']|] //.
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

Lemma refine_memory_upd cache aregs cregs amem cmem cmem' addr v v' ct t ct' t' :
  cache_correct cache cmem ->
  refine_registers aregs cregs cmem ->
  refine_memory amem cmem ->
  cmem addr = Some v@ct ->
  decode Symbolic.M cmem ct = Some (USER t) ->
  updm cmem addr v'@ct' = Some cmem' ->
  decode Symbolic.M cmem ct' = Some (USER t') ->
  exists amem',
    [/\ updm amem addr v'@t' = Some amem',
        cache_correct cache cmem',
        refine_registers aregs cregs cmem' &
        refine_memory amem' cmem'].
Proof.
  move=> Hcache Hregs Hmem Hget Hdec Hupd Hdec'.
  have Hget' := proj1 Hmem _ _ _ _ Hdec Hget.
  move: Hupd; rewrite /updm Hget Hget' /= => - [<-].
  have Hdec_eq := decode_monotonic v' _ Hget Hdec Hdec'.
  eexists; split; trivial.
  - move=> cmvec crvec Hlookup.
    case Hdec_pc: (decode _ _ _) => [pct|] //= Hpct_user.
    rewrite Hdec_eq in Hdec_pc.
    have := Hcache cmvec crvec Hlookup.
    rewrite Hdec_pc => /(_ Hpct_user) [ivec [ovec [Hdec_ivec Hdec_ovec Htrans]]].
    rewrite -(decode_ivec_monotonic v' Hget Hdec Hdec') in Hdec_ivec.
    rewrite -(decode_ovec_monotonic _ v' Hget Hdec Hdec') in Hdec_ovec.
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
      move: Hget''; rewrite !getm_set.
      have [Heq|Hneq] := w =P addr.
      * subst w; move=> [? ?]; subst; congruence.
      * by eapply (proj1 Hmem); eauto.
    + move=> w x st Hget''; move: Hget'' Hdec_eq; rewrite /updm !getm_set.
      have [_ {w}|Hneq] := altP (w =P addr).
        move => [-> Ht]; eexists ct'=> //.
        by rewrite Hdec_eq Hdec' Ht.
      move=> Hget''.
      have [ct'' Hdec_ct'' Hget_ct''] := proj2 Hmem _ _ _ Hget''.
      rewrite Hget_ct''=> Hdec''; eexists ct''=> //.
      by rewrite Hdec''.
Qed.

Lemma wf_entry_points_user_upd cmem cmem' addr v v' ct t ct' t' :
  wf_entry_points cmem ->
  cmem addr = Some v@ct ->
  decode Symbolic.M cmem ct = Some (USER t) ->
  updm cmem addr v'@ct' = Some cmem' ->
  decode Symbolic.M cmem ct' = Some (USER t') ->
  wf_entry_points cmem'.
Proof.
move=> Hwf Hget Hdec Hupd Hdec' addr' t''; rewrite Hwf.
have := decode_monotonic _ _ Hget Hdec Hdec'.
move: Hupd; rewrite /updm Hget /= => - [<-] {cmem'} Hmono.
rewrite getm_set.
have [-> {addr'}|_] := altP (addr' =P addr).
  by rewrite Hget !Hmono Hdec Hdec' !andbF.
case: (cmem addr') => [[i ti]|] //.
  by rewrite Hmono.
Qed.

Lemma mvec_in_kernel_user_upd cmem cmem' addr v v' ct t ct' t' :
  mvec_in_kernel cmem ->
  cmem addr = Some v@ct ->
  decode Symbolic.M cmem ct = Some (USER t) ->
  updm cmem addr v'@ct' = Some cmem' ->
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
  move: UPD; rewrite /updm GET /= => - [<-].
  by rewrite getm_set (introF eqP NEQ) KER; eauto.
Qed.

Lemma mvec_in_kernel_kernel_upd cmem cmem' addr w :
  mvec_in_kernel cmem ->
  updm cmem addr w@Concrete.TKernel = Some cmem' ->
  mvec_in_kernel cmem'.
Proof.
intros MVEC UPD addr' IN.
move: UPD; rewrite /updm; case: (cmem _) => //= _ [<-].
rewrite getm_set.
by have [?|/eqP NEQ] := altP (addr' =P addr); simpl in *; subst; eauto.
Qed.

Lemma refine_memory_upd' cache aregs cregs amem amem' cmem addr v ct t :
  cache_correct cache cmem ->
  refine_registers aregs cregs cmem ->
  refine_memory amem cmem ->
  updm amem addr v@t = Some amem' ->
  decode Symbolic.M cmem ct = Some (USER t) ->
  exists cmem',
    [/\ updm cmem addr v@ct = Some cmem',
        cache_correct cache cmem',
        refine_registers aregs cregs cmem' &
        refine_memory amem' cmem' ].
Proof.
  move=> Hcache Hregs Hmem Hupd Hdec.
  have [[x t'] Hget] : exists a, amem addr = Some a.
    by move: Hupd; rewrite /updm; case: (amem _); eauto.
  have [ct' Hdec' Hget'] := proj2 Hmem _ _ _ Hget.
  have Hupd' : updm cmem addr v@ct = Some (setm cmem addr v@ct).
    by rewrite /updm Hget'.
  have Hdec_eq := decode_monotonic v _ Hget' Hdec' Hdec.
  rewrite Hupd'. eexists. split; eauto.
  - move=> cmvec crvec Hlookup.
    rewrite Hdec_eq.
    move=> /(Hcache _ _ Hlookup) [ivec [ovec [Hdec_i Hdec_o Htrans]]].
    rewrite -(decode_ivec_monotonic v Hget' Hdec' Hdec) in Hdec_i.
    rewrite -(decode_ovec_monotonic _ v Hget' Hdec' Hdec) in Hdec_o.
    by eauto using And3.
  - split.
    + move=> r x'' ct'' st'' Hdec_ct'' Hget''.
      rewrite Hdec_eq in Hdec_ct''.
      by apply (proj1 Hregs _ _ _ _ Hdec_ct'' Hget'').
    + move=> r x'' st'' /(proj2 Hregs) [ct'' Hdec_ct'' Hget''].
      rewrite -Hdec_eq in Hdec_ct''.
      by eauto.
  - move: Hupd; rewrite /updm Hget=> - [<-] {amem'}; split.
    + move=> w x'' ct'' st''.
      rewrite Hdec_eq !getm_set.
      have [_ {w}|_] := altP (w =P addr).
        move=> Hdec_ct'' [Hv Hct]. move: Hv Hct Hdec_ct'' => <- <- {x'' ct''}.
        by rewrite Hdec; move => [->].
      by apply (proj1 Hmem).
    + move=> w x' st'.
      rewrite !getm_set.
      case: (w == addr) => [{w} [<- <-] {x' st'}|].
        exists ct=> //.
        by rewrite Hdec_eq.
      move=> /(proj2 Hmem) [ct'' Hdec_ct'' Hget''].
      exists ct''=> //.
      by rewrite Hdec_eq.
Qed.

Lemma refine_registers_upd areg creg creg' cmem r v v' ct t ct' t' :
  refine_registers areg creg cmem ->
  creg r = Some v@ct ->
  decode Symbolic.R cmem ct = Some (USER t) ->
  updm creg r v'@ct' = Some creg' ->
  decode Symbolic.R cmem ct' = Some (USER t') ->
  exists2 areg',
    updm areg r v'@t' = Some areg' &
    refine_registers areg' creg' cmem.
Proof.
  move=> Hregs Hget Hdec Hupd Hdec'.
  have Hget' := proj1 Hregs _ _ _ _ Hdec Hget.
  have Hupd' : updm areg r v'@t' = Some (setm areg r v'@t').
    by rewrite /updm Hget'.
  move: Hupd; rewrite {1}/updm Hget /= => - [<-].
  rewrite Hupd'; eexists => //; split.
  - move=> r' x ct'' st''.
    rewrite !getm_set.
    case: (r' == r) => [Hdec'' [Hx Hct'']|].
      move: Hx Hct'' Hdec'' => <- <-.
      by rewrite Hdec'=> [[->]].
    by apply (proj1 Hregs).
  - move=> r' x st''.
    rewrite !getm_set.
    case: (r' == r) => [[<- <-] {x st''}|]; first by eauto.
    by apply (proj2 Hregs).
Qed.

Lemma refine_registers_upd' areg areg' creg cmem r v ct t :
  refine_registers areg creg cmem ->
  updm areg r v@t = Some areg' ->
  decode _ cmem ct = Some (USER t) ->
  exists2 creg',
    updm creg r v@ct = Some creg' &
    refine_registers areg' creg' cmem.
Proof.
  rewrite /updm; case Hget: (areg r)=> [[v0 t0]|] //= Hregs [<-] Hdec.
  have [ct0 Hdec' Hget'] := proj2 Hregs _ _ _ Hget.
  rewrite Hget' /=.
  eexists=> //; split.
  - move=> r' x ct' st'; rewrite !getm_set.
    case: (r' == r) => [Hdec_ct' [Hx Hct']|].
      move: Hx Hct' Hdec_ct' => <- <- {x ct'}.
      by rewrite Hdec => [[<-]].
    by apply (proj1 Hregs).
  - move=> r' x st'; rewrite !getm_set.
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
  Concrete.cop cmvec = word_of_op op ->
  if Symbolic.privileged_op op then False else
  exists tpc : Symbolic.ttypes Symbolic.P, decode _ cmem (Concrete.ctpc cmvec) = Some (USER tpc) /\
  ((exists (ti : Symbolic.ttypes Symbolic.M)
           (ts : hseq Symbolic.ttypes (Symbolic.inputs op))
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
  rewrite mword_of_opK in E1; last first.
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

Lemma miss_state_not_user st mvec :
  ~~ (in_user (Concrete.miss_state st mvec)).
Proof.
  apply/negP=> INUSER.
  apply in_user_in_kernel in INUSER.
  unfold Concrete.miss_state in INUSER.
  unfold in_kernel, Concrete.is_kernel_tag in INUSER.
  by rewrite /= eqxx in INUSER.
Qed.

Lemma valid_initial_user_instr_tags cst cst' v ti :
  cache_correct (Concrete.cache cst) (Concrete.mem cst) ->
  in_user cst ->
  in_user cst' ->
  Concrete.step _ masks cst cst' ->
  Concrete.mem cst (Concrete.pcv cst) = Some v@ti ->
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
  rewrite /= => Hcst'.
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
      case Hdec: (decode Symbolic.P (Concrete.mem st) _) => [[st''|]|] //= Hdec_o.
      suff : @decode _ _ e Symbolic.P (Concrete.mem st') =1
             @decode _ _ e Symbolic.P (Concrete.mem st).
        move=> E. rewrite -E in Hdec. by eauto.
      move/concrete.exec.stepP: Hstep Hcmvec Hdec_i Hdec_o.
      rewrite /step /build_cmvec {1}(Concrete.state_eta st) /=.
      case Hget: (getm _ (Concrete.pcv _)) => [[i cti]|] //=.
      case Hdec_i: (decode_instr i) => [instr|] //=.
      destruct instr; move=> Hstep; match_inv; try by []; move => [?]; subst cmvec;
      unfold Concrete.next_state_reg, Concrete.next_state_pc,
             Concrete.next_state_reg_and_pc, Concrete.next_state in *;
      simpl in *;
      match goal with
      | H : match _ with _ => _ end = Some _ |- _ =>
        rewrite Hlookup in H
      end; match_inv;
      repeat match goal with
      | H : Some _ = Some _ |- _ => inv H; simpl in *
      end; trivial.
      rewrite /decode_ivec mword_of_opK /= => ?.
      match_inv; simpl in *;
      repeat match goal with
      | H : hshead _ = _ |- _ => rewrite /hshead /hnth eq_axiomK /= in H
      | a : atom _ _ |- _ => destruct a
      | H : OP _ = OP _ |- _ => inversion H; subst; clear H
      end; simpl in *; subst.
      move=> H /=; match_inv.
      move: E1; rewrite /updm; case: (getm _ _) => /= [_|] // [<-].
      by eapply decode_monotonic; eauto.
    rewrite {}Hpc_st'.
    case=> _ Hop _ _.
    move: ovec {Htrans} Hdec_o.
    rewrite {}Hop /= => [[]].
    by have [->|//] := _ =P Concrete.TKernel; auto.
  by rewrite /= => ->; auto.
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
  forall addr (w : mword mt) ct t,
    decode Symbolic.M cmem ct = Some t ->
    (cmem addr = Some w@ct <->
     cmem' addr = Some w@ct).

Definition user_regs_unchanged (cregs cregs' : Concrete.registers mt) cmem :=
  forall r (w : mword mt) ct t,
    decode Symbolic.R cmem ct = Some t ->
    (cregs r = Some w@ct <->
     cregs' r = Some w@ct).

Lemma get_reg_no_user sreg reg m r v ctg t :
  refine_registers sreg reg m ->
  getm sreg r = None ->
  getm reg r = Some v@ctg ->
  decode Symbolic.R m ctg = Some t ->
  exists ut, t = rules.ENTRY ut.
Proof.
  intros REF SGET GET DEC.
  destruct t.
  - move: (proj1 REF r v ctg ut DEC GET).
    by rewrite SGET.
  - eexists; reflexivity.
Qed.

Lemma get_mem_no_user smem mem addr v ctg t :
  refine_memory smem mem ->
  getm smem addr = None ->
  getm mem addr = Some v@ctg ->
  decode Symbolic.M mem ctg = Some t ->
  exists ut, t = rules.ENTRY ut.
Proof.
  intros REF SGET GET DEC.
  destruct t.
  - move: (proj1 REF addr v ctg ut DEC GET).
    by rewrite SGET.
  - eexists; reflexivity.
Qed.

Lemma in_user_ctpc cst :
  in_user cst ->
  exists ut,
    decode Symbolic.P (Concrete.mem cst) (taga (Concrete.pc cst)) = Some (rules.USER ut).
Proof.
  rewrite /in_user /=.
  by case: (decode _ _) => [[?|?]|] //=; eauto.
Qed.

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

Class kernel_code_fwd_correctness : Prop := {

(* BCP: Added some comments -- please check! *)
  handler_correct_allowed_case_fwd :
  forall mem cmvec ivec ovec reg cache old_pc int,
    (* If kernel invariant holds... *)
    ki mem reg cache int ->
    (* and calling the handler on the current m-vector succeeds and returns rvec... *)
    decode_ivec e mem cmvec = Some ivec ->
    Symbolic.transfer ivec = Some ovec ->
    (* and storing the concrete representation of the m-vector yields new memory mem'... *)
    let mem' := Concrete.store_mvec mem cmvec in
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

  syscalls_correct_allowed_case_fwd :
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
      ki cmem' creg' cache' int'

}.

Class kernel_code_bwd_correctness : Prop := {

  handler_correct_allowed_case_bwd :
  forall mem cmvec reg cache old_pc int st',
    ki mem reg cache int ->
    let mem' := Concrete.store_mvec mem cmvec in
    cache_correct cache mem ->
    kernel_user_exec
        (Concrete.mkState mem' reg cache
                          (Concrete.fault_handler_start _)@Concrete.TKernel
                          old_pc)
        st' ->
    exists ivec ovec,
      decode_ivec e mem cmvec = Some ivec /\
      Symbolic.transfer ivec = Some ovec /\
      cache_correct (Concrete.cache st') (Concrete.mem st') /\
      mvec_in_kernel (Concrete.mem st') /\
      user_tags_unchanged mem (Concrete.mem st') /\
      user_mem_unchanged mem (Concrete.mem st') /\
      user_regs_unchanged reg (Concrete.regs st') mem /\
      Concrete.pc st' = old_pc /\
      wf_entry_points (Concrete.mem st') /\
      ki (Concrete.mem st') (Concrete.regs st') (Concrete.cache st') int;

  handler_correct_disallowed_case :
  forall mem cmvec reg cache old_pc int st',
    (* If kernel invariant holds... *)
    ki mem reg cache int ->
    (* and calling the handler on mvec FAILS... *)
    match decode_ivec e mem cmvec with
    | Some ivec => ~~ Symbolic.transfer ivec
    | None => true
    end ->
    (* and storing the concrete representation of the m-vector yields new memory mem'... *)
    let mem' := Concrete.store_mvec mem cmvec in
    (* then if we start the concrete machine in kernel mode and let it
       run, it will never reach a user-mode state. *)
    ~~ in_kernel st' ->
    ~ exec (Concrete.step _ masks)
      (Concrete.mkState mem' reg cache
                        (Concrete.fault_handler_start _)@Concrete.TKernel
                        old_pc)
      st';

  syscalls_correct_allowed_case_bwd :
  forall amem areg apc atpc int
         cmem creg cache ctpc epc
         cmem' creg' cache' cpc' ctpc' epc' sc,
    ki cmem creg cache int ->
    refine_memory amem cmem ->
    refine_registers areg creg cmem ->
    cache_correct cache cmem ->
    mvec_in_kernel cmem ->
    Symbolic.get_syscall table apc = Some sc ->
    decode _ cmem ctpc = Some (USER atpc) ->
    let cst := Concrete.mkState cmem
                                creg
                                cache
                                apc@ctpc epc in
    cache_allows_syscall cst ->
    user_kernel_user_step cst
                          (Concrete.mkState cmem' creg' cache'
                                            cpc'@ctpc' epc') ->
    exists amem' areg' atpc' int',
      Symbolic.run_syscall sc (Symbolic.State amem areg apc@atpc int) =
      Some (Symbolic.State amem' areg' cpc'@atpc' int') /\
      decode Symbolic.P cmem' ctpc' = Some (USER atpc') /\
      refine_memory amem' cmem' /\
      refine_registers areg' creg' cmem' /\
      cache_correct cache' cmem' /\
      mvec_in_kernel cmem' /\
      wf_entry_points cmem' /\
      ki cmem' creg' cache' int'

}.

End Refinement.
