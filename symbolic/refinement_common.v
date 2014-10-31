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
  (forall w x ctg atg,
     decode Symbolic.R cmem ctg = Some (USER atg) ->
     PartMaps.get creg w = Some x@ctg ->
     PartMaps.get areg w = Some x@atg) /\
  (forall w x atg,
     PartMaps.get areg w = Some x@atg ->
     exists2 ctg,
       decode Symbolic.R cmem ctg = Some (USER atg) &
       PartMaps.get creg w = Some x@ctg).

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
          decode_ovec e (Symbolic.op ivec) cmem crvec = Some ovec,
          Symbolic.transfer ivec = Some ovec &
          ~~ privileged_op (Symbolic.op ivec) ].

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

(*
Lemma is_user_pc_tag_is_kernel_tag tg :
  @word_lift _ _ (e Symbolic.P) (fun x => is_user x) tg -> Concrete.is_kernel_tag tg.
Proof.
  unfold word_lift, is_user, Concrete.is_kernel_tag.
  destruct (decode tg) as [[ut| |]|] eqn:E; try discriminate.
  intros _.
  apply encodeK in E.
  have [E'|//] := eqP.
  rewrite (@encode_kernel_tag _ _ (e Symbolic.P)) in E'.
  rewrite E' in E.
  now apply encode_inj in E.
Qed.
*)

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
    (exists sc, Symbolic.get_syscall table addr = Some sc /\
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
  have: exists sc', Symbolic.get_syscall table addr = Some sc' /\
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
  exists sc,
    Symbolic.get_syscall table addr = Some sc /\
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
  intros CACHE REGS MEM GET DEC UPD DEC'.
  assert (GET' := proj1 MEM _ _ _ _ DEC GET).
  destruct (PartMaps.upd_defined v'@t' GET') as [amem' UPD'].
  admit.
(*
  - apply MEM in GET.
    rewrite (PartMaps.get_upd_eq UPD).
    rewrite (PartMaps.get_upd_eq UPD').
    intros t''. split; try congruence.
    intros H.
    inv H.
    exploit (fun T => @encode_inj mt T); try eassumption; eauto.
    congruence.
  - rewrite (PartMaps.get_upd_neq NEQ UPD').
    rewrite (PartMaps.get_upd_neq NEQ UPD).
    now apply MEM.*)
Qed.

Lemma wf_entry_points_user_upd cmem cmem' addr v v' ct t ct' t' :
  wf_entry_points cmem ->
  PartMaps.get cmem addr = Some v@ct ->
  decode Symbolic.M cmem ct = Some (USER t) ->
  PartMaps.upd cmem addr v'@ct' = Some cmem' ->
  decode Symbolic.M cmem ct' = Some (USER t') ->
  wf_entry_points cmem'.
Proof.
  unfold wf_entry_points.
  intros WF GET UPD addr'.
  admit. (*
  split; intros H.
  - rewrite ->WF in H.
    case MEM: (PartMaps.get cmem addr') H => [[v'' t'']|] H //=.
    erewrite PartMaps.get_upd_neq; try apply word_map_axioms; eauto; first by rewrite MEM.
    intros ?. subst addr'.
    assert (EQ : t'' = encode (USER t)) by congruence. subst.
    move/andP: H => [_ H].
    by move/eqP/encode_inj: H.
  - apply WF. clear WF.
    case GET': (PartMaps.get cmem' addr') H => [[v'' t'']|] H //=.
    erewrite PartMaps.get_upd_neq in GET'; eauto using word_map_axioms.
    { now rewrite GET'. }
    intros ?. subst addr'.
    erewrite PartMaps.get_upd_eq in GET'; eauto using word_map_axioms.
    assert (EQ : t''= encode (USER t')) by congruence. subst.
    move/andP: H => [_ H].
    by move/eqP/encode_inj: H. *)
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
  admit.
Qed.
(*
  intros MEM UPD.
  destruct (PartMaps.upd_inv UPD) as [[w' t'] GET].
  apply MEM in GET.
  eapply PartMaps.upd_defined in GET; auto using word_map_axioms.
  destruct GET as [cmem' UPD'].
  eexists. split; eauto.
  intros addr' w'' t''.
  have [EQ|/eqP NEQ] := altP (addr' =P addr); simpl in *; subst.
  - rewrite (PartMaps.get_upd_eq UPD').
    rewrite (PartMaps.get_upd_eq UPD).
    split; try congruence.
    intros ?.
    assert (E : USER t = USER t''); try congruence.
    eapply encode_inj. congruence.
  - rewrite (PartMaps.get_upd_neq NEQ UPD).
    rewrite (PartMaps.get_upd_neq NEQ UPD').
    now apply MEM.
Qed.
*)

Lemma refine_registers_upd areg creg creg' cmem r v v' ct t ct' t' :
  refine_registers areg creg cmem ->
  PartMaps.get creg r = Some v@ct ->
  decode Symbolic.R cmem ct = Some (USER t) ->
  PartMaps.upd creg r v'@ct' = Some creg' ->
  decode Symbolic.R cmem ct' = Some (USER t') ->
  exists areg',
    PartMaps.upd areg r v'@t' = Some areg' /\
    refine_registers areg' creg' cmem.
Proof.
  admit.
Qed.
(*
  intros REG GET UPD.
  assert (GET' := proj1 (REG _ _ _) GET).
  assert (NEW := PartMaps.upd_defined v'@t' GET').
  destruct NEW as [areg' UPD'].
  eexists. split; eauto.
  intros r' v'' t''.
  have [EQ|/eqP NEQ] := altP (r' =P r); simpl in *; subst.
  - rewrite (PartMaps.get_upd_eq UPD).
    rewrite (PartMaps.get_upd_eq UPD').
    split; try congruence.
    intros ?.
    assert (USER t' = USER t''); try congruence.
    eapply encode_inj; congruence.
  - rewrite (PartMaps.get_upd_neq NEQ UPD).
    rewrite (PartMaps.get_upd_neq NEQ UPD').
    now apply REG.
Qed.
*)

Lemma refine_registers_upd' areg areg' creg cmem r v ct t :
  refine_registers areg creg cmem ->
  PartMaps.upd areg r v@t = Some areg' ->
  decode _ cmem ct = Some (USER t) ->
  exists2 creg',
    PartMaps.upd creg r v@ct = Some creg' &
    refine_registers areg' creg' cmem.
Proof.
  admit.
Qed.
(*
  intros REF UPD.
  move: (PartMaps.upd_inv UPD) => [[v0 t0] /REF GET].
  eapply PartMaps.upd_defined in GET.
  move: GET => [creg' UPD']. rewrite -> UPD'.
  eexists. split; first by [].
  intros r' v' t'.
  have [EQ|/eqP NEQ] := altP (r' =P r); simpl in *.
  - subst r'.
    rewrite (PartMaps.get_upd_eq UPD).
    rewrite (PartMaps.get_upd_eq UPD').
    split; try congruence.
    intros ?.
    assert (USER t' = USER t); try congruence.
    eapply encode_inj; try congruence.
  - rewrite (PartMaps.get_upd_neq NEQ UPD).
    rewrite (PartMaps.get_upd_neq NEQ UPD').
    now apply REF.
Qed.
*)

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
  if privileged_op op then False else
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
        [[op' tpc' ti' ts] /= [ovec /= [/decode_ivec_inv /= [E1|E1] E2 E3 E4]]];
  rewrite op_to_wordK in E1; last first.
    case: E1 => [[?] ? -> ->] {E4}. subst op op'.
    move: E2 => /=.
    have [-> _| //] := (Concrete.ctrpc _ =P _).
    by eauto 11 using And3.
  case: E1 => op'' [? [?] -> ->]. subst op' op'' => ->.
  move: E4 E2 => /= /negbTE ->.
  case: ovec E3 => trpc tr E3.
  case: (decode _ cmem _) => [[trpc'| |?]|] //= DEC.
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
  admit.
Qed.
(*
  intros CACHE INUSER INUSER' STEP GET;
  inv STEP;
  unfold Concrete.next_state_reg, Concrete.next_state_reg_and_pc,
         Concrete.next_state_pc, Concrete.next_state,
         Concrete.miss_state, word_lift in *;
  simpl in *;

  match_inv;

  try analyze_cache;

  try match goal with
  | H1 : PartMaps.get ?mem ?pc = Some _@?w1,
    H2 : PartMaps.get ?mem ?pc = Some _@?w2 |- _ =>
    let EQ := fresh "EQ" in
    assert (EQ : w1 = w2) by congruence;
    try (apply encode_inj in EQ; discriminate EQ);
    subst
  end;

  by [
      rewrite decodeK
    | rewrite /in_user /word_lift ?(@encode_kernel_tag _ _ (e Symbolic.P)) decodeK /= in INUSER'
  ].
Qed.
*)

Lemma valid_pcs st st' :
  Concrete.step _ masks st st' ->
  cache_correct (Concrete.cache st) (Concrete.mem st) ->
  in_user st ->
  (exists t,
     decode Symbolic.P (Concrete.mem st') (Concrete.pct st') = Some (USER t)) \/
  Concrete.pct st' = Concrete.TKernel.
Proof.
  admit.
Qed.
(*
  intros STEP CACHE INUSER. simpl.
  inv STEP;
  unfold Concrete.next_state_reg, Concrete.next_state_reg_and_pc,
         Concrete.next_state_pc, Concrete.next_state,
         Concrete.miss_state in *;
  simpl in *;

  match_inv;

  try analyze_cache;

  simpl in *; try rewrite (@encode_kernel_tag _ _ (e Symbolic.P)); now rewrite decodeK.

Qed.
*)

Lemma refine_ivec sst cst ivec :
  refine_state sst cst ->
  build_ivec table sst = Some ivec ->
  exists2 cmvec,
    build_cmvec cst = Some cmvec &
    decode_ivec e (Concrete.mem cst) cmvec = Some ivec.
Proof.
  admit.
Qed.
(*
  intros [smem sreg int mem reg cache epc pc stpc
               ? ? REFM REFR CACHE MVE WF KI] IVEC.
  subst sst cst.
  rewrite /build_ivec in IVEC.
  match_inv;
  try match goal with
  | H : ?X = _ |- _ =>
    match X with
    | context[match ?E with _ => _ end] =>
      destruct E eqn:?; try discriminate H
    end
  end;
  match_inv;
  repeat match goal with
  | a : atom _ _ |- _ => destruct a
  end;
  repeat match goal with
  | GET : PartMaps.get ?mem _ = Some _,
    REFM : refine_memory ?mem _ |- _ =>
    apply REFM in GET
  | GET : PartMaps.get ?reg _ = Some _,
    REFM : refine_registers ?reg _ |- _ =>
    apply REFR in GET
  end; simpl;
  repeat match goal with
  | E : ?X = _ |- context[?X] => rewrite E; simpl
  end; try solve [ discriminate | eexists; reflexivity ].
  match goal with
  | GET : Symbolic.get_syscall _ _ = Some _,
    WF : wf_entry_points _ |- _ =>
    let EQ := fresh "EQ" in
    let ISNOP := fresh "ISNOP" in
    destruct (wf_entry_points_if _ WF GET) as (? & EQ & ISNOP);
    apply is_nopP in ISNOP; rewrite EQ ISNOP //=
  end.
Qed.
*)

Lemma refine_ivec_inv sst cst cmvec ivec :
  refine_state sst cst ->
  build_cmvec cst = Some cmvec ->
  decode_ivec e (Concrete.mem cst) cmvec = Some ivec ->
  build_ivec table sst = Some ivec.
Proof.
  admit.
Qed.

(*
Lemma handler_build_ivec sst cst cmvec crvec :
  refine_state sst cst ->
  build_cmvec mt cst = Some cmvec ->
  handler cmvec = Some crvec ->
  exists ivec,
    build_ivec table sst = Some ivec.
Proof.
  intros [smem sreg int mem reg cache epc pc stpc
               ? ? REFM REFR CACHE MVE WF KI].
  subst sst cst.
  rewrite /build_cmvec.
  move => CMVEC;
  match_inv;
  match goal with
  | H : ?X = _ |- _ =>
    match X with
    | context[match ?Y with _ => _ end] =>
      destruct Y; match_inv
    end
  end;
  repeat match goal with
  | a : atom _ _ |- _ =>
    destruct a
  end;
  move => HANDLER;
  rewrite /handler /rules.handler ?decodeK /= ?op_to_wordK in HANDLER;
  match_inv;
  try simpl in HANDLER;
  rewrite /decode_ivec /= ?decodeK /= in HANDLER; match_inv;
  try match goal with
  | H : word_to_op (op_to_word _) = Some ?op |- _ =>
    rewrite op_to_wordK in H; inv H
  end;
  repeat match goal with
  | t : hlist _ _ |- _ => simpl in t
  | t : unit |- _ => destruct t
  | t : prod _ _ |- _ => destruct t
  | H : context[ivec_of_ivec] |- _ => unfold ivec_of_ivec in H; simpl in H
  | H : context[decode_fields] |- _ => unfold decode_fields in H; simpl in H
  end;
  unfold omap, obind, oapp in *;
  match_inv;
  repeat match goal with
  | H : decode ?t = Some _ |- _ => apply encodeK in H; subst t
  end;
  repeat match goal with
  | GET : PartMaps.get ?cregs ?r = Some _@(encode (USER _)),
    REFR : refine_registers ?sregs ?cregs |- _ =>
    match goal with
    | GET' : PartMaps.get sregs r = Some _ |- _ => fail 1
    | |- _ => idtac
    end;
    pose proof (proj1 (REFR _ _ _) GET)
  | GET : PartMaps.get ?cmem ?addr = Some ?w@(encode ?t),
    REFM : refine_memory ?smem ?cmem |- _ =>
    match t with
    | USER _ =>
      match goal with
      | GET' : PartMaps.get smem addr = Some _ |- _ => fail 2
      | |- _ => idtac
      end;
      pose proof (proj1 (REFM _ _ _) GET)
    | ENTRY _ =>
      match goal with
      | GET' : PartMaps.get smem addr = None |- _ => fail 2
      | WF : wf_entry_points cmem,
        DEC : decode_instr _ = Some (Nop _) |- _ =>
        pose proof (entry_point_undefined _ _ REFM GET);
        destruct (wf_entry_points_only_if _ _ WF GET (proj2 (is_nopP _) DEC))
          as (? & ? & ?)
      end
    end
  end; simpl;
  repeat match goal with
  | E : ?X = _ |- context[?X] => rewrite E; simpl
  end;
  solve [simpl in *; eauto].
Qed.
*)

Hint Unfold Symbolic.next_state.
Hint Unfold Symbolic.next_state_reg_and_pc.
Hint Unfold Symbolic.next_state_pc.
Hint Unfold Symbolic.next_state_reg.

Definition user_pc_tag_unchanged cmem cmem' :=
  forall ctg atg,
    decode Symbolic.P cmem ctg = Some (USER atg) <->
    decode Symbolic.P cmem' ctg = Some (USER atg).

Definition user_mem_unchanged (cmem cmem' : Concrete.memory mt) :=
  forall addr (w : word mt) ct t,
    (PartMaps.get cmem addr = Some w@ct /\
     decode Symbolic.M cmem ct = Some (USER t)) <->
    (PartMaps.get cmem' addr = Some w@ct /\
     decode Symbolic.M cmem' ct = Some (USER t)).

Definition user_regs_unchanged (cregs cregs' : Concrete.registers mt) cmem cmem' :=
  forall r (w : word mt) ct t,
    (PartMaps.get cregs r = Some w@ct /\
     decode Symbolic.R cmem ct = Some (USER t) <->
     PartMaps.get cregs' r = Some w@ct /\
     decode Symbolic.R cmem' ct = Some (USER t)).

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
      user_pc_tag_unchanged mem (Concrete.mem st') /\
      user_mem_unchanged mem (Concrete.mem st') /\
      user_regs_unchanged reg (Concrete.regs st') mem (Concrete.mem st') /\
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
