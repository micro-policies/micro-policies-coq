From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From extructures Require Import ord fset fmap.
From CoqUtils Require Import word.

Require Import lib.utils lib.fmap_utils.
Require Import common.types.
Require Import symbolic.symbolic.
Require Import cfi.abstract.
Require Import cfi.symbolic.
Require Import cfi.rules.
Require Import cfi.classes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module RefinementAS.

Section Refinement.

Context {mt : machine_types}
        {ops : machine_ops mt}
        {opss : machine_ops_spec ops}
        {ids : cfi_id mt}.

Variable cfg : id -> id -> bool.

(* Instantiate the symbolic machine with the CFI stuff*)
Instance sym_params : Symbolic.params := Sym.sym_cfi cfg.

Variable atable : Abs.syscall_table mt.
Variable stable : Symbolic.syscall_table mt.

Implicit Types (smem : Sym.memory mt ids cfg).

(*Refinement related definitions*)
Definition refine_dmemory (admem : Abs.dmemory mt)
                          smem :=
  forall w (x : mword mt),
    getm smem w = Some x@DATA <->
    getm admem w = Some x.

Definition refine_imemory (aimem : Abs.imemory mt)
                          smem :=
  forall w x,
    (exists id, getm smem w = Some x@(INSTR id)) <->
    getm aimem w = Some x.

Definition refine_registers (areg : Abs.registers mt)
                            (sreg : Sym.registers mt ids cfg) :=
  forall n (x : mword mt),
    getm sreg n = Some x@DATA <->
    getm areg n = Some x.

Definition refine_pc
           (apc : mword mt)
           (spc : atom (mword mt) (Symbolic.tag_type Symbolic.ttypes Symbolic.P)) :=
  apc = vala spc /\
  (taga spc = DATA \/
   exists id, taga spc = INSTR (Some id)).

Lemma refine_memory_total aimem admem smem :
  refine_imemory aimem smem ->
  refine_dmemory admem smem ->
  (forall addr, getm aimem addr = None /\ getm admem addr = None <->
                getm smem addr = None).
Proof.
  intros REFI REFD addr.
  split.
  { intros [AGETI AGETD].
    destruct (getm smem addr) eqn:GET.
    - destruct a as [v [id|]].
      + assert (EGET: exists id, getm smem addr = Some v@(INSTR id))
          by (eexists; eauto).
        apply REFI in EGET. congruence.
      + apply REFD in GET.
        congruence.
    - reflexivity.
  }
  { intros GET. split.
    - destruct (getm aimem addr) eqn:AGET.
      + apply REFI in AGET.
      destruct AGET as [id AGET]. congruence.
      + reflexivity.
    - destruct (getm admem addr) eqn:AGET.
      + apply REFD in AGET.
        congruence.
      + reflexivity.
  }
Qed.

(*Some useless lemmas, just for sanity check -- probably to be removed*)
Lemma xxx : forall tpc ti,
    (tpc = DATA \/ tpc = INSTR None \/
     (exists src dst, tpc = INSTR (Some src) /\
                      ti = INSTR (Some dst) /\
                      cfg src dst)) <->
    (forall src, tpc = INSTR (Some src) ->
       exists dst, ti = INSTR (Some dst) /\ cfg src dst).
Proof.
  split.
  - intro H.
    destruct H as [? | [? | [src [dst [TPC [TI VALID]]]]]]; try (intros; congruence).
    intros src0 TPC'.
    rewrite TPC in TPC'. inversion TPC'; subst.
    eexists; eauto.
  - intros H.
    destruct tpc.
    + right. destruct o.
      * right.
        assert (H' := H s).
        destruct H' as [dst [? ?]]. reflexivity.
        eexists; eexists; eauto.
      * left; reflexivity.
    + left; reflexivity.
Qed.

Lemma yyy : forall tpc ti,
   match tpc with
   | INSTR (Some src) =>
     exists dst, ti = INSTR (Some dst) /\ cfg src dst
   | _ => True
   end
    <->
    (forall src, tpc = INSTR (Some src) ->
       exists dst, ti = INSTR (Some dst) /\ cfg src dst).
Proof.
  intros tpc ti.
  split.
  - destruct tpc.
    * destruct o.
      + intros H src H'. inversion H'; subst. assumption.
      + intros ? src CONTRA. inversion CONTRA.
    * intros ? ? CONTRA; inversion CONTRA.
  - intros H.
    destruct tpc.
    * destruct o.
      + apply H; reflexivity.
      + auto.
    * auto.
Qed.

Definition refine_state (ast : Abs.state mt)
                        (sst : @Symbolic.state mt sym_params) :=
  let '(Abs.State imem dmem aregs apc cont) := ast in
  let '(Symbolic.State smem sregs spc@tpc _) := sst in
  refine_imemory imem smem /\
  refine_dmemory dmem smem /\
  refine_registers aregs sregs /\
  refine_pc apc (spc@tpc) /\
  (forall i ti,
    getm smem spc = Some i@ti ->
    (cont <->
    (forall src, tpc = INSTR (Some src) ->
       exists dst, ti = INSTR (Some dst) /\ cfg src dst))) /\
  (forall sc, getm smem spc = None ->
   stable spc = Some sc ->
   (cont <->
    (forall src,
       tpc = INSTR (Some src) ->
       exists dst,
         (Symbolic.entry_tag sc) = INSTR (Some dst) /\ cfg src dst))) /\
  Sym.invariants stable sst.

Definition refine_syscall acall scall :=
  forall ast sst,
    refine_state ast sst ->
    match acall ast, scall sst with
    | Some ares, Some sres => refine_state ares sres
    | None, None => True
    | _, _ => False
    end.

Definition syscall_domains
           (atbl : Abs.syscall_table mt)
           (stbl : Symbolic.syscall_table mt) : Prop :=
  forall addr,
    (exists acall, atbl addr = Some acall) <->
    (exists scall, stbl addr = Some scall).

Lemma same_domain_total :
  forall atbl stbl,
    syscall_domains atbl stbl ->
    forall addr', atbl addr' = None <->
                  stbl addr' = None.
Proof.
  intros atbl stbl SAME addr'.
  assert (ACALL: forall addr'', atbl addr'' = None \/
                         exists ac, atbl addr'' = Some ac).
  { intros addr'';
    destruct (atbl addr'');
    [right; eexists; eauto | left; reflexivity].
  }
  assert (SCALL: forall addr'', stbl addr'' = None \/
                         exists sc, stbl addr'' = Some sc).
  { intros addr''.
    destruct (stbl addr'');
      [right; eexists; eauto | left; reflexivity].
  }
  split.
  - intro ACALL'.
    destruct (SCALL addr') as [? | CONTRA];
      [assumption | apply SAME in CONTRA; destruct CONTRA; congruence].
  - intro SCALL'.
    destruct (ACALL addr') as [? | CONTRA];
      [assumption | apply SAME in CONTRA; destruct CONTRA; congruence].
Qed.

(* Might need absence of duplicates in these maps? *)
(* Could use pointwise, and pointwise -> same_domains *)
Definition refine_syscalls
           (atbl : Abs.syscall_table mt)
           (stbl : Symbolic.syscall_table mt) : Prop :=
  forall addr,
    match atbl addr, stbl addr with
    | Some acall, Some scall =>
      refine_syscall (@Abs.sem mt acall)
                     (@Symbolic.run_syscall mt sym_params scall)
    | None, None => True
    | _, _ => False
    end.

Lemma refine_syscalls_domains : forall atbl stbl,
  refine_syscalls atbl stbl ->
  syscall_domains atbl stbl.
Proof.
  intros atbl stbl REFS.
  intro addr.
  specialize (REFS addr).
  split.
  - intros [? AGET].
    rewrite AGET in REFS.
    destruct (stbl addr) eqn:SGET.
    + eexists; reflexivity.
    + destruct REFS.
  - intros [? SGET].
    rewrite SGET in REFS.
    destruct (atbl addr) eqn:AGET.
    + eexists; reflexivity.
    + destruct REFS.
Qed.

Hypothesis refine_syscalls_correct : refine_syscalls atable stable.

Lemma syscalls_backwards_simulation ast sst addr sc sst' :
    refine_syscalls atable stable ->
    stable addr = Some sc ->
    refine_state ast sst ->
    Symbolic.run_syscall sc sst = Some sst' ->
    exists ac ast',
      atable addr = Some ac /\
      Abs.sem ac ast = Some ast' /\
      refine_state ast' sst'.
Proof.
  intros. unfold refine_syscalls in *. specialize (H addr).
  rewrite H0 in H. destruct (atable addr); [| contradiction H].
  specialize (H _ _ H1). rewrite H2 in H.
  destruct (Abs.sem s ast) eqn:?; [| contradiction H].
  do 2 eexists. split. reflexivity. split. eassumption. assumption.
Qed.

Hypothesis syscall_sem :
  forall ac ast ast',
    @Abs.sem mt ac ast = Some ast' ->
       let '(Abs.State imem _ _ _ b) := ast in
       let '(Abs.State imem' _ _ _ b') := ast' in
         imem = imem' /\ b' = b.

(*We will need stronger assumption on symbolic system calls for fwd simulation?*)
Hypothesis syscall_preserves_instruction_tags :
  forall sc st st',
    Sym.instructions_tagged (cfg := cfg) (Symbolic.mem st) ->
    Symbolic.sem sc st = Some st' ->
    Sym.instructions_tagged (cfg := cfg) (Symbolic.mem st').

Hypothesis syscall_preserves_valid_jmp_tags :
  forall sc st st',
    Sym.valid_jmp_tagged stable (Symbolic.mem st) ->
    Symbolic.sem sc st = Some st' ->
    Sym.valid_jmp_tagged stable (Symbolic.mem st').

Hypothesis syscall_preserves_entry_tags :
  forall sc st st',
    Sym.entry_points_tagged stable (Symbolic.mem st) ->
    Symbolic.sem sc st = Some st' ->
    Sym.entry_points_tagged stable (Symbolic.mem st').

Hypothesis syscall_preserves_register_tags :
  forall sc st st',
    Sym.registers_tagged (cfg := cfg) (Symbolic.regs st) ->
    Symbolic.sem sc st = Some st' ->
    Sym.registers_tagged (cfg := cfg) (Symbolic.regs st').

Hypothesis syscall_preserves_jump_tags :
  forall sc st st',
    Sym.jumps_tagged (cfg := cfg) (Symbolic.mem st) ->
    Symbolic.sem sc st = Some st' ->
    Sym.jumps_tagged (Symbolic.mem st').

Hypothesis syscall_preserves_jal_tags :
  forall sc st st',
    Sym.jals_tagged (cfg := cfg) (Symbolic.mem st) ->
    Symbolic.sem sc st = Some st' ->
    Sym.jals_tagged (Symbolic.mem st').

Import Vector.VectorNotations.

Lemma refine_registers_upd sreg sreg' areg r v v' :
  refine_registers areg sreg ->
  getm sreg r = Some v@DATA ->
  updm sreg r v'@DATA = Some sreg' ->
  exists areg',
    updm areg r v' = Some areg' /\
    refine_registers areg' sreg'.
Proof.
  intros REFR GET UPD.
  apply REFR in GET.
  assert (NEW := updm_defined v' GET).
  destruct NEW as [areg' UPD'].
  eexists; split; eauto.
  unfold refine_registers. intros r' v''.
  have [EQ|/eqP NEQ] := altP (r' =P r); [simpl in EQ | simpl in NEQ]; subst.
  *
    rewrite (getm_upd_eq UPD').
    rewrite (getm_upd_eq UPD).
    split.
    - intro H. inversion H; reflexivity.
    - intro H. inversion H; reflexivity.
  * rewrite (getm_upd_neq NEQ UPD).
    rewrite (getm_upd_neq NEQ UPD').
    auto.
Qed.

Lemma refine_memory_upd smem smem' amemd addr v v' :
  refine_dmemory amemd smem ->
  getm smem addr = Some v@DATA ->
  updm smem addr v'@DATA = Some smem' ->
  exists amemd',
    updm amemd addr v' = Some amemd' /\
    refine_dmemory amemd' smem'.
Proof.
  intros MEM GET UPD.
  assert (GET': getm amemd addr = Some v)
    by (apply MEM in GET; auto).
  destruct (updm_defined v' GET') as [amem' UPD'].
  do 2 eexists; eauto.
  intros addr' w'.
  have [EQ|/eqP NEQ] := altP (addr' =P addr); [simpl in EQ | simpl in NEQ]; subst.
  - rewrite (getm_upd_eq UPD).
    rewrite (getm_upd_eq UPD').
    split; simpl; try congruence.
  - rewrite (getm_upd_neq NEQ UPD').
    rewrite (getm_upd_neq NEQ UPD).
    now apply MEM.
Qed.

Lemma data_memory_upd (smem : @Symbolic.memory mt sym_params) smem' addr v v' :
  getm smem addr = Some v@DATA ->
  updm smem addr v'@DATA = Some smem' ->
  (forall addr' i id,
     getm smem addr' = Some i@(INSTR id) ->
     getm smem' addr' = Some i@(INSTR id)).
Proof.
  intros GET UPD addr' i id GET'.
  have [EQ|/eqP NEQ] := altP (addr' =P addr); [simpl in EQ | simpl in NEQ]; subst.
  * rewrite GET in GET'. discriminate.
  * rewrite (getm_upd_neq NEQ UPD);
    assumption.
Qed.

Lemma imem_upd_preservation amemi (smem : @Symbolic.memory mt sym_params)
      (smem' : @Symbolic.memory mt sym_params) addr v v' :
  refine_imemory amemi smem ->
  getm smem addr = Some v@DATA ->
  updm smem addr v'@DATA = Some smem' ->
  refine_imemory amemi smem'.
Proof.
  intros MEM GET UPD w x.
  split.
  - intros (id & GET').
    have [EQ|/eqP NEQ] := altP (addr =P w); [simpl in EQ | simpl in NEQ]; subst.
    * assert (CONTRA := getm_upd_eq UPD).
      simpl in CONTRA. rewrite CONTRA in GET'. discriminate.
    * simpl in UPD. eapply getm_upd_neq in UPD; eauto; try apply word_map_axioms.
      simpl in UPD. rewrite UPD in GET'.
      eapply MEM; eauto.
  - intro GET'.
    apply MEM in GET'.
    have [EQ|/eqP NEQ] := altP (addr =P w); [simpl in EQ | simpl in NEQ]; subst.
    * simpl in GET. rewrite GET in GET'. destruct GET'; congruence.
    * simpl in UPD.
      eapply getm_upd_neq in UPD; eauto; try apply word_map_axioms.
      simpl in UPD; rewrite UPD; assumption.
Qed.


Lemma refine_imemory_none aimem smem pc :
  refine_imemory aimem smem ->
  getm smem pc = None ->
  getm aimem pc = None.
Proof.
  intros REF GET.
  case E: (getm aimem pc) => [i|] //.
  move/(REF _ _): E => [? ?]; congruence.
Qed.

Hint Resolve Sym.itags_preserved_by_step : invariant_db.
Hint Resolve Sym.entry_point_tags_preserved_by_step : invariant_db.
Hint Resolve Sym.valid_jmp_tagged_preserved_by_step : invariant_db.

Theorem backwards_simulation ast sst sst' :
  refine_state ast sst ->
  Symbolic.step stable sst sst' ->
  exists ast',
    Abs.step atable cfg ast ast' /\
    refine_state ast' sst'.
Proof.
  intros REF SSTEP;
  destruct ast as [imem dmem aregs apc b];
  destruct b.
  { (*1st case*)
    inversion SSTEP; subst;
    destruct REF
      as [REFI [REFD [REFR [REFPC [CORRECTNESS [SYSCORRECT [ITG [VTG [ETG [RTG [JUTG JATG]]]]]]]]]]];
    simpl in *;
    (*unfoldings and case analysis on tags*)
    repeat (
        match goal with
          | [H: refine_pc _ _ |- _] =>
            unfold refine_pc in H; simpl in H; destruct H as [? ?]
          | [H: Symbolic.next_state_pc _ _ _ = _ |- _] =>
            unfold Symbolic.next_state_pc in H
          | [H: Symbolic.next_state_reg _ _ _ _ = _ |- _] =>
            unfold Symbolic.next_state_reg in H
          | [H: Symbolic.next_state_reg_and_pc _ _ _ _ _ = _ |- _] =>
            unfold Symbolic.next_state_reg_and_pc in H
          | [H: Symbolic.next_state _ _ = Some _ |- _] =>
            unfold Symbolic.next_state in H; simpl in H
        end); match_inv;
    repeat match goal with
    | H : ?b = true |- _ =>
      change (b = true) with (is_true b) in H
    end;
 (* switch memory updates to abstract*)
    repeat (
        match goal with
          | [H: updm ?Mem ?Addr ?V@_ = Some _,
                H1 : refine_dmemory _ ?Mem,
                     H2: getm ?Mem ?Addr = Some _ |- _] =>
            simpl in H;
          destruct (refine_memory_upd H1 H2 H) as [dmem' [? ?]]
        end);
    (*switch memory and register reads to abstract*)
    try match goal with
          | [H1: refine_imemory _ ?Mem,
                 H2: getm ?Mem ?Pc = Some ?I@(INSTR _) |- _] =>
            assert (exists id, getm Mem Pc = Some I@(INSTR id))
              by (eexists;eauto)
        end;
    (* prove that all register reads have DATA tag*)
    repeat match goal with
        | [H1: Sym.registers_tagged ?Reg, H: getm ?Reg ?R = Some ?V@?TG |- _] =>
          assert (TMP: TG = DATA)
            by (apply H1 in H; assumption);
          assert (getm Reg R = Some V@DATA /\ True)
            by (subst; auto);
          clear H TMP
           end;
      repeat match goal with
               | [H: getm _ _ = _ /\ True |- _] =>
                 destruct H as [? TMP];
                   clear TMP
             end;
      (*Refine registers update - unsure about this part - it seems to still work*)
     try match goal with
           | [H: refine_registers _ _, H1: getm _ ?R = Some _,
                                           H2: updm _ ?R ?V'@_ = Some _ |- _] =>
             try (unfold default_rtag in H2; simpl in H2);
               destruct (refine_registers_upd H H1 H2) as [aregs' [? ?]]
           end;
    (*do refinements*)
    repeat match goal with
             | [H1: refine_imemory _ ?Mem,
                    H2: exists _, getm ?Mem _ = Some _@(INSTR _) |- _] =>
               apply H1 in H2
             | [H1: refine_dmemory _ ?Mem, H2: getm ?Mem _ = Some _@DATA |- _] =>
               apply H1 in H2
             | [H1: refine_registers _ ?Reg,
                    H2: getm ?Reg ?R = Some ?Old@_ |- _] =>
               apply H1 in H2
           end;
    auto;
    pose proof (refine_syscalls_domains refine_syscalls_correct) as DOMAIN;
    (* put into context stuff required for syscalls *)
    match goal with
      | [H1: getm _ ?W = Some ?Sc,
             H2: Symbolic.run_syscall ?Sc _ = Some ?St
         |- _] => (
          assert (EGETCALL: exists sc, stable W = Some sc)
          by (eexists; eauto);
          destruct (DOMAIN W) as [ASDOM SADOM];
          apply SADOM in EGETCALL; destruct EGETCALL;
          assert (REF: refine_state (Abs.State imem dmem aregs pc true)
                                    (Symbolic.State mem reg pc@tpc extra))
            by (repeat (split; auto));
          destruct (syscalls_backwards_simulation (*(Abs.State imem dmem aregs pc true)*)
                                                  (*@Symbolic.State _ sym_params mem reg pc@tpc extra*)
                                                  (*W*)
                                                  refine_syscalls_correct H1
                                                  REF CALL) as
              [ac [ast' [GETCALL' [CALL' FINALREF]]]];
          destruct ast' as [imem' dmem' aregs' apc' b];
          destruct (syscall_sem CALL') as
              [? ?];
          subst
        ) || fail 4 "Couldn't analyze syscall"
      | |- _ => idtac
    end;
    (*handle abstract steps*)
    repeat (match goal with
              | [|- exists _,  _ /\ _] => eexists; split
              | [|- Abs.step _ _ _ _] => s_econstructor eassumption
              | [H: decode_instr _ = Some (Load _ _) |- Abs.step _ _ _ _] =>
                eapply Abs.step_load; eauto
              | [H: getm ?Mem ?Addr = Some ?V@?TG, H1: refine_imemory _ _,
                  H2: refine_dmemory _ _ |- getm _ ?Addr =  _ \/ getm _ ?Addr = _] =>
                (*for load*)
                destruct TG;
                  [left;
                    assert(MEMLOAD: exists id, getm Mem Addr = Some V@(INSTR id))
                     by (eexists; eauto); apply H1 in MEMLOAD; eassumption |
                   right; apply H2 in H; eassumption]
              | [H: decode_instr _ = Some (Store _ _) |- Abs.step _ _ _ _] =>
                eapply Abs.step_store; eauto
              | [H: decode_instr _ = Some (Jump _ ) |- Abs.step _ _ _ _] =>
                eapply Abs.step_jump; eauto
              | [H: decode_instr _ = Some (Bnz _ _) |- Abs.step _ _ _ _] =>
                eapply Abs.step_bnz; eauto
              | [H: decode_instr _ = Some (Jal _ ) |- Abs.step _ _ _ _] =>
                eapply Abs.step_jal; eauto
              | [H: getm _ ?Pc = None, H1: refine_imemory _ _,
                     H2: refine_dmemory _ _ |- _] =>
                  destruct (refine_memory_total H1 H2 Pc) as [? NOMEM];
                  destruct (NOMEM H)
              | [H1: getm stable _ = Some _
                 |- Abs.step _ _ _ _] =>
                 eapply Abs.step_syscall; eauto
            end); auto; (*this auto solves syscall ref*)
    unfold refine_state;
    repeat (match goal with
              | [|- _ /\ _] => split; [eauto | idtac]
              | [H: refine_imemory ?Imem ?Mem |- refine_imemory ?Imem ?Mem] =>
                assumption
              | [H: refine_imemory ?Imem ?Mem |- refine_imemory ?Imem ?Mem'] =>
                eapply imem_upd_preservation; eauto
              | [|- refine_pc _ _] => unfold refine_pc; simpl; auto
              | [|- INSTR _ = DATA \/ _ ] => right; eexists; eauto
              | [H: refine_dmemory dmem ?Mem |- getm ?Mem _ = Some _] =>
                eapply H; eauto
            end);
    (*handle the correctness part*)
    repeat match goal with
             | [|- _ <-> _] => simpl; split
             | [|- true = true] => reflexivity
             | [|- _ -> _] => intros
             | [H: INSTR _ = INSTR _ |- _ ] => inv H
           end;
    try match goal with
          | [H: is_true (Abs.valid_jmp _ _ _) |- _] =>
            destruct (VTG _ _ H) as [[? ?] [[? ?] | [? [? [? ?]]]]]
        end;
    repeat match goal with
             | [H: getm ?Mem ?W = _, H1: getm ?Mem ?W = _ |- _] =>
               rewrite H in H1; inv H1
             | [H: _ = word_to_id _ |- _] =>
               symmetry in H
             | [H:getm stable ?W = _,
                H1: getm stable ?W = _ |- _] =>
               rewrite H in H1; inv H1
           end;
     try match goal with
          | [H: is_true (Abs.valid_jmp _ _ _) |- _] =>
            destruct (valid_jmp_true H) as [? [? [? ?]]]
        end;
    repeat match goal with
             | [H: word_to_id ?Pc = _ , H1: word_to_id ?Pc = _
                |- _] => rewrite H in H1; inv H1
             | [H: Symbolic.entry_tag ?X = _ |- context[Symbolic.entry_tag ?X]] =>
               rewrite H
             | [H: word_to_id ?W = _ |- context[word_to_id ?W]] =>
               rewrite H
             | [H: is_true (Abs.valid_jmp _ _ _) |- _] =>
               unfold Abs.valid_jmp, valid_jmp in H
             | [H: context[?Expr], H1: ?Expr = _ |- _] =>
               rewrite H1 in H; simpl in H
           end;
    try discriminate; (*do not initialize existential when it's contradiction*)
    try match goal with
             | [|-exists _, _] => by (eexists; eauto)
    end;
    (*from symbolic to abstract correctness*)
    repeat match goal with
             | [H: forall _, INSTR _ = INSTR _ -> _ |- _] =>
               destruct (H _ erefl) as [? [? ?]]; clear H; subst
             | [H: getm ?Mem ?W = Some _, H1: getm ?Mem ?Pc = Some _ |-
                is_true (Abs.valid_jmp _ ?Pc ?W)] =>
               apply ITG in H; apply ITG in H1;
               unfold Abs.valid_jmp, valid_jmp;
               rewrite H H1;
               by assumption
           end;
    (*for syscall*)
    repeat match goal with
          | [H: getm ?Mem ?W = None, H1: getm stable ?W = Some ?Sc,
             H2: Symbolic.entry_tag ?Sc = _
             |- is_true (Abs.valid_jmp _ _ _)] =>
              assert (ETAG := ETG _ _ _ H H1 H2)
          | [H1: getm ?Mem ?Pc = Some _ |- is_true (Abs.valid_jmp _ _ _)] =>
            apply ITG in H1;
            unfold Abs.valid_jmp, valid_jmp
          | [H: ?Expr = _ |- is_true match ?Expr with _ => _ end] =>
            rewrite H
          | [H: is_true (cfg ?A ?B) |- cfg ?A ?B = true] => by assumption
        end;
    (*re-establishing invariants*)
   repeat match goal with
             | [|- Sym.invariants _ ?St'] =>
               unfold Sym.invariants
             | [|- _ /\ _] => split; try (simpl; assumption)
             | [|- Sym.instructions_tagged _] =>
               eapply Sym.itags_preserved_by_step; eauto; simpl; auto
             | [ |- Sym.valid_jmp_tagged _ _] =>
               eapply Sym.valid_jmp_tagged_preserved_by_step; eauto; simpl; auto
             | [ |- Sym.entry_points_tagged _ _] =>
               eapply Sym.entry_point_tags_preserved_by_step; eauto; simpl; auto
             | [ |- Sym.registers_tagged _] =>
               eapply Sym.register_tags_preserved_by_step; eauto; simpl; auto
             | [ |- Sym.jumps_tagged _] =>
               eapply Sym.jump_tags_preserved_by_step; eauto; simpl; auto
             | [ |- Sym.jals_tagged _] =>
               eapply Sym.jal_tags_preserved_by_step; eauto; simpl; auto
        end; simpl; trivial.
  }
  { inversion SSTEP; subst;
    destruct REF as [REFI [REFD [REFR [REFPC [CORRECTNESS [SYSCORRECT INV]]]]]];
    match goal with
      | [H : refine_pc _ ?Pc@_, H': getm _ ?Pc = Some ?I@?Ti |- _] =>
        destruct (CORRECTNESS I Ti H') as [? ABSURD]
      | [H : refine_pc _ ?Pc@_, H' : getm _ ?Pc = None,
             H'': getm stable _ = Some _ |- _] =>
        destruct (SYSCORRECT _ H' H'') as [? ABSURD]
    end;
    (*unfoldings and case analysis on tags*)
    repeat (
        match goal with
          | [H: refine_pc _ _ |- _] => unfold refine_pc in H; simpl in H
          | [H: Symbolic.next_state_pc _ _ _ = _ |- _] =>
            unfold Symbolic.next_state_pc in H
          | [H: Symbolic.next_state_reg _ _ _ _ = _ |- _] =>
            unfold Symbolic.next_state_reg in H
          | [H: Symbolic.next_state_reg_and_pc _ _ _ _ _ = _ |- _] =>
            unfold Symbolic.next_state_reg_and_pc in H
          | [H: Symbolic.next_state _ _ = Some _ |- _] =>
            unfold Symbolic.next_state in H; simpl in H
          | [H: Symbolic.run_syscall _ _ = Some _ |- _] =>
            unfold Symbolic.run_syscall in H;
            unfold Symbolic.transfer in H; simpl in H
        end); match_inv; subst;
    repeat match goal with
    | H : ?b = true |- _ =>
      change (b = true) with (is_true b) in H
    end; assert (false);
    try match goal with
          | [H: _ -> is_true false |- is_true false] => apply H
        end; try discriminate;
    repeat match goal with
             | [|- forall _, _] => intros
             | [H: INSTR _ = INSTR _ |- _] => inversion H; subst; clear H
             | [H: DATA = INSTR _ |- _] => inversion H
             | [|- exists _, _] => eexists; eauto
           end.
  }
Qed.

Definition untag_atom (a : atom (mword mt) cfi_tag) := vala a.

Lemma reg_refinement_preserved_by_equiv :
  forall areg reg reg',
    Sym.registers_tagged reg ->
    refine_registers areg reg ->
    Sym.equiv reg reg' ->
    refine_registers (mapm untag_atom reg') reg'.
Proof.
  intros areg reg reg' RTG REF EQUIV.
  unfold Sym.equiv in EQUIV.
  unfold refine_registers in REF.
  assert (MAP := mapmE untag_atom reg').
  intros r v.
  split.
  - intro GET.
    assert (MAP' := MAP r).
    rewrite /= GET in MAP'.
    simpl in MAP'. by assumption.
  - intro GET'.
    assert (MAP' := MAP r).
    rewrite /= GET' in MAP'.
    case GET'': (reg' r) MAP' => [[v' tg]|] //= MAP'.
    inv MAP'.
    specialize (EQUIV r).
    rewrite GET'' in EQUIV.
    destruct (getm reg r) as [[vold told]|] eqn:GET;
    rewrite GET in EQUIV; try contradiction.
    apply RTG in GET. subst.
    by inv EQUIV; simpl in *; subst.
Qed.

Lemma imem_refinement_preserved_by_equiv :
  forall imem mem mem',
    refine_imemory imem mem ->
    Sym.equiv mem mem' ->
    refine_imemory imem mem'.
Proof.
  intros imem mem mem' REF EQUIV.
  unfold Sym.equiv in EQUIV.
  intros addr v.
  split.
  - destruct (REF addr v) as [MEMSA MEMAS].
    intro GET.
    assert (EQUIV' := EQUIV addr). clear EQUIV.
    case GET': (mem addr) EQUIV' MEMSA=> [v'|] //= EQUIV' MEMSA.
    + assert (GET'' := GET).
      destruct GET as [id GET].
      rewrite GET in EQUIV'. inversion EQUIV'; subst.
      * simpl in H0. congruence.
      * rewrite GET in GET''. apply MEMSA in GET''. assumption.
    + destruct GET as [? GET].
      by rewrite GET in EQUIV'.
  - intro GET.
    assert (EQUIV' := EQUIV addr); clear EQUIV.
    case GET': (mem addr) EQUIV'=> [v'|] //= EQUIV'.
    + case GET'': (mem' addr) EQUIV'=> [v''|] EQUIV'.
      * destruct EQUIV' as [TG TG' | id' id'' TG TG' EQ].
        { unfold refine_imemory in REF. apply REF in GET.
          destruct GET as [id GET].
          rewrite GET' in GET. destruct v' as [v' tg]; subst.
          simpl in TG. congruence. }
        { subst. apply REF in GET.  destruct GET as [id''' GET].
          rewrite GET' in GET. exists id'''. assumption.
        }
      * destruct EQUIV'.
    + apply REF in GET. destruct GET as [? GET]. rewrite GET in GET'. congruence.
Qed.

Definition is_data (a : atom (mword mt) cfi_tag) :=
  match taga a with
    | DATA => true
    | INSTR _ => false
  end.

Lemma refine_dmemory_domains dmem mem :
  refine_dmemory dmem mem ->
  domm dmem = domm (filterm (fun _ v => is_data v) mem).
Proof.
  intros REF; apply/eq_fset=> addr.
  unfold refine_dmemory in REF; rewrite !mem_domm.
  case GET: (dmem addr)=> [v|].
  + by rewrite filtermE; move/REF in GET; rewrite GET /=.
  + rewrite filtermE; case GET': (mem addr)=> [[? [|]]|] //=.
    by move/REF in GET'; rewrite GET' in GET.
Qed.

Lemma dmem_refinement_preserved_by_equiv :
  forall dmem mem mem',
    refine_dmemory dmem mem ->
    Sym.equiv mem mem' ->
    exists dmem',
      refine_dmemory dmem' mem'.
Proof.
  intros dmem mem mem' REF EQUIV.
  exists (mapm untag_atom (filterm (fun _ v => is_data v) mem')); subst.
  intros addr v; rewrite mapmE /= filtermE /=.
  split; first by move=> ->.
  by case GET: (mem' addr) => [[v' [|]]|] //= [?]; subst v'.
Qed.

Lemma dmem_domain_preserved_by_equiv :
  forall dmem dmem' mem mem',
    refine_dmemory dmem mem ->
    Sym.equiv mem mem' ->
    refine_dmemory dmem' mem' ->
    domm dmem = domm dmem'.
Proof.
move=> dmem dmem' mem mem' REF EQUIV REF'.
have DOMAINMM' := Sym.equiv_same_domain EQUIV.
rewrite (refine_dmemory_domains REF') (refine_dmemory_domains REF).
apply/filter_domains=> // addr; move: (EQUIV addr).
by case E: (mem addr) => [[v [o|]]|];
case E': (mem' addr) => [[v' [o'|]]|] //=; case.
Qed.

Lemma refine_reg_domains areg reg :
  refine_registers areg reg ->
  Sym.registers_tagged reg ->
  domm areg = domm reg.
Proof.
move=> REF RTG; apply/eq_fset=> n; rewrite !mem_domm.
unfold refine_registers in REF.
case GET: (areg n) => [v|].
+ case GET': (reg n) => [v'|].
  * auto.
  * apply REF in GET.
    rewrite GET in GET'. congruence.
+ case GET': (reg n) => [v'|].
  * destruct v' as [v ut].
    assert (ut = DATA)
      by (apply RTG in GET'; assumption); subst.
    apply REF in GET'.
    congruence.
  * constructor.
Qed.

Lemma reg_domain_preserved_by_equiv :
  forall areg areg' reg reg',
    refine_registers areg reg ->
    Sym.registers_tagged reg ->
    Sym.equiv reg reg' ->
    refine_registers areg' reg' ->
    domm areg = domm areg'.
Proof.
  intros areg areg' reg reg' REF RTG EQUIV REF'.
  unfold pointwise.
  apply/eq_fset=> n; rewrite !mem_domm.
  assert (RTG' : Sym.registers_tagged (cfg := cfg) reg')
    by (eapply Sym.register_tags_preserved_by_step_a'; eauto).
  assert (DOMAIN : domm areg = domm reg)
    by (apply refine_reg_domains; auto).
  assert (DOMAIN' : domm areg' = domm reg')
    by (apply refine_reg_domains; auto).
  assert (EQUIV' := EQUIV n). clear EQUIV.
  destruct (getm reg n) eqn:GET, (getm reg' n) eqn:GET'; rewrite GET in EQUIV'.
  { destruct a as [v ut], a0 as [v' ut'].
    assert (ut = DATA) by (apply RTG in GET; assumption).
    assert (ut' = DATA) by (apply RTG' in GET'; assumption).
    subst.
    apply REF in GET. apply REF' in GET'.
    rewrite GET GET'. constructor.
  }
  { destruct EQUIV'. }
  { destruct EQUIV'. }
  { move/dommPn: GET'; rewrite -DOMAIN' => /dommPn ->.
    by move/dommPn: GET; rewrite -DOMAIN => /dommPn ->. }
Qed.

Theorem backwards_simulation_attacker ast sst sst' :
  refine_state ast sst ->
  Sym.step_a sst sst' ->
  exists ast',
    Abs.step_a ast ast' /\
    refine_state ast' sst'.
Proof.
  intros REF SSTEP.
  destruct ast as [imem dmem aregs apc b].
  inversion SSTEP; subst;
  unfold refine_state in REF;
  destruct REF as [REFI [REFD [REFR [REFPC [CORRECTNESS [SYSCORRECT [ITG [VTG [ETG [RTG FWD]]]]]]]]]];
  unfold refine_pc in REFPC; simpl in REFPC; destruct REFPC as [? TPC]; subst.
  assert (REFR' := reg_refinement_preserved_by_equiv RTG REFR REQUIV);
  assert (REFI' := imem_refinement_preserved_by_equiv REFI MEQUIV);
  destruct (dmem_refinement_preserved_by_equiv REFD MEQUIV) as [dmem' REFD'];
  assert (DOMAINM := dmem_domain_preserved_by_equiv REFD MEQUIV REFD').
  assert (DOMAINR := reg_domain_preserved_by_equiv REFR RTG REQUIV REFR').
  exists (Abs.State imem dmem' (mapm untag_atom reg') pc b).
  split; [s_econstructor eauto | split; auto].
  split; auto.
  split; auto.
  split.
  unfold refine_pc. split; auto.
  split=> [i ti H|].
  { (*proof of correctness for instructions*)
     split.
     - intros CONT src TAG.
       unfold Sym.equiv in MEQUIV.
       assert (MEQUIV' := MEQUIV pc); clear MEQUIV; rewrite H in MEQUIV'.
       destruct (mem pc) eqn:hmem => //.
       destruct MEQUIV' as [TG1 TG2 | id' id'' TG TG' EQ].
         destruct a as [av atg].
         destruct (CORRECTNESS av atg hmem) as [CORRECT ?].
         subst tpc.
         simpl in TG1. subst atg.
         by move: (CORRECT CONT _ erefl) => [? [ ]] //=.
       subst.
       move: CORRECTNESS => /(_ _ _ hmem) CORRECTNESS.
       move/CORRECTNESS: CONT => {CORRECTNESS} /(_ _ erefl).
       by simpl in TG, TG'; subst.
     - intros CORRECT'.
       assert (MEQUIV' := MEQUIV pc); clear MEQUIV.
       destruct (getm mem pc) eqn:GET.
       { rewrite H in MEQUIV'.
         + inversion MEQUIV' as [TG1 TG2 | id' id'' TG TG' EQ]; subst.
           - destruct a as [av atg].
             simpl in TG1. rewrite TG1 in GET.
             simpl in TG2.
             destruct TPC as [TPC | [? TPC]]; subst.
             * move: CORRECTNESS => /(_ _ _ GET) CORRECTNESS.
               apply CORRECTNESS.
               intros ? CONTRA. by discriminate.
             * specialize (CORRECT' x erefl).
               destruct CORRECT' as [dst [TI VALID]].
               discriminate.
           - simpl in *.
             apply (CORRECTNESS _ _ GET).
             assumption.
       }
       { rewrite H in MEQUIV'. destruct MEQUIV'. }
  }
  { split.
    - (*proof for syscall correctness*)
      intros sc H GETCALL.
      split.
      + intros CONT src TPC'.
        specialize (MEQUIV pc).
        rewrite H in MEQUIV.
        destruct (getm mem pc) eqn:GET.
        * destruct MEQUIV.
        * specialize (SYSCORRECT sc GET GETCALL).
          destruct SYSCORRECT as [SYS ?].
          specialize (SYS CONT src TPC').
          assumption.
      + intros CORRECT'.
        specialize (MEQUIV pc).
        rewrite H in MEQUIV.
        destruct (getm mem pc) eqn:GET.
        * destruct MEQUIV.
        * specialize (SYSCORRECT sc GET GETCALL).
          apply SYSCORRECT; auto.
    - assert (Sym.invariants stable (Symbolic.State mem reg pc@tpc int))
        by (repeat (split; auto)).
      eauto using Sym.invariants_preserved_by_step_a.
  }
Qed.

(*Lemmas for forward simulation - Started after POPL 2015 submission*)

Lemma refine_registers_upd_fwd reg reg' sreg r v' :
  refine_registers reg sreg ->
  updm reg r v' = Some reg' ->
  exists sreg',
    updm sreg r v'@DATA = Some sreg' /\
    refine_registers reg' sreg'.
Proof.
  intros REFR UPD.
  destruct (updm_inv UPD) as [v GET].
  apply REFR in GET.
  assert (NEW := updm_defined (v'@DATA) GET).
  destruct NEW as [sreg' UPD'].
  eexists; split; eauto.
  unfold refine_registers. intros r' v''.
  have [EQ|/eqP NEQ] := altP (r' =P r); [simpl in EQ | simpl in NEQ]; subst.
  *
    rewrite (getm_upd_eq UPD').
    rewrite (getm_upd_eq UPD).
    split.
    - intro H. inversion H; reflexivity.
    - intro H. inversion H; reflexivity.
  * rewrite (getm_upd_neq NEQ UPD).
    rewrite (getm_upd_neq NEQ UPD').
    auto.
Qed.

Lemma refine_memory_upd_fwd dmem dmem' smem addr v' :
  refine_dmemory dmem smem ->
  updm dmem addr v' = Some dmem' ->
  exists smem',
    updm smem addr v'@DATA = Some smem' /\
    refine_dmemory dmem' smem'.
Proof.
  intros REFM UPD.
  destruct (updm_inv UPD) as [v GET].
  apply REFM in GET.
  assert (NEW := updm_defined (v'@DATA) GET).
  destruct NEW as [sreg' UPD'].
  eexists; split; eauto.
  unfold refine_dmemory. intros addr' v''.
  have [EQ|/eqP NEQ] := altP (addr' =P addr); [simpl in EQ | simpl in NEQ]; subst.
  *
    rewrite (getm_upd_eq UPD').
    rewrite (getm_upd_eq UPD).
    split.
    - intro H. inversion H; reflexivity.
    - intro H. inversion H; reflexivity.
  * rewrite (getm_upd_neq NEQ UPD).
    rewrite (getm_upd_neq NEQ UPD').
    auto.
Qed.

Lemma refine_memory_none aimem admem smem pc :
  refine_imemory aimem smem ->
  refine_dmemory admem smem ->
  getm aimem pc = None ->
  getm admem pc = None ->
  getm smem pc = None.
Proof.
  intros REFI REFD GETI GETD.
  case GET: (getm smem pc) => [[v [x|]]|] //.
  - assert (EGET: exists x, getm smem pc = Some v@(INSTR x))
                            by (eexists; eauto).
    apply REFI in EGET.
    by congruence.
  - apply REFD in GET.
    by congruence.
Qed.

End Refinement.

End RefinementAS.
