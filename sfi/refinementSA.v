Require Import List. Import ListNotations.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Require Import lib.utils lib.ordered lib.partial_maps common.common.
Require Import symbolic.symbolic symbolic.rules.
Require Import sfi.haskell_notation.
Require Import sfi.classes sfi.list_utils sfi.set_utils sfi.isolate_sets.
Require Import sfi.abstract sfi.abstract_slow sfi.symbolic.

Set Bullet Behavior "Strict Subproofs".
Import DoNotation.

Section RefinementSA.

Set Implicit Arguments.

Import PartMaps.
Import Sym.EnhancedDo.

(* I want to use S and I as variables. *)
Let S := Datatypes.S.
Let I := Logic.I.
(* ssreflect exposes `succn' as a synonym for `S' *)
Local Notation II := Logic.I.

Context
  (t            : machine_types)
  {ops          : machine_ops t}
  {spec         : machine_ops_spec ops}
  {ap           : abstract_params t}
  {ap_spec      : params_spec ap}
  {sfi_syscalls : sfi_syscall_params t}
  {smemory      : Type}
  {smem_class   : partial_map smemory (word t) (atom (word t) (@Sym.stag t))}
  {smem_axioms  : axioms smem_class}
  {sregisters   : Type}
  {sreg_class   : partial_map sregisters (reg t) (atom (word t) (@Sym.stag t))}
  {sreg_axioms  : axioms sreg_class}.

Notation word    := (word t).
Notation stag    := (@Sym.stag t).
Notation sym_sfi := (@Sym.sym_sfi t ops smemory smem_class sregisters sreg_class).

Notation astate  := (@Abs.state t ap).
Notation astate' := (@AbsSlow.state t ap).
Notation sstate  := (@Symbolic.state t sym_sfi).

Notation astep  := Abs.step.
Notation astep' := AbsSlow.step.
Notation sstep  := Sym.step.

Notation satom  := (atom word stag).
Notation svalue := (@val word stag).
Notation slabel := (@common.tag word stag).

(* We check the compartment stuff later *)
Definition refine_pc_b (apc : word) (spc : satom) :=
  match spc with
    | spc' @ (Sym.PC _ _) => apc == spc'
    | _                   => false
  end.

(* We check the compartment stuff later *)
Definition refine_mem_loc_b (ax : word) (sx : satom) : bool :=
  match sx with
    | sx' @ (Sym.DATA _ _ _) => ax == sx'
    | _                      => false
  end.

Definition refine_reg_b (ar : word) (sr : satom) : bool :=
  match sr with
    | sr' @ Sym.REG => ar == sr'
    | _             => false
  end.

Definition refine_memory : memory -> smemory -> Prop :=
  pointwise refine_mem_loc_b.

Definition refine_registers : registers -> sregisters -> Prop :=
  pointwise refine_reg_b.

Section With_EqType_refine_compartment_b.
Import Sym.
Definition refine_compartment_b (c : Abs.compartment t)
                                (smem : smemory) : bool :=
  is_some $
    let: Abs.Compartment A J S := c in
    do! sxs <- map_options (get smem) A;
    do! sc  <- the =<< map_options (stag_compartment ∘ slabel) sxs;
               (* modulo emptiness *)
    do! guard? forallb (set_elem sc) <$>
                 map_options (stag_incoming ∘ slabel <=< get smem) J;
    do! guard? forallb (set_elem sc) <$>
                 map_options (stag_writers  ∘ slabel <=< get smem) S;
    Some tt.
End With_EqType_refine_compartment_b.

Definition refine_compartment_tag (C   : list (Abs.compartment t))
                                  (sst : sstate)
                                  (p   : word) : Prop :=
  match get (Symbolic.mem sst) p with
    | Some (_ @ (Sym.DATA cid I W)) =>
      (exists c,
         Abs.in_compartment p C c /\
         forall p',
           match get (Symbolic.mem sst) p' with
             | Some (_ @ (Sym.DATA cid' _ _)) => cid = cid' ->
                                                 Abs.in_compartment p' C c
             | Some (_ @ _)                   => False
             | None                           => True
           end) /\
        is_some (assoc_list_lookup (Sym.set_ids (Symbolic.internal sst))
                                   (eq_op I)) /\
        is_some (assoc_list_lookup (Sym.set_ids (Symbolic.internal sst))
                                   (eq_op W))
    | Some (_ @ _) =>
      False
    | None =>
      True
  end.

Definition refine_compartments (C : list (Abs.compartment t))
                               (sst : sstate) : Prop :=
  forallb (refine_compartment_b ^~ (Symbolic.mem sst)) C /\
  (forall p, refine_compartment_tag C sst p) /\
  forallb (fun set_id => let: (set,id) := set_id in
             is_set set && (id <? (Sym.next_id (Symbolic.internal sst))))
          (Sym.set_ids (Symbolic.internal sst)).
    (* This last condition is just what we need to guarantee that the symbolic
       state is good if the abstract state is. *)

Record refine_astate (ast : astate) (sst : sstate) : Prop := RefineState
  { pc_refined          : refine_pc_b         (Abs.pc   ast) (Symbolic.pc   sst)
  ; regs_refined        : refine_registers    (Abs.regs ast) (Symbolic.regs sst)
  ; mems_refined        : refine_memory       (Abs.mem  ast) (Symbolic.mem  sst)
  ; compartments_refine : refine_compartments (Abs.compartments ast) sst }.

Inductive refine_astate' : astate' -> sstate -> Prop :=
| refine_none : forall sst, (~ exists sst', sstep sst sst') ->
                            refine_astate' None sst
| refine_some : forall ast sst, refine_astate ast sst ->
                                refine_astate' (Some ast) sst.

Generalizable All Variables.

Theorem refine_good : forall `(REFINE : refine_astate ast sst),
  Abs.good_state ast ->
  Sym.good_state sst.
Proof.
  clear S I.
  intros [Apc AR AM AC] [SM SR [Spc Lpc] [Snext Sids]] [RPC RREGS RMEMS RCOMPS]
         GOOD;
    simpl in *;
    unfold refine_compartments in RCOMPS; simpl in RCOMPS;
    destruct RCOMPS as [RCOMPS [RTAGS ROK]];
  unfold Sym.good_state, Abs.good_state in *; simpl in *;
    move: GOOD => /andP [ICO GOOD].
  repeat split.
  - intros p; unfold Sym.good_memory_tag.
    unfold refine_memory, pointwise in RMEMS; specialize RMEMS with p.
    specialize RTAGS with p; unfold refine_compartment_tag in RTAGS;
      simpl in RTAGS.
    destruct (get SM p) as [[Sx SL]|] eqn:SGET; rewrite SGET in RTAGS *;
      [|trivial].
    destruct (get AM p) as [Ax|] eqn:AGET; [simpl in RMEMS | elim RMEMS].
    destruct SL as [|c I W|]; solve [apply/andP; tauto | done].
  - intros r; unfold Sym.good_register_tag.
    unfold refine_registers, pointwise in RREGS; specialize RREGS with r.
    destruct (get SR r) as [[Sx SL]|] eqn:SGET; rewrite SGET; [|trivial].
    destruct (get AR r) as [Ax|] eqn:AGET; [|elim RREGS].
    unfold refine_reg_b in RREGS.
    by destruct SL.
  - by destruct Lpc.
  - exact ROK.
Qed.

Ltac unoption :=
  repeat match goal with
    | EQ  : Some _ = Some _ |- _ => inversion EQ; subst; clear EQ
    | NEQ : Some _ = None   |- _ => discriminate
    | NEQ : None   = Some   |- _ => discriminate
    | EQ  : None   = None   |- _ => clear EQ
  end.

(* For greppability *)
Tactic Notation "slowness" "admit" :=
  match goal with
    | |- Abs.in_compartment (_ + _)%w _ _ => admit
    | _ => fail "Not a slowness case!"
  end.

(* This *really* needs to be cleaned up! *)
Theorem backward_simulation : forall ast sst sst',
  refine_astate' ast sst ->
  sstep sst sst' ->
  exists ast',
    astep' ast ast' /\
    refine_astate' ast' sst'.
Proof.
  clear S I; move=> ast sst sst' REFINE SSTEP.
  destruct REFINE as [sst NOT|ast sst REFINE]; [elim NOT; eauto|]; simpl in *.
  destruct REFINE as [RPC RREGS RMEMS RCOMP], ast as [Apc AR AM AC]; simpl in *.
  destruct SSTEP; subst; try subst mvec;
    unfold Symbolic.next_state_reg, Symbolic.next_state_pc,
           Symbolic.next_state_reg_and_pc, Symbolic.next_state in *;
    simpl in *;
    unfold Sym.rvec_next, Sym.rvec_jump, Sym.rvec_store, Sym.rvec_simple,
           Sym.rvec_step in *;
    simpl in *.
  - (* Nop *)
    undo1 NEXT rvec; undo1 def_rvec cid;
      unfold Sym.can_execute,Sym.sfi_rvec in *; unoption; simpl in *.
    destruct tpc as [S cid'| |]; try discriminate;
      destruct ti as [|cid'' I W|]; try discriminate.
    move/eqP in RPC; subst Apc.
    exists (Some (Abs.State (pc+1)%w AR AM AC)); split.
    + eapply AbsSlow.step_go; try reflexivity.
      rewrite /refine_compartments /refine_compartment_tag /= in RCOMP;
        move: RCOMP => [RCOMPS [RCTAGS RCOK]].
      specialize RCTAGS with pc; rewrite PC in RCTAGS.
      destruct RCTAGS as [[c [IN_c IN_SAME]] [OK_I OK_W]].
      eapply Abs.step_nop; try reflexivity.
      * unfold Abs.decode.
        unfold refine_memory,pointwise,refine_mem_loc_b in RMEMS;
          specialize RMEMS with pc; rewrite PC in RMEMS;
          destruct (get AM pc); [simpl|contradiction].
        move/eqP in RMEMS; subst; assumption.
      * split; [apply IN_c|].
        slowness admit.
    + by do 2 constructor; simpl.
  - (* Const *)
    undo1 NEXT rvec;
      destruct told as [| |]; try discriminate;
      undo1 def_rvec cid;
      undo1 NEXT regs';
      unfold Sym.can_execute,Sym.sfi_rvec in *; unoption; simpl in *.
    destruct tpc as [S cid'| |]; try discriminate;
      destruct ti as [|cid'' I W|]; try discriminate.
    move/eqP in RPC; subst Apc.
    evar (AR' : registers);
      exists (Some (Abs.State (pc+1)%w AR' AM AC)); split;
      subst AR'.
    + eapply AbsSlow.step_go; try reflexivity.
      rewrite /refine_compartments /refine_compartment_tag /= in RCOMP;
        move: RCOMP => [RCOMPS [RCTAGS RCOK]].
      specialize RCTAGS with pc; rewrite PC in RCTAGS.
      destruct RCTAGS as [[c [IN_c IN_SAME]] [OK_I OK_W]].
      eapply Abs.step_const; try reflexivity.
      * unfold Abs.decode.
        unfold refine_memory,pointwise,refine_mem_loc_b in RMEMS;
          specialize RMEMS with pc; rewrite PC in RMEMS;
          destruct (get AM pc); [simpl|contradiction].
        move/eqP in RMEMS; subst; eassumption.
      * split; [apply IN_c|].
        slowness admit.
      * unfold upd; rewrite /refine_registers /pointwise in RREGS;
          specialize RREGS with r.
        destruct (get AR r) eqn:GET;
          [reflexivity | rewrite OLD in RREGS; done].
    + do 2 constructor; simpl; try done.
      unfold upd; rewrite /refine_registers /pointwise in RREGS *; intros r'.
      destruct (r == r') eqn:EQ_r; move/eqP in EQ_r; [subst r'|].
      * erewrite get_set_eq, get_upd_eq by eauto using reg_axioms.
        by unfold refine_reg_b.
      * erewrite get_set_neq, get_upd_neq with (m' := regs')
          by eauto using reg_axioms.
        apply RREGS.
  - (* Mov *)
    undo1 NEXT rvec;
      destruct t1,told; try discriminate;
      undo1 def_rvec cid;
      undo1 NEXT regs';
      unfold Sym.can_execute,Sym.sfi_rvec in *; unoption; simpl in *.
    destruct tpc as [S cid'| |]; try discriminate;
      destruct ti as [|cid'' I W|]; try discriminate.
    move/eqP in RPC; subst Apc.
    rewrite /refine_registers /pointwise in RREGS.
    destruct (get AR r1) as [x1|] eqn:GET1;
      [| specialize RREGS with r1; rewrite R1W GET1 in RREGS; done].
    destruct (get AR r2) as [x2|] eqn:GET2;
      [| specialize RREGS with r2; rewrite OLD GET2 in RREGS; done].
    evar (AR' : registers);
      exists (Some (Abs.State (pc+1)%w AR' AM AC)); split;
      subst AR'.
    + rewrite /refine_compartments /refine_compartment_tag /= in RCOMP;
        move: RCOMP => [RCOMPS [RCTAGS RCOK]].
      specialize RCTAGS with pc; rewrite PC in RCTAGS.
      destruct RCTAGS as [[c [IN_c IN_SAME]] [OK_I OK_W]].
      eapply AbsSlow.step_go; try reflexivity.
      eapply Abs.step_mov; try reflexivity.
      * unfold Abs.decode.
        unfold refine_memory,pointwise,refine_mem_loc_b in RMEMS;
          specialize RMEMS with pc; rewrite PC in RMEMS;
          destruct (get AM pc); [simpl|contradiction].
        move/eqP in RMEMS; subst; eassumption.
      * split; [apply IN_c|].
        slowness admit.
      * eassumption.
      * unfold upd; rewrite GET2; reflexivity.
    + do 2 constructor; simpl; try done.
      unfold upd; rewrite /refine_registers /pointwise in RREGS *; intros r2'.
      destruct (r2 == r2') eqn:EQ_r2; move/eqP in EQ_r2; [subst r2'|].
      * erewrite get_set_eq, get_upd_eq by eauto using reg_axioms.
        by specialize RREGS with r1; rewrite GET1 R1W /refine_reg_b in RREGS *.
      * erewrite get_set_neq, get_upd_neq with (m' := regs')
          by eauto using reg_axioms.
        apply RREGS.
  - (* Binop *)
    undo1 NEXT rvec;
      destruct t1,t2,told; try discriminate;
      undo1 def_rvec cid;
      undo1 NEXT regs';
      unfold Sym.can_execute,Sym.sfi_rvec in *; unoption; simpl in *.
    destruct tpc as [S cid'| |]; try discriminate;
      destruct ti as [|cid'' I W|]; try discriminate.
    move/eqP in RPC; subst Apc.
    rewrite /refine_registers /pointwise in RREGS.
    destruct (get AR r1) as [x1|] eqn:GET1;
      [| specialize RREGS with r1; rewrite R1W GET1 in RREGS; done].
    destruct (get AR r2) as [x2|] eqn:GET2;
      [| specialize RREGS with r2; rewrite R2W GET2 in RREGS; done].
    destruct (get AR r3) as [x3|] eqn:GET3;
      [| specialize RREGS with r3; rewrite OLD GET3 in RREGS; done].
    evar (AR' : registers);
      exists (Some (Abs.State (pc+1)%w AR' AM AC)); split;
      subst AR'.
    + rewrite /refine_compartments /refine_compartment_tag /= in RCOMP;
        move: RCOMP => [RCOMPS [RCTAGS RCOK]].
      specialize RCTAGS with pc; rewrite PC in RCTAGS.
      destruct RCTAGS as [[c [IN_c IN_SAME]] [OK_I OK_W]].
      eapply AbsSlow.step_go; try reflexivity.
      eapply Abs.step_binop; try reflexivity.
      * unfold Abs.decode.
        unfold refine_memory,pointwise,refine_mem_loc_b in RMEMS;
          specialize RMEMS with pc; rewrite PC in RMEMS;
          destruct (get AM pc); [simpl|contradiction].
        move/eqP in RMEMS; subst; eassumption.
      * split; [apply IN_c|].
        slowness admit.
      * eassumption.
      * eassumption.
      * unfold upd; rewrite GET3; reflexivity.
    + do 2 constructor; simpl; try done.
      unfold upd; rewrite /refine_registers /pointwise in RREGS *; intros r3'.
      destruct (r3 == r3') eqn:EQ_r3; move/eqP in EQ_r3; [subst r3'|].
      * erewrite get_set_eq, get_upd_eq by eauto using reg_axioms.
        { unfold refine_reg_b. apply/eqP; f_equal.
          - by specialize RREGS with r1;
               rewrite GET1 R1W /refine_reg_b in RREGS *; apply/eqP.
          - by specialize RREGS with r2;
               rewrite GET2 R2W /refine_reg_b in RREGS *; apply/eqP. }
      * erewrite get_set_neq, get_upd_neq with (m' := regs')
          by eauto using reg_axioms.
        apply RREGS.
  - (* Load *)
    undo1 NEXT rvec;
      destruct t1,t2,told; try discriminate;
      undo1 def_rvec cid;
      undo1 NEXT regs';
      unfold Sym.can_execute,Sym.sfi_rvec in *; unoption; simpl in *.
    destruct tpc as [S cid'| |]; try discriminate;
      destruct ti as [|cid'' I'' W''|]; try discriminate.
    move/eqP in RPC; subst Apc.
    rewrite /refine_registers /refine_memory /pointwise  in RREGS RMEMS.
    destruct (get AR r1) as [x1|] eqn:GET1;
      [| specialize RREGS with r1; rewrite R1W GET1 in RREGS; done].
    destruct (get AR r2) as [xold|] eqn:GET2;
      [| specialize RREGS with r2; rewrite OLD GET2 in RREGS; done].
    assert (EQ1 : x1 = w1) by
      (by specialize RREGS with r1;
          rewrite R1W GET1 /refine_reg_b in RREGS; move/eqP in RREGS);
      subst x1.
    destruct (get AM w1) as [x2|] eqn:GETM1;
      [|specialize RMEMS with w1; rewrite MEM1 GETM1 in RMEMS; done].
    evar (AR' : registers);
      exists (Some (Abs.State (pc+1)%w AR' AM AC)); split;
      subst AR'.
    + rewrite /refine_compartments /refine_compartment_tag /= in RCOMP;
        move: RCOMP => [RCOMPS [RCTAGS RCOK]].
      specialize RCTAGS with pc; rewrite PC in RCTAGS.
      destruct RCTAGS as [[ac [IN_ac IN_SAME]] [OK_I OK_W]].
      eapply AbsSlow.step_go; try reflexivity.
      eapply Abs.step_load; try reflexivity.
      * unfold Abs.decode.
        unfold refine_memory,pointwise,refine_mem_loc_b in RMEMS;
          specialize RMEMS with pc; rewrite PC in RMEMS;
          destruct (get AM pc); [simpl|contradiction].
        move/eqP in RMEMS; subst; eassumption.
      * split; [apply IN_ac|].
        slowness admit.
      * eassumption.
      * eassumption.
      * unfold upd; rewrite GET2; reflexivity.
    + do 2 constructor; simpl; try done.
      unfold upd; rewrite /refine_registers /pointwise in RREGS *; intros r2'.
      destruct (r2 == r2') eqn:EQ_r2; move/eqP in EQ_r2; [subst r2'|].
      * erewrite get_set_eq, get_upd_eq by eauto using reg_axioms.
        by specialize RMEMS with w1;
           rewrite GETM1 MEM1 /refine_mem_loc_b /refine_reg_b in RMEMS *.
      * erewrite get_set_neq, get_upd_neq with (m' := regs')
          by eauto using reg_axioms.
        apply RREGS.
  - (* Store *)
    admit.
  - (* Jump *)
    admit.
  - (* Bnz *)
    undo1 NEXT rvec;
      destruct t1; try discriminate;
      undo1 def_rvec cid;
      unfold Sym.can_execute,Sym.sfi_rvec in *; unoption; simpl in *.
    destruct tpc as [S cid'| |]; try discriminate;
      destruct ti as [|cid'' I W|]; try discriminate.
    move/eqP in RPC; subst Apc.
    rewrite /refine_registers /pointwise in RREGS.
    destruct (get AR r) as [x|] eqn:GET;
      [| specialize RREGS with r; rewrite RW GET in RREGS; done].
    assert (EQ : x = w) by
      (by specialize RREGS with r;
          rewrite RW GET /refine_reg_b in RREGS; move/eqP in RREGS);
      subst x.
    evar (AR' : registers);
      exists (Some (Abs.State (pc + (if w == 0 then 1 else imm_to_word n))%w
                              AR' AM AC)); split;
      subst AR'.
    + eapply AbsSlow.step_go; try reflexivity.
      rewrite /refine_compartments /refine_compartment_tag /= in RCOMP;
        move: RCOMP => [RCOMPS [RCTAGS RCOK]].
      specialize RCTAGS with pc; rewrite PC in RCTAGS.
      destruct RCTAGS as [[c [IN_c IN_SAME]] [OK_I OK_W]].
      eapply Abs.step_bnz; try reflexivity.
      * unfold Abs.decode.
        unfold refine_memory,pointwise,refine_mem_loc_b in RMEMS;
          specialize RMEMS with pc; rewrite PC in RMEMS;
          destruct (get AM pc); [simpl|contradiction].
        move/eqP in RMEMS; subst; eassumption.
      * assumption.
      * split; [apply IN_c|].
        slowness admit.
    + by do 2 constructor; simpl.
  - (* Jal *)
    admit.
  - (* Syscall *)
    admit.
Qed.

End RefinementSA.