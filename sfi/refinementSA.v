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
  {sregisters   : Type}
  {sreg_class   : partial_map sregisters (reg t) (atom (word t) (@Sym.stag t))}.

Notation word    := (word t).
Notation stag    := (@Sym.stag t).
Notation sym_sfi := (@Sym.sym_sfi t ops smemory smem_class sregisters sreg_class).

Notation astate  := (@Abs.state t ap).
Notation astate' := (@AbsSlow.state t ap).
Notation sstate  := (@Symbolic.state t sym_sfi).

Notation astep  := (Abs.step []).
Notation astep' := (AbsSlow.step []).
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

Definition refine_compartment_set_b (C   : list (Abs.compartment t))
                                    (sst : sstate)
                                    (p   : word) : bool :=
  match get (Symbolic.mem sst) p with
    | Some (_ @ (Sym.DATA _ I W)) =>
      is_some (assoc_list_lookup (Sym.set_ids (Symbolic.internal sst))
                                 (eq_op I)) &&
      is_some (assoc_list_lookup (Sym.set_ids (Symbolic.internal sst))
                                 (eq_op W))
    | Some (_ @ _) =>
      false
    | None =>
      true
  end.

Definition refine_compartments (C : list (Abs.compartment t))
                               (sst : sstate) : Prop :=
  forallb (refine_compartment_b ^~ (Symbolic.mem sst)) C /\
  (forall p, refine_compartment_set_b C sst p) /\
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
    destruct RCOMPS as [RCOMPS [RSETS ROK]];
  unfold Sym.good_state, Abs.good_state in *; simpl in *;
    move: GOOD => /andP [ICO GOOD].
  repeat split.
  - intros p; unfold Sym.good_memory_tag.
    unfold refine_memory, pointwise in RMEMS; specialize RMEMS with p.
    specialize RSETS with p; unfold refine_compartment_set_b in RSETS;
      simpl in RSETS.
    destruct (get SM p) as [[Sx SL]|] eqn:SGET; rewrite SGET in RSETS *;
      [|trivial].
    destruct (get AM p) as [Ax|] eqn:AGET; [simpl in RMEMS | elim RMEMS].
    by destruct SL as [|c I W|].
  - intros r; unfold Sym.good_register_tag.
    unfold refine_registers, pointwise in RREGS; specialize RREGS with r.
    destruct (get SR r) as [[Sx SL]|] eqn:SGET; rewrite SGET; [|trivial].
    destruct (get AR r) as [Ax|] eqn:AGET; [|elim RREGS].
    unfold refine_reg_b in RREGS.
    by destruct SL.
  - by destruct Lpc.
  - exact ROK.
Qed.

Theorem backward_simulation : forall ast sst sst',
  refine_astate' ast sst ->
  sstep sst sst' ->
  exists ast',
    astep' ast ast' /\
    refine_astate' ast' sst'.
Proof.
Abort.

End RefinementSA.