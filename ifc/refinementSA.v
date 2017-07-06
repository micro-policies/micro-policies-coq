From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype finfun.
From CoqUtils Require Import hseq ord fset partmap word.
From MicroPolicies Require Import
  lib.utils lib.partmap_utils common.types symbolic.symbolic symbolic.exec
  ifc.labels ifc.symbolic ifc.abstract.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Refinement.

Import DoNotation.

Variable L : labType.
Variable mt : machine_types.
Variable mops : machine_ops mt.
Variable r_arg : reg mt.

Local Notation word := (mword mt).
Local Notation d_atom := (atom word L).

Local Notation sstate := (@Symbolic.state mt (sym_ifc L)).
Local Notation sstep :=
  (@stepf _ _ _ (@ifc_syscalls L mt)).
Local Notation astate := (ifc.abstract.state L mt).
Local Notation astep := (@step L mt mops).

Implicit Types (sst : sstate) (ast : astate).

Local Open Scope label_scope.

Definition refine_m_atom (x : atom word (mem_tag L)) (y : instr mt + d_atom) :=
  match x, y with
  | wx@MemInstr, inl i => decode_instr wx = Some i
  | wx@(MemData rl), inr a => wx@rl = a
  | _, _ => False
  end.

Inductive refine_state sst ast : Prop :=
| RefineState of pointwise refine_m_atom
                           (Symbolic.mem sst)
                           (ifc.abstract.mem ast)
              &  Symbolic.regs sst = ifc.abstract.regs ast
              &  vala (Symbolic.pc sst) = vala (ifc.abstract.pc ast)
              &  taga (Symbolic.pc sst) = taga (ifc.abstract.pc ast).

Hint Unfold Symbolic.next_state_pc.
Hint Unfold Symbolic.next_state_reg.
Hint Unfold Symbolic.next_state_reg_and_pc.
Hint Unfold Symbolic.next_state.

Lemma refinement sst sst' ast :
  refine_state sst ast ->
  sstep sst = Some sst' ->
  match astep ast with
  | Some ast' => refine_state sst' ast'
  | None => False
  end.
Proof.
rewrite (lock sstep) (lock astep).
case: sst=> /= sm sr [spc slpc] t.
case: ast=> /= am ar [apc alpc].
case=> /= ref_m ref_r.
move: sr ref_r=> regs <- {ar}.
move: spc slpc => pc lpc <- <- {apc alpc}.
rewrite -lock /=.
move: (ref_m pc).
case: (sm pc) => [[si [|sti]]|]; case aget_pc: (am pc) => [[ai|a]|] //=.
- (* Instruction *)
  case: decode_instr => [i|] ref_i //=.
  case: i ref_i aget_pc => //=; repeat autounfold=> /=.
  + (* Nop *)
    move=> [<-] {ai} aget_pc [<-] {sst'}.
    by rewrite -lock /= aget_pc /=; split.
  + (* Const *)
    move=> i r [<-] {ai} aget_pc.
    case: (regs r)=> //= - [_ _].
    case upd_r: updm => [regs'|] //= [<-] {sst'}.
    by rewrite -lock /= aget_pc /= upd_r /=; split.
  + (* Mov *)
    move=> r1 r2 [<-] {ai} aget_pc.
    case get_r1: (regs r1)=> [[w1 rl1]|] //=.
    case: (regs r2)=> //= - [_ _].
    case upd_r2: updm => [regs'|] //= [<-] {sst'}.
    by rewrite -lock /= aget_pc get_r1 /= upd_r2 /=; split.
  + (* Binop *)
    move=> b r1 r2 r3 [<-] {ai} aget_pc.
    case get_r1: (regs r1)=> [[w1 rl1]|] //=.
    case get_r2: (regs r2)=> [[w2 rl2]|] //=.
    case: (regs r3)=> [[_ _]|] //=.
    case upd_r3: updm=> [regs'|] //= [<-] {sst'}.
    by rewrite -lock /= aget_pc get_r1 /= get_r2 /= upd_r3 /=; split.
  + (* Load *)
    move=> r1 r2 [<-] {ai} aget_pc.
    case get_r1: (regs r1)=> [[w1 rl1]|] //=.
    move: (ref_m w1).
    case sget_w1: (sm w1) => [[w1' [|rl1']]|] //=;
    case: (regs r2)=> [[_ _]|] //=.
    case aget_w1: (am w1) => [[?|a]|] //= e.
    move: e aget_w1=> <- {a} aget_w1.
    case upd_r2: updm => [regs'|] //= [<-] {sst'}.
    by rewrite -lock /= aget_pc get_r1 /= aget_w1 /= upd_r2 /=; split.
  + (* Store *)
    move=> r1 r2 [<-] {ai} aget_pc.
    case get_r1: (regs r1)=> [[w1 rl1]|] //=.
    case sget_w1: (sm w1) => [[wold [|rlold]]|] //=;
    case get_r2: (regs r2)=> [[w2 rl2]|] //=.
    case: ifP => // check /=.
    case supd_w1: updm => [sm'|] //= [<-] {sst'}.
    have [am' aupd_w1]:
      exists am', updm am w1 (inr w2@(rl1 ⊔ rl2 ⊔ lpc)) = Some am'.
      exists (setm am w1 (inr w2@(rl1 ⊔ rl2 ⊔ lpc))).
      move: (ref_m w1) supd_w1; rewrite /updm.
      by case: (sm w1) (am w1) => //= sa [aa|] //= {sa aa} _ [<-].
    have ref_a: refine_m_atom w2@(MemData (rl1 ⊔ rl2 ⊔ lpc))
                              (inr w2@(rl1 ⊔ rl2 ⊔ lpc)) by [].
    have ref_m' := refine_upd_pointwise2 ref_m ref_a supd_w1 aupd_w1.
    move: (ref_m w1); rewrite sget_w1 /=.
    case aget_w1: (am w1) => [[?|a]|] //= e.
    move: e aget_w1 => <- {a} aget_w1.
    rewrite -lock /= aget_pc get_r1 /= get_r2 /= aget_w1 /= check aupd_w1 /=.
    by split.
  + (* Jump *)
    move=> r [<-] {ai} aget_pc.
    case get_r: (regs r)=> [[w1 rl1]|] //= [<-] {sst'}.
    by rewrite -lock /= aget_pc get_r /=; split.
  + (* Bnz *)
    move=> r i [<-] {ai} aget_pc.
    case get_r: (regs r)=> [[w1 rl1]|] //= [<-] {sst'}.
    by rewrite -lock /= aget_pc get_r /=; split.
  (* Jal *)
  move=> r [<-] {ai} aget_pc.
  case get_r: (regs r) => [[w1 rl1]|] //=.
  case: (regs ra)=> [[_ _]|] //=.
  case upd_ra: updm => [regs'|] //= [<-] {sst'}.
  by rewrite -lock /= aget_pc /= get_r /= upd_ra /=; split.
- (* Fetch data in memory instead of instruction; contradiction *)
  move=> e; move: e aget_pc => <- aget_pc {a}.
  by case: decode_instr => [[]|] /= *;
  repeat autounfold in *; simpl in *; match_inv.
(* System services; none for now. *)
Qed.

End Refinement.
