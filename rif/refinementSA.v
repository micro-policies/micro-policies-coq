From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq fintype finfun.
From CoqUtils Require Import hseq ord fset partmap word.
From MicroPolicies Require Import
  lib.utils lib.partmap_utils common.types symbolic.symbolic symbolic.exec
  rif.common rif.symbolic rif.abstract.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Abstract.

Import DoNotation.

Variable Σ : finType.
Variable mt : machine_types.
Variable mops : machine_ops mt.
Variable r_arg : reg mt.

Local Notation rifAutomaton := (rifAutomaton Σ).
Local Notation rifLabel := (rifLabel Σ).
Local Notation event := (event Σ mt).
Local Notation word := (mword mt).
Local Notation d_atom := (atom word rifLabel).

Variable output_addr : word.
Variable reclassify_addr : word.

Local Notation sstate := (@Symbolic.state mt (sym_rif Σ mt)).
Local Notation sstep :=
  (@stepf _ _ _ (@rif_syscalls Σ mt mops output_addr reclassify_addr r_arg)).
Local Notation astate := (rif.abstract.state Σ mt).
Local Notation astep := (@step Σ mt mops r_arg output_addr reclassify_addr).
Local Notation ainstr := (ainstr Σ mt).

Implicit Types (sst : sstate) (ast : astate).

Local Open Scope rif_scope.

Definition abs_instr (i : word) (oF : option Σ) : option ainstr :=
  if decode_instr i is Some i then
    match i with
    | Nop => Some ANop
    | Const i r => Some (AConst i r)
    | Mov r1 r2 => Some (AMov r1 r2)
    | Binop o r1 r2 r3 => Some (ABinop o r1 r2 r3)
    | Load r1 r2 => Some (ALoad r1 r2)
    | Store r1 r2 => Some (AStore r1 r2)
    | Jump r => Some (AJump r)
    | Bnz r i => Some (ABnz r i)
    | Jal r => Some (AJal r oF)
    | Halt => Some AHalt
    | JumpEpc | AddRule  | GetTag _ _  | PutTag _ _ _ => None
    end
  else None.

Definition refine_m_atom (x : atom word (mem_tag Σ)) (y : ainstr + d_atom) :=
  match x, y with
  | wx@(MemInstr oF), inl i => abs_instr wx oF = Some i
  | wx@(MemData rl), inr a => wx@rl = a
  | _, _ => False
  end.

Inductive refine_state sst ast : Prop :=
| RefineState of pointwise refine_m_atom (Symbolic.mem sst) (rif.abstract.mem ast)
              &  Symbolic.regs sst = rif.abstract.regs ast
              &  vala (Symbolic.pc sst) = vala (rif.abstract.pc ast)
              &  (taga (Symbolic.pc sst)).1 = taga (rif.abstract.pc ast)
              &  (taga (Symbolic.pc sst)).2 = rif.abstract.reclass ast.

Hint Unfold Symbolic.next_state_pc.
Hint Unfold Symbolic.next_state_reg.
Hint Unfold Symbolic.next_state_reg_and_pc.
Hint Unfold Symbolic.next_state.

Lemma refinement sst sst' ast :
  refine_state sst ast ->
  sstep sst = Some sst' ->
  match astep ast with
  | Some (ast', oe) =>
    refine_state sst' ast'
    /\ Symbolic.internal sst' =
       Symbolic.internal sst ++ oapp (cons ^~ [::]) [::] oe
  | None => False
  end.
Proof.
rewrite (lock sstep) (lock astep).
case: sst=> /= sm sr [spc [slpc src]] t.
case: ast=> /= am ar [apc alpc] arc.
case=> /= ref_m ref_r.
move: sr ref_r=> regs <- {ar}.
move: spc slpc src => pc lpc rc <- <- <- {apc alpc arc}.
rewrite -lock /=.
move: (ref_m pc).
case: (sm pc) => [[si [oF|sti]]|]; case aget_pc: (am pc) => [[ai|?]|] //=.
- (* Instruction *)
  rewrite /abs_instr.
  case: decode_instr => [i|] ref_i //=.
  case: i ref_i aget_pc => //=; repeat autounfold=> /=.
  + (* Nop *)
    move=> [<-] {ai} aget_pc [<-] {sst'}.
    by rewrite -lock /= aget_pc /= cats0; split.
  + (* Const *)
    move=> i r [<-] {ai} aget_pc.
    case: (regs r)=> //= - [_ _].
    case upd_r: updm => [regs'|] //= [<-] {sst'}.
    by rewrite -lock /= aget_pc /= upd_r /= cats0; split.
  + (* Mov *)
    move=> r1 r2 [<-] {ai} aget_pc.
    case get_r1: (regs r1)=> [[w1 rl1]|] //=.
    case: (regs r2)=> //= - [_ _].
    case upd_r2: updm => [regs'|] //= [<-] {sst'}.
    by rewrite -lock /= aget_pc get_r1 /= upd_r2 /= cats0; split.
  + (* Binop *)
    move=> b r1 r2 r3 [<-] {ai} aget_pc.
    case get_r1: (regs r1)=> [[w1 rl1]|] //=.
    case get_r2: (regs r2)=> [[w2 rl2]|] //=.
    case: (regs r3)=> [[_ _]|] //=.
    case upd_r3: updm=> [regs'|] //= [<-] {sst'}.
    by rewrite -lock /= aget_pc get_r1 /= get_r2 /= upd_r3 /= cats0; split.
  + (* Load *)
    move=> r1 r2 [<-] {ai} aget_pc.
    case get_r1: (regs r1)=> [[w1 rl1]|] //=.
    move: (ref_m w1).
    case sget_w1: (sm w1) => [[w1' [oF'|rl1']]|] //=;
    case: (regs r2)=> [[_ _]|] //=.
    case aget_w1: (am w1) => [[?|a]|] //= e.
    move: e aget_w1=> <- {a} aget_w1.
    case upd_r2: updm => [regs'|] //= [<-] {sst'}.
    by rewrite -lock /= aget_pc get_r1 /= aget_w1 /= upd_r2 /= cats0; split.
  + (* Store *)
    move=> r1 r2 [<-] {ai} aget_pc.
    case get_r1: (regs r1)=> [[w1 rl1]|] //=.
    case sget_w1: (sm w1) => [[wold [oF'|rlold]]|] //=;
    case get_r2: (regs r2)=> [[w2 rl2]|] //=.
    case: ifP => // check /=.
    case supd_w1: updm => [sm'|] //= [<-] {sst'}.
    have [am' aupd_w1]:
      exists am', updm am w1 (inr w2@(rl1 ⊔ₗ rl2 ⊔ₗ lpc)) = Some am'.
      exists (setm am w1 (inr w2@(rl1 ⊔ₗ rl2 ⊔ₗ lpc))).
      move: (ref_m w1) supd_w1; rewrite /updm.
      by case: (sm w1) (am w1) => //= sa [aa|] //= {sa aa} _ [<-].
    have ref_a: refine_m_atom w2@(MemData (rl1 ⊔ₗ rl2 ⊔ₗ lpc))
                              (inr w2@(rl1 ⊔ₗ rl2 ⊔ₗ lpc)) by [].
    have ref_m' := refine_upd_pointwise2 ref_m ref_a supd_w1 aupd_w1.
    move: (ref_m w1); rewrite sget_w1 /=.
    case aget_w1: (am w1) => [[?|a]|] //= e.
    move: e aget_w1 => <- {a} aget_w1.
    rewrite -lock /= aget_pc get_r1 /= get_r2 /= aget_w1 /= check aupd_w1 /=.
    by rewrite cats0; split.
  + (* Jump *)
    move=> r [<-] {ai} aget_pc.
    case get_r: (regs r)=> [[w1 rl1]|] //= [<-] {sst'}.
    by rewrite -lock /= aget_pc get_r /= cats0; split.
  + (* Bnz *)
    move=> r i [<-] {ai} aget_pc.
    case get_r: (regs r)=> [[w1 rl1]|] //= [<-] {sst'}.
    by rewrite -lock /= aget_pc get_r /= cats0; split.
  (* Jal *)
  move=> r [<-] {ai} aget_pc.
  case get_r: (regs r) => [[w1 rl1]|] //=.
  case: (regs ra)=> [[_ _]|] //=.
  case upd_ra: updm => [regs'|] //= [<-] {sst'}.
  by rewrite -lock /= aget_pc /= get_r /= upd_ra /= cats0; split.
- (* Fetch data in memory instead of instruction; contradiction *)
  admit.
(* System service *)
move=> _ /=.
admit.
Admitted.

End Abstract.
