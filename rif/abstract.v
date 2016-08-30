From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq fintype finfun.
From CoqUtils Require Import hseq ord fset partmap word.
From MicroPolicies Require Import lib.utils common.types rif.common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Abstract.

Import DoNotation.

Variable Σ : finType.
Variable mt : machine_types.
Variable mops : machine_ops mt.

Local Notation rifAutomaton := (rifAutomaton Σ).
Local Notation rifLabel := (rifLabel Σ).
Local Notation event := (event Σ mt).
Local Notation atom := (atom (mword mt) rifLabel).

Record state := State {
  imem : {partmap mword mt -> instr mt};
  dmem : {partmap mword mt -> atom};
  regs : {partmap reg mt -> atom};
  pc   : atom
}.

Local Open Scope word_scope.
Local Open Scope rif_scope.

Implicit Type s : state.

Definition step s :=
  let: State imem dmem regs pc@lpc := s in
  do! i <- imem pc;
  match i with
  | Nop => Some (State imem dmem regs (pc + 1)@lpc)
  | Const k r =>
    do! regs <- updm regs r (swcast k)@⊥ₗ;
    Some (State imem dmem regs (pc + 1)@lpc)
  | Mov r1 r2 =>
    do! v <- regs r1;
    do! regs <- updm regs r2 v;
    Some (State imem dmem regs (pc + 1)@lpc)
  | Binop o r1 r2 r3 =>
    do! v1 <- regs r1;
    do! v2 <- regs r2;
    do! regs <- updm regs r3 (binop_denote o (vala v1) (vala v2))@(taga v1 ⊔ₗ taga v2);
    Some (State imem dmem regs (pc + 1)@lpc)
  | Load r1 r2 =>
    do! v1 <- regs r1;
    do! v2 <- dmem (vala v1);
    do! regs <- updm regs r2 (vala v2)@(taga v1 ⊔ₗ taga v2);
    Some (State imem dmem regs (pc + 1)@lpc)
  | Store r1 r2 =>
    do! v1 <- regs r1;
    do! v2 <- regs r2;
    do! vold <- dmem (vala v1);
    if taga v1 ⊔ₗ lpc ⊑ₗ taga vold then
      do! dmem <- updm dmem (vala v1)
                            (vala v2)@(taga v1 ⊔ₗ taga v2 ⊔ₗ lpc);
      Some (State imem dmem regs (pc + 1)@lpc)
    else None
  | Jump r =>
    do! v <- regs r;
    Some (State imem dmem regs (vala v)@(taga v ⊔ₗ lpc))
  | Bnz r x =>
    do! v <- regs r;
    let pc' := pc + if vala v == 0 then 1
                    else swcast x in
    Some (State imem dmem regs pc'@(taga v ⊔ₗ lpc))
  | Jal r =>
    do! v <- regs r;
    do! regs <- updm regs ra (pc + 1)@(taga v ⊔ₗ lpc);
    Some (State imem dmem regs (vala v)@(taga v ⊔ₗ lpc))
  | _ => None
  end.

End Abstract.
