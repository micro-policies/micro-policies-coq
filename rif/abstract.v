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
Variable r_arg : reg mt.

Local Notation rifAutomaton := (rifAutomaton Σ).
Local Notation rifLabel := (rifLabel Σ).
Local Notation event := (event Σ mt).
Local Notation atom := (atom (mword mt) rifLabel).

Inductive ainstr : Type :=
| ANop
| AConst of imm mt & reg mt
| AMov of reg mt & reg mt
| ABinop of binop & reg mt & reg mt & reg mt
| ALoad of reg mt & reg mt
| AStore of reg mt & reg mt
| AJump of reg mt
| ABnz of reg mt & imm mt
| AJal of reg mt & Σ
| AHalt
| AOutput
| AReclassify.

Record state := State {
  imem    : {partmap mword mt -> ainstr};
  dmem    : {partmap mword mt -> atom};
  regs    : {partmap reg mt -> atom};
  pc      : atom;
  reclass : option Σ
}.

Local Open Scope word_scope.
Local Open Scope rif_scope.

Implicit Type s : state.

Definition step s : option (state * option event) :=
  let: State imem dmem regs pc@lpc reclass := s in
  do! i <- imem pc;
  match i with
  | ANop => Some (State imem dmem regs (pc + 1)@lpc None, None)
  | AConst k r =>
    do! regs <- updm regs r (swcast k)@⊥ₗ;
    Some (State imem dmem regs (pc + 1)@lpc None, None)
  | AMov r1 r2 =>
    do! v <- regs r1;
    do! regs <- updm regs r2 v;
    Some (State imem dmem regs (pc + 1)@lpc None, None)
  | ABinop o r1 r2 r3 =>
    do! v1 <- regs r1;
    do! v2 <- regs r2;
    do! regs <- updm regs r3 (binop_denote o (vala v1) (vala v2))@(taga v1 ⊔ₗ taga v2);
    Some (State imem dmem regs (pc + 1)@lpc None, None)
  | ALoad r1 r2 =>
    do! v1 <- regs r1;
    do! v2 <- dmem (vala v1);
    do! regs <- updm regs r2 (vala v2)@(taga v1 ⊔ₗ taga v2);
    Some (State imem dmem regs (pc + 1)@lpc None, None)
  | AStore r1 r2 =>
    do! v1 <- regs r1;
    do! v2 <- regs r2;
    do! vold <- dmem (vala v1);
    if taga v1 ⊔ₗ lpc ⊑ₗ taga vold then
      do! dmem <- updm dmem (vala v1)
                            (vala v2)@(taga v1 ⊔ₗ taga v2 ⊔ₗ lpc);
      Some (State imem dmem regs (pc + 1)@lpc None, None)
    else None
  | AJump r =>
    do! v <- regs r;
    Some (State imem dmem regs (vala v)@(taga v ⊔ₗ lpc) None, None)
  | ABnz r x =>
    do! v <- regs r;
    let pc' := pc + if vala v == 0 then 1
                    else swcast x in
    Some (State imem dmem regs pc'@(taga v ⊔ₗ lpc) None, None)
  | AJal r F =>
    do! v <- regs r;
    do! regs <- updm regs ra (pc + 1)@(taga v ⊔ₗ lpc);
    Some (State imem dmem regs (vala v)@(taga v ⊔ₗ lpc) (Some F), None)
  | AHalt => None
  | AOutput =>
    do! raddr <- regs ra;
    do! out   <- regs r_arg;
    let r_pc  := rif_readers _ (rif_state (taga raddr)) in
    let r_out := rif_readers _ (rif_state (taga out)) in
    Some (State imem dmem regs raddr None,
          Some (Output _ (vala out) (r_pc ⊔ᵣ r_out)))
  | AReclassify =>
    do! raddr <- regs ra;
    do! arg   <- regs r_arg;
    if reclass is Some F then
      do! regs  <- updm regs r_arg (vala arg)@(rl_trans (taga arg) F);
      Some (State imem dmem regs raddr None,
            Some (Reclassify _ (taga arg) F))
    else None
  end.

End Abstract.
