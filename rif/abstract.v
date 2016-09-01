From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype finfun.
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
Variable output_addr : mword mt.
Variable reclassify_addr : mword mt.

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
| AJal of reg mt & option Σ
| AHalt.

Definition ainstr_eq i1 i2 :=
  match i1, i2 with
  | ANop, ANop => true
  | AConst i1 r1, AConst i2 r2 => (i1 == i2) && (r1 == r2)
  | AMov r11 r12, AMov r21 r22 => (r11 == r21) && (r12 == r22)
  | ABinop b1 r11 r12 r13, ABinop b2 r21 r22 r23 =>
    [&& b1 == b2, r11 == r21, r12 == r22 & r13 == r23]
  | ALoad r11 r12, ALoad r21 r22 => (r11 == r21) && (r12 == r22)
  | AStore r11 r12, AStore r21 r22 => (r11 == r21) && (r12 == r22)
  | AJump r1, AJump r2 => r1 == r2
  | ABnz r1 i1, ABnz r2 i2 => (r1 == r2) && (i1 == i2)
  | AJal r1 oF1, AJal r2 oF2 => (r1 == r2) && (oF1 == oF2)
  | AHalt, AHalt => true
  | _, _ => false
  end.

Lemma ainstr_eqP : Equality.axiom ainstr_eq.
Proof.
move=> i1 i2; case: i1=> *; case: i2=> * /=;
by [
  constructor; congruence |
  by apply/(iffP idP)=> [/eqP ->|[->]] |
  by apply/(iffP and4P)=> [[/eqP -> /eqP -> /eqP -> /eqP ->]|[-> -> -> ->]] |
  by apply/(iffP andP)=> [[/eqP -> /eqP ->]|[-> ->]] ].
Qed.

Definition ainstr_eqMixin := EqMixin ainstr_eqP.
Canonical ainstr_eqType := Eval hnf in EqType ainstr ainstr_eqMixin.

Record state := State {
  mem     : {partmap mword mt -> ainstr + atom};
  regs    : {partmap reg mt -> atom};
  pc      : atom;
  reclass : option Σ
}.

Local Open Scope word_scope.
Local Open Scope rif_scope.

Implicit Type s : state.

Definition step s : option (state * option event) :=
  let: State mem regs pc@lpc reclass := s in
  if mem pc is Some i then
    if i is inl i then
      match i with
      | ANop => Some (State mem regs (pc + 1)@lpc None, None)
      | AConst k r =>
        do! regs <- updm regs r (swcast k)@⊥ₗ;
        Some (State mem regs (pc + 1)@lpc None, None)
      | AMov r1 r2 =>
        do! v <- regs r1;
        do! regs <- updm regs r2 v;
        Some (State mem regs (pc + 1)@lpc None, None)
      | ABinop o r1 r2 r3 =>
        do! v1 <- regs r1;
        do! v2 <- regs r2;
        do! regs <- updm regs r3 (binop_denote o (vala v1) (vala v2))@(taga v1 ⊔ₗ taga v2);
        Some (State mem regs (pc + 1)@lpc None, None)
      | ALoad r1 r2 =>
        do! v1 <- regs r1;
        do! v2 <- mem (vala v1);
        if v2 is inr v2 then
          do! regs <- updm regs r2 (vala v2)@(taga v1 ⊔ₗ taga v2);
          Some (State mem regs (pc + 1)@lpc None, None)
        else None
      | AStore r1 r2 =>
        do! v1 <- regs r1;
        do! v2 <- regs r2;
        do! vold <- mem (vala v1);
        if vold is inr vold then
          if taga v1 ⊔ₗ lpc ⊑ₗ taga vold then
            do! mem <- updm mem (vala v1)
                                (inr (vala v2)@(taga v1 ⊔ₗ taga v2 ⊔ₗ lpc));
            Some (State mem regs (pc + 1)@lpc None, None)
          else None
        else None
      | AJump r =>
        do! v <- regs r;
        Some (State mem regs (vala v)@(taga v ⊔ₗ lpc) None, None)
      | ABnz r x =>
        do! v <- regs r;
        let pc' := pc + if vala v == 0 then 1
                        else swcast x in
        Some (State mem regs pc'@(taga v ⊔ₗ lpc) None, None)
      | AJal r oF =>
        do! v <- regs r;
        do! regs <- updm regs ra (pc + 1)@(taga v ⊔ₗ lpc);
        Some (State mem regs (vala v)@(taga v ⊔ₗ lpc) oF, None)
      | AHalt => None
      end
    else None
  else if pc == output_addr then
    do! raddr <- regs ra;
    do! out   <- regs r_arg;
    let r_pc  := rif_readers _ (rif_state (taga raddr)) in
    let r_out := rif_readers _ (rif_state (taga out)) in
    Some (State mem regs raddr None,
          Some (Output _ (vala out) (r_pc ⊔ᵣ r_out)))
  else if pc == reclassify_addr then
    do! raddr <- regs ra;
    do! arg   <- regs r_arg;
    if reclass is Some F then
      do! regs  <- updm regs r_arg (vala arg)@(rl_trans (taga arg) F);
      Some (State mem regs raddr None,
            Some (Reclassify _ (taga arg) F))
    else None
  else None.

Fixpoint stepn n s :=
  if n is S n' then
    if step s is Some (s', oe) then
      if stepn n' s' is Some (s'', t) then
        Some (s'', t ++ seq_of_opt oe)
      else None
    else None
  else Some (s, [::]).

End Abstract.

Arguments ANop {Σ mt}.
Arguments AConst {Σ mt} _ _.
Arguments AMov {Σ mt} _ _.
Arguments ABinop {Σ mt} _ _ _ _.
Arguments ALoad {Σ mt} _ _.
Arguments AStore {Σ mt} _ _.
Arguments AJump {Σ mt} _.
Arguments ABnz {Σ mt} _ _.
Arguments AJal {Σ mt} _ _.
Arguments AHalt {Σ mt}.
