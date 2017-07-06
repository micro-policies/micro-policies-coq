From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype finfun.
From CoqUtils Require Import hseq ord partmap word.
From MicroPolicies Require Import lib.utils common.types ifc.labels ifc.common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Abstract.

Import DoNotation.

Variable L : labType.
Variable mt : machine_types.
Variable mops : machine_ops mt.
Variable r_arg : reg mt.
Variable output_addr : mword mt.

Local Notation word := (mword mt).
Local Notation atom := (atom word L).

Record state := State {
  mem        : {partmap mword mt -> instr mt + atom};
  regs       : {partmap reg mt -> atom};
  pc         : atom;
  call_stack : seq (call_frame mt L)
}.

Local Open Scope word_scope.
Local Open Scope label_scope.

Implicit Type s : state.

Definition step s : option (state * option atom):=
  let: State mem regs pc@lpc stk := s in
  if mem pc is Some i then
    if i is inl i then
      match i with
      | Nop => Some (State mem regs (pc + 1)@lpc stk, None)
      | Const k r =>
        do! regs <- updm regs r (swcast k)@⊥;
        Some (State mem regs (pc + 1)@lpc stk, None)
      | Mov r1 r2 =>
        do! v <- regs r1;
        do! regs <- updm regs r2 v;
        Some (State mem regs (pc + 1)@lpc stk, None)
      | Binop o r1 r2 r3 =>
        do! v1 <- regs r1;
        do! v2 <- regs r2;
        do! regs <- updm regs r3 (binop_denote o (vala v1) (vala v2))@(taga v1 ⊔ taga v2);
        Some (State mem regs (pc + 1)@lpc stk, None)
      | Load r1 r2 =>
        do! v1 <- regs r1;
        do! v2 <- mem (vala v1);
        if v2 is inr v2 then
          do! regs <- updm regs r2 (vala v2)@(taga v1 ⊔ taga v2);
          Some (State mem regs (pc + 1)@lpc stk, None)
        else None
      | Store r1 r2 =>
        do! v1 <- regs r1;
        do! v2 <- regs r2;
        do! vold <- mem (vala v1);
        if vold is inr vold then
          if taga v1 ⊔ lpc ⊑ taga vold then
            do! mem <- updm mem (vala v1)
                                (inr (vala v2)@(taga v1 ⊔ taga v2 ⊔ lpc));
            Some (State mem regs (pc + 1)@lpc stk, None)
          else None
        else None
      | Jump r =>
        do! v <- regs r;
        Some (State mem regs (vala v)@(taga v ⊔ lpc) stk, None)
      | Bnz r x =>
        do! v <- regs r;
        let pc' := pc + if vala v == 0 then 1
                        else swcast x in
        Some (State mem regs pc'@(taga v ⊔ lpc) stk, None)
      | Jal r =>
        do! v <- regs r;
        do! regs <- updm regs ra (pc + 1)@(taga v ⊔ lpc);
        Some (State mem regs (vala v)@(taga v ⊔ lpc) stk, None)
      | JumpEpc => None
      | AddRule => None
      | GetTag _ _ => None
      | PutTag _ _ _ => None
      | Halt => None
      end
    else None
  else if pc == output_addr then
    do! raddr <- regs ra;
    do! out   <- regs r_arg;
    let r_pc  := taga raddr in
    let r_out := taga out in
    Some (State mem regs raddr stk,
          Some (vala out)@(r_pc ⊔ r_out))
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
