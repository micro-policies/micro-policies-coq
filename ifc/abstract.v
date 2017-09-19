From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype finfun.
From CoqUtils Require Import hseq ord fmap word.
From MicroPolicies Require Import lib.utils common.types ifc.labels ifc.common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Abstract.

Import DoNotation.

Variable L : labType.
Variable mt : machine_types.
Variable mops : machine_ops mt.
Context {sregs : syscall_regs mt}.
Context {addrs : ifc_addrs mt}.

Local Notation word := (mword mt).
Local Notation atom := (atom word L).

Record state := State {
  mem        : {fmap mword mt -> instr mt + atom};
  regs       : {fmap reg mt -> atom};
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

  (* Note that we often need to adjust the tag on the caller pc because it may be
     lower than the one on the current pc; for example, if we jump to the service
     via BNZ instead of JAL. *)
  else if pc == return_addr then
    if stk is cf :: stk' then
      do! retv <- regs syscall_ret;
      do! rs' <- updm (cf_regs cf) syscall_ret (vala retv)@(lpc ⊔ taga retv);
      Some (State mem rs' (cf_pc cf) stk', None)
    else None
  else if pc == call_addr then
    do! caller_pc <- regs ra;
    let caller_pc := (vala caller_pc)@(taga caller_pc ⊔ lpc) in
    do! called_pc <- regs syscall_arg1;
    Some (State mem regs
                (vala called_pc)@(taga called_pc ⊔ taga caller_pc)
                (CallFrame caller_pc regs :: stk), None)
  else if pc == output_addr then
    do! raddr <- regs ra;
    let r_pc  := taga raddr ⊔ lpc in
    let raddr := (vala raddr)@r_pc in
    do! out   <- regs syscall_arg1;
    let r_out := taga out in
    Some (State mem regs raddr stk,
          Some (vala out)@(lpc ⊔ r_out))
  else None.

Fixpoint trace n s :=
  if n is S n' then
    if step s is Some (s', oe) then
      seq_of_opt oe ++ trace n' s'
    else [::]
  else [::].

End Abstract.
