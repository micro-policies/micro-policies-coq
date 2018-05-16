(** Executable semantics for abstract memory-safety machine *)

From mathcomp Require Import
  ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype ssrint.
From extructures Require Import ord fset fmap fperm.
From CoqUtils Require Import word nominal.
Require Import lib.utils.
Require Import common.types memory_safety.classes memory_safety.abstract.

Import DoNotation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module AbstractE.

Section AbstractE.

Local Open Scope fset_scope.

Import Abstract.

Variable mt : machine_types.
Variable ops : machine_ops mt.
Variable sr : syscall_regs mt.
Variable addrs : memory_syscall_addrs mt.

Local Notation state := (state mt).
Local Notation pointer := [eqType of pointer mt].
Local Notation value := (value mt).
Open Scope word_scope.
Local Notation "x .+1" := (fst x, snd x + 1).

Implicit Type m : memory mt.
Implicit Type rs : registers mt.
Implicit Type s : state.
Implicit Type b : name.
Implicit Type p : pointer.
Implicit Type bs : {fset name}.
Implicit Type v : value.
Implicit Type pm : {fperm name}.

Definition step s : option state :=
  let: State m rs pc := s in
  match pc with
  | VPtr pc =>
    do! i <- getv m pc;
    if i is VData i then
      do! i <- decode_instr i;
      match i with
      | Nop => Some (State m rs (VPtr pc.+1))
      | Const n r =>
        do! rs' <- updm rs r (VData (swcast n));
        Some (State m rs' (VPtr pc.+1))
      | Mov r1 r2 =>
        do! v <- rs r1;
        do! rs' <- updm rs r2 v;
        Some (State m rs' (VPtr pc.+1))
      | Binop f r1 r2 r3 =>
        do! v1 <- rs r1;
        do! v2 <- rs r2;
        do! v3 <- lift_binop f v1 v2;
        do! rs' <- updm rs r3 v3;
        Some (State m rs' (VPtr pc.+1))
      | Load r1 r2 =>
        do! v1 <- rs r1;
        if v1 is VPtr p1 then
          do! v2 <- getv m p1;
          do! rs' <- updm rs r2 v2;
          Some (State m rs' (VPtr pc.+1))
        else None
      | Store r1 r2 =>
        do! v1 <- rs r1;
        if v1 is VPtr p1 then
          do! v2 <- rs r2;
          do! m' <- updv m p1 v2;
          Some (State m' rs (VPtr pc.+1))
        else None
      | Jump r =>
        do! v <- rs r;
        if v is VPtr p then
          Some (State m rs (VPtr p))
        else None
      | Bnz r n =>
        do! v <- rs r;
        if v is VData w then
          let off_pc' := pc.2 + (if w == 0 then 1 else swcast n) in
          Some (State m rs (VPtr (pc.1, off_pc')))
        else None
      | Jal r =>
        do! v <- rs r;
        do! rs' <- updm rs ra (VPtr pc.+1);
        Some (State m rs' v)
      | _ => None
      end
    else None
  | VData pc =>
    if pc == addr Malloc then
      do! v1 <- rs syscall_arg1;
      if v1 is VData sz then
        let: (m', b) := malloc_fun m (blocks s) sz in
        do! rs' <- updm rs syscall_ret (VPtr (b, 0));
        do! pc' <- rs ra;
        if pc' is VPtr pc' then
          Some (State m' rs' (VPtr pc'))
        else None
      else None
    else if pc == addr Free then
      do! v1 <- rs syscall_arg1;
      if v1 is VPtr p then
        do! m' <- free_fun m p.1;
        do! pc' <- rs ra;
        if pc' is VPtr pc' then
          Some (State m' rs (VPtr pc'))
        else None
      else None
    else if pc == addr Base then
      do! v1 <- rs syscall_arg1;
      if v1 is VPtr p then
        do! pc' <- rs ra;
        do! rs' <- updm rs syscall_ret (VPtr (p.1, 0));
        if pc' is VPtr pc' then
          Some (State m rs' (VPtr pc'))
        else None
      else None
    else if pc == addr Eq then
      do! v1 <- rs syscall_arg1;
      do! v2 <- rs syscall_arg2;
      let v3 := VData (as_word (v1 == v2)) in
      do! rs' <- updm rs syscall_ret v3;
      do! pc' <- rs ra;
      if pc' is VPtr pc' then
        Some (State m rs' (VPtr pc'))
      else None
    else None
  end.

Ltac solve_step_forward :=
  rewrite /malloc_fun;
  intros;
  repeat match goal with
  | e : ?x = _ |- context[?x] => rewrite e /=
  | e : (_, _) = (_, _) |- _ => case: e=> ??; subst
  | |- _ => rewrite (inj_eq (@uniq_addr _ addrs)) /=
  end.

Ltac solve_step_backward :=
  repeat (
    match goal with
    | p : Abstract.pointer _ |- _ => destruct p; simpl in *
    | e : (if (?pc == ?rhs) then _ else _) = Some _ |- _ =>
      move: e; have [->|?] := altP (pc =P rhs); move=> e //
    | |- _ => match_inv
    end
  ).

Lemma stepP s s' : Abstract.step s s' <-> step s = Some s'.
Proof.
split.
(* -> *)
by case: s s' / => /=; solve_step_forward.
(* <- *)
case: s=> m rs [pc|pc] /=;
intros; solve_step_backward; [> once (econstructor; solve [eauto | reflexivity]) ..].
Qed.

End AbstractE.

End AbstractE.
