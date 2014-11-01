Require Import lib.utils lib.partial_maps lib.Coqlib lib.hlist lib.Integers.
Require Import common.common symbolic.symbolic.
Require Import Coq.Vectors.Vector.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Set Implicit Arguments.

Import DoNotation.
Import PartMaps.

Section WithClasses.

Context {t : machine_types}
        {ops : machine_ops t}
        {sp : Symbolic.params}.

Variable table : list (Symbolic.syscall t).

Import HListNotations.
Import Symbolic.

Local Notation "x .+1" := (Word.add x Word.one).

Definition stepf (st : state t) : option (state t) :=
  let 'State mem reg pc@tpc extra := st in
  match PartMaps.get mem pc with
  | Some iti =>
    let: i@ti := iti in
    do! instr <- decode_instr i;
    match instr with
    | Nop =>
      let mvec := mkIVec NOP tpc ti [] in
      next_state_pc st mvec (pc.+1)
    | Const n r =>
      do! old <- PartMaps.get reg r;
      let: _@told := old in
      let ivec := mkIVec CONST tpc ti [told] in
      next_state_reg st ivec r (Word.casts n)
    | Mov r1 r2 =>
      do! a1 <- PartMaps.get reg r1;
      let: w1@t1 := a1 in
      do! a2 <- PartMaps.get reg r2;
      let: _@told := a2 in
      let mvec := mkIVec MOV tpc ti [t1;told] in
      next_state_reg st mvec r2 w1
    | Binop op r1 r2 r3 =>
      do! a1 <- PartMaps.get reg r1;
      let: w1@t1 := a1 in
      do! a2 <- PartMaps.get reg r2;
      let: w2@t2 := a2 in
      do! a3 <- PartMaps.get reg r3;
      let: _@told := a3 in
      let mvec := mkIVec (BINOP op) tpc ti [t1;t2;told] in
      next_state_reg st mvec r3 (binop_denote op w1 w2)
    | Load r1 r2 =>
      do! a1 <- PartMaps.get reg r1;
      let: w1@t1 := a1 in
      do! amem <- PartMaps.get mem w1;
      let: w2@t2 := amem in
      do! a2 <- PartMaps.get reg r2;
      let: _@told := a2 in
      let mvec := mkIVec LOAD tpc ti [t1;t2;told] in
      next_state_reg st mvec r2 w2
    | Store r1 r2 =>
      do! a1 <- PartMaps.get reg r1;
      let: w1@t1 := a1 in
      do! amem <- PartMaps.get mem w1;
      let: _@told := amem in
      do! a2 <- PartMaps.get reg r2;
      let: w2@t2 := a2 in
      let mvec := mkIVec STORE tpc ti [t1;t2;told] in
      next_state st mvec (fun ov =>
         do! mem' <- upd mem w1 w2@(tr ov);
         Some (State mem' reg (pc.+1)@(trpc ov) extra))
    | Jump r =>
      do! a <- PartMaps.get reg r;
      let: w@t1 := a in
      let mvec := mkIVec JUMP tpc ti [t1] in
      next_state_pc st mvec w
    | Bnz r n =>
      do! a <- PartMaps.get reg r;
      let: w@t1 := a in
      let pc' := Word.add pc (if w == Word.zero
                              then Word.one else Word.casts n) in
      let ivec := mkIVec BNZ tpc ti [t1] in
      next_state_pc st ivec pc'
    | Jal r =>
      do! a <- PartMaps.get reg r;
      let: w@t1 := a in
      do! oldtold <- PartMaps.get reg ra;
      let: _@told := oldtold in
      let mvec := mkIVec JAL tpc ti [t1; told] in
      next_state_reg_and_pc st mvec ra (pc.+1) w
    | JumpEpc | AddRule | GetTag _ _ | PutTag _ _ _ | Halt =>
      None
    end
  | None =>
    match get mem pc with
    | None =>
      do! sc <- get_syscall table pc;
      run_syscall sc st
    | Some _ =>
      None
    end
  end.

Lemma stepP :
  forall st st',
    stepf st = Some st' <->
    step table st st'.
Proof.
  intros st st'. split; intros STEP.
  { destruct st as [mem reg [pc tpc] int].
    simpl in STEP.
    destruct (get mem pc) as [[i ti]|] eqn:GET;
    apply obind_inv in STEP.
    - destruct STEP as (instr & INSTR & STEP).
      destruct instr; try discriminate;
          repeat match goal with
             | STEP : (do! x <- ?t; _) = Some _ |- _ =>
               destruct t eqn:?; simpl in STEP; try discriminate
             | x : common.atom _ _ |- _ =>
               destruct x; simpl in *
             | rv : OVec _ |- _ =>
               destruct rv; simpl in *
             | H : Some _ = Some _ |- _ =>
               inversion H; subst
           end;
      econstructor (solve [eauto]).
    - destruct STEP as (sc & GETCALL & STEP).
      econstructor (solve [eauto]).
  }
  { unfold stepf.
    inversion STEP; subst; rewrite PC; try (subst mvec);
    simpl;
    repeat match goal with
             | [H: ?Expr = _ |- context[?Expr]] =>
               rewrite H; simpl
           end; by reflexivity.
  }
Qed.

Lemma stepP' :
  forall st st',
    reflect (step table st st') (stepf st == Some st').
Proof.
  move => st st'.
  apply (iffP eqP); by move => /stepP.
Qed.

Definition build_ivec st : option (Symbolic.IVec Symbolic.ttypes)  :=
  match get (Symbolic.mem st) (Symbolic.pcv st) with
    | Some i =>
      match decode_instr (common.val i) with
        | Some op =>
          let part := @Symbolic.mkIVec Symbolic.ttypes (opcode_of op) (Symbolic.pct st) (common.tag i) in
          match op return (hlist Symbolic.ttypes (Symbolic.inputs (opcode_of op)) ->
                           Symbolic.IVec Symbolic.ttypes) -> option (Symbolic.IVec Symbolic.ttypes) with
            | Nop => fun part => Some (part [])
            | Const n r => fun part =>
                do! old <- get (Symbolic.regs st) r;
                Some (part [common.tag old])
            | Mov r1 r2 => fun part =>
              do! v1 <- get (Symbolic.regs st) r1;
              do! v2 <- get (Symbolic.regs st) r2;
              Some (part [(common.tag v1); (common.tag v2)])
            | Binop _ r1 r2 r3 => fun part =>
              do! v1 <- get (Symbolic.regs st) r1;
              do! v2 <- get (Symbolic.regs st) r2;
              do! v3 <- get (Symbolic.regs st) r3;
              Some (part [(common.tag v1); (common.tag v2); (common.tag v3)])
            | Load  r1 r2 => fun part =>
              do! w1 <- get (Symbolic.regs st) r1;
              do! w2 <- get (Symbolic.mem st) (common.val w1);
              do! old <- get (Symbolic.regs st) r2;
              Some (part [(common.tag w1); (common.tag w2); (common.tag old)])
            | Store  r1 r2 => fun part =>
              do! w1 <- get (Symbolic.regs st) r1;
              do! w2 <- get (Symbolic.regs st) r2;
              do! w3 <- get (Symbolic.mem st) (common.val w1);
              Some (part [(common.tag w1); (common.tag w2); (common.tag w3)])
            | Jump  r => fun part =>
              do! w <- get (Symbolic.regs st) r;
              Some (part [common.tag w])
            | Bnz  r n => fun part =>
              do! w <- get (Symbolic.regs st) r;
              Some (part [common.tag w])
            | Jal  r => fun part =>
              do! w <- get (Symbolic.regs st) r;
              do! old <- get (Symbolic.regs st) ra;
              Some (part [common.tag w; common.tag old])
            | JumpEpc => fun _ => None
            | AddRule => fun _ => None
            | GetTag _ _ => fun _ => None
            | PutTag _ _ _ => fun _ => None
            | Halt => fun _ => None
          end part
        | None => None
      end
    | None =>
      match Symbolic.get_syscall table (Symbolic.pcv st) with
        | Some sc =>
          Some (Symbolic.mkIVec SERVICE (Symbolic.pct st) (Symbolic.entry_tag sc) [])
        | None => None
      end
  end.

End WithClasses.
