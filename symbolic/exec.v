From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From CoqUtils Require Import hseq word fmap.
Require Import lib.utils common.types symbolic.symbolic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import DoNotation.

Section WithClasses.

Context {mt : machine_types}
        {ops : machine_ops mt}
        {sp : Symbolic.params}.

Variable table : Symbolic.syscall_table mt.

Import Symbolic.

Local Open Scope word_scope.
Local Notation "x .+1" := (x + 1).

Definition stepf (st : state mt) : option (state mt) :=
  let 'State mem reg pc@tpc extra := st in
  match mem pc with
  | Some iti =>
    let: i@ti := iti in
    do! instr <- decode_instr i;
    match instr with
    | Nop =>
      let mvec := IVec NOP tpc ti [hseq] in
      next_state_pc st mvec (pc.+1)
    | Const n r =>
      do! old <- reg r;
      let: _@told := old in
      let ivec := IVec CONST tpc ti [hseq told] in
      next_state_reg st ivec r (swcast n)
    | Mov r1 r2 =>
      do! a1 <- reg r1;
      let: w1@t1 := a1 in
      do! a2 <- reg r2;
      let: _@told := a2 in
      let mvec := IVec MOV tpc ti [hseq t1;told] in
      next_state_reg st mvec r2 w1
    | Binop op r1 r2 r3 =>
      do! a1 <- reg r1;
      let: w1@t1 := a1 in
      do! a2 <- reg r2;
      let: w2@t2 := a2 in
      do! a3 <- reg r3;
      let: _@told := a3 in
      let mvec := IVec (BINOP op) tpc ti [hseq t1;t2;told] in
      next_state_reg st mvec r3 (binop_denote op w1 w2)
    | Load r1 r2 =>
      do! a1 <- reg r1;
      let: w1@t1 := a1 in
      do! amem <- mem w1;
      let: w2@t2 := amem in
      do! a2 <- reg r2;
      let: _@told := a2 in
      let mvec := IVec LOAD tpc ti [hseq t1;t2;told] in
      next_state_reg st mvec r2 w2
    | Store r1 r2 =>
      do! a1 <- reg r1;
      let: w1@t1 := a1 in
      do! amem <- mem w1;
      let: _@told := amem in
      do! a2 <- reg r2;
      let: w2@t2 := a2 in
      let mvec := IVec STORE tpc ti [hseq t1;t2;told] in
      @next_state _ _ st mvec (fun ov =>
         do! mem' <- updm mem w1 w2@(tr ov);
         Some (State mem' reg (pc.+1)@(trpc ov) extra))
    | Jump r =>
      do! a <- reg r;
      let: w@t1 := a in
      let mvec := IVec JUMP tpc ti [hseq t1] in
      next_state_pc st mvec w
    | Bnz r n =>
      do! a <- reg r;
      let: w@t1 := a in
      let pc' := pc + (if w == 0
                       then 1 else swcast n) in
      let ivec := IVec BNZ tpc ti [hseq t1] in
      next_state_pc st ivec pc'
    | Jal r =>
      do! a <- reg r;
      let: w@t1 := a in
      do! oldtold <- reg ra;
      let: _@told := oldtold in
      let mvec := IVec JAL tpc ti [hseq t1; told] in
      next_state_reg_and_pc st mvec ra (pc.+1) w
    | JumpEpc | AddRule | GetTag _ _ | PutTag _ _ _ | Halt =>
      None
    end
  | None =>
    match mem pc with
    | None =>
      do! sc <- table pc;
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
    move: STEP => /=; case GET: (mem pc) => [[i ti]|] //= STEP;
    apply obind_inv in STEP.
    - destruct STEP as (instr & INSTR & STEP).
      destruct instr; try discriminate;
          repeat match goal with
             | STEP : (do! x <- ?t; _) = Some _ |- _ =>
               destruct t eqn:?; simpl in STEP; try discriminate
             | x : atom _ _ |- _ =>
               destruct x; simpl in *
             | rv : ovec _ |- _ =>
               destruct rv; simpl in *
             | H : Some _ = Some _ |- _ =>
               inversion H; subst; clear H
           end;
      s_econstructor (solve [eauto]).

    - destruct STEP as (sc & GETCALL & STEP).
      s_econstructor (solve [eauto]).
  }
  { unfold stepf.
    inversion STEP; subst; rewrite PC; try (subst mv);
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

Definition build_ivec st : option (ivec ttypes)  :=
  match mem st (pcv st) with
    | Some i =>
      match decode_instr (vala i) with
        | Some op =>
          let part := @IVec ttypes (opcode_of op) (pct st) (taga i) in
          match op return (hseq (tag_type ttypes) (inputs (opcode_of op)) ->
                           ivec ttypes) -> option (ivec ttypes) with
            | Nop => fun part => Some (part [hseq])
            | Const n r => fun part =>
                do! old <- regs st r;
                Some (part [hseq taga old])
            | Mov r1 r2 => fun part =>
              do! v1 <- regs st r1;
              do! v2 <- regs st r2;
              Some (part [hseq (taga v1); (taga v2)])
            | Binop _ r1 r2 r3 => fun part =>
              do! v1 <- regs st r1;
              do! v2 <- regs st r2;
              do! v3 <- regs st r3;
              Some (part [hseq (taga v1); (taga v2); (taga v3)])
            | Load  r1 r2 => fun part =>
              do! w1 <- regs st r1;
              do! w2 <- (mem st) (vala w1);
              do! old <- regs st r2;
              Some (part [hseq (taga w1); (taga w2); (taga old)])
            | Store  r1 r2 => fun part =>
              do! w1 <- regs st r1;
              do! w2 <- regs st r2;
              do! w3 <- mem st (vala w1);
              Some (part [hseq (taga w1); (taga w2); (taga w3)])
            | Jump  r => fun part =>
              do! w <- regs st r;
              Some (part [hseq taga w])
            | Bnz  r n => fun part =>
              do! w <- regs st r;
              Some (part [hseq taga w])
            | Jal  r => fun part =>
              do! w <- regs st r;
              do! old <- regs st ra;
              Some (part [hseq taga w; taga old])
            | JumpEpc => fun _ => None
            | AddRule => fun _ => None
            | GetTag _ _ => fun _ => None
            | PutTag _ _ _ => fun _ => None
            | Halt => fun _ => None
          end part
        | None => None
      end
    | None =>
      match table (pcv st) with
        | Some sc =>
          Some (IVec SERVICE (pct st) (entry_tag sc) [hseq])
        | None => None
      end
  end.

Lemma step_build_ivec st st' :
  step table st st' ->
  exists ivec ovec,
    build_ivec st = Some ivec /\
    transfer ivec = Some ovec.
Proof.
  move/stepP.
  rewrite {1}(state_eta st) /= /build_ivec.
  case: (getm _ _) => [[i ti]|] //=; last first.
    case: (getm _ _) => [sc|] //=.
    rewrite /run_syscall /=.
    case TRANS: (transfer _) => [ovec|] //= _.
    by eauto.
  case: (decode_instr i) => [instr|] //=.
  rewrite /next_state_pc /next_state_reg /next_state_reg_and_pc /next_state.
  by destruct instr; move=> STEP; match_inv; first [ eauto | discriminate ].
Qed.

End WithClasses.
