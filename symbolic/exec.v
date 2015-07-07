Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.ssrnat Ssreflect.seq.
Require Import CoqUtils.hseq CoqUtils.word CoqUtils.partmap.
Require Import lib.utils common.types symbolic.symbolic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

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
  let: State mem reg pc@tpc extra := st in
  let regv := omap vala ∘ reg in
  let memv := omap vala ∘ mem in
  match mem pc with
  | Some iti =>
    let: i@ti := iti in
    do! instr <- decode_instr i;
    match instr with
    | Nop =>
      let lv := LVec NOP tpc ti [hseq] in
      next_state_pc st lv (pc.+1)
    | Const n r =>
      let lv := LVec CONST tpc ti [hseq r] in
      next_state_reg st lv r (swcast n)
    | Mov r1 r2 =>
      do! w1 <- regv r1;
      let mvec := LVec MOV tpc ti [hseq r1; r2] in
      next_state_reg st mvec r2 w1
    | Binop op r1 r2 r3 =>
      do! w1 <- regv r1;
      do! w2 <- regv r2;
      let lv := LVec (BINOP op) tpc ti [hseq r1; r2; r3] in
      next_state_reg st lv r3 (binop_denote op w1 w2)
    | Load r1 r2 =>
      do! w1 <- regv r1;
      do! w2 <- memv w1;
      let lv := LVec LOAD tpc ti [hseq r1; w1; r2] in
      next_state_reg st lv r2 w2
    | Store r1 r2 =>
      do! w1 <- regv r1;
      do! w2 <- regv r2;
      let lv := LVec STORE tpc ti [hseq r1; r2; w1] in
      do! st'  <- next_state_pc st lv (pc.+1);
      let: State mem' reg' pc' extra' := st' in
      do! mem'' <- repm mem' w1 (fun a => w2@(taga a));
      Some (State mem'' reg' pc' extra')
    | Jump r =>
      do! w <- regv r;
      let lv := LVec JUMP tpc ti [hseq r] in
      next_state_pc st lv w
    | Bnz r n =>
      do! w <- regv r;
      let pc' := pc + (if w == 0 then 1 else swcast n) in
      let lv := LVec BNZ tpc ti [hseq r] in
      next_state_pc st lv pc'
    | Jal r =>
      do! w <- regv r;
      let lv := LVec JAL tpc ti [hseq r; ra] in
      next_state_reg_and_pc st lv ra (pc.+1) w
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

Ltac unfold_next_states :=
  rewrite /next_state_pc /next_state_reg /next_state_reg_and_pc /next_state /=.

Lemma stepP st st' :
  stepf st = Some st' <-> step table st st'.
Proof.
  split.
  - case: st => [mem reg [pc tpc] int] /=.
    case GET: (mem pc) => [[i ti]|] /=.
    + case INSTR: (decode_instr i) => [[]|] //=; unfold_next_states => STEP;
        repeat match goal with
                 | STEP : (do! x <- ?t; _) = Some _ |- _ =>
                   destruct t eqn:?; simpl in STEP; try discriminate
                 | a : atom _ _ |- _ =>
                   destruct a; simpl in *
                 | lv : lvec |- _ =>
                   destruct lv; simpl in *
                 | EQ : Some _ = Some _ |- _ =>
                   inversion EQ; subst; clear EQ
               end;
        s_econstructor (solve [
          unfold_next_states;
          repeat match goal with EQ : _ = _ |- _ => rewrite EQ /= end;
          eauto]).
    + case GETCALL: (table pc) => [sc|] //= STEP.
      s_econstructor (solve [eauto]).
  - inversion 1; subst; rewrite /= PC; try (subst lv); simpl;
      repeat match goal with [EQ : ?Expr = _ |- context[?Expr]] => rewrite EQ /= end;
      reflexivity.
Qed.

Lemma stepP' :
  forall st st',
    reflect (step table st st') (stepf st == Some st').
Proof.
  move => st st'.
  apply (iffP eqP); by move => /stepP.
Qed.

Definition build_ivec (st : state mt) : option (mvec' ttypes) :=
  match mem st (pcv st) with
    | Some i =>
      match decode_instr (vala i) with
        | Some op =>
          let part ts := MVec' (opcode_of op) (pct st) (taga i) ts in
          match op return (hseq (tag_type ttypes) (inputs (opcode_of op)) ->
                           mvec' ttypes) -> option (mvec' ttypes) with
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
          Some (MVec' SERVICE (pct st) (entry_tag sc) [hseq])
        | None => None
      end
  end.

Lemma step_build_ivec st st' :
  step table st st' ->
  exists iop ivec ovec,
    build_ivec st = Some (existT _ iop ivec) /\
    transfer ivec = Some ovec.
Proof.
  move/stepP.
  rewrite {1}(state_eta st) /= /build_ivec.
  case: (getm _ _) => [[i ti]|] //=; last first.
  - case: (getm _ _) => [sc|] //=.
    rewrite /run_syscall /=.
    case TRANS: (transfer _) => [ovec|] //= _.
    by eauto.
  - case: (decode_instr i) => [instr|] //=.
    unfold_next_states; destruct instr; unfold_next_states => STEP;
      match_inv; try discriminate;
      repeat match goal with
        |- context[do! _ <- getm ?pmap ?k; _] =>
        repeat match goal with
          H : context[getm pmap k] |- _ => move: H
        end;
        let w    := fresh "w"    in
        let t    := fresh "t"    in
        case ?: (pmap k) => [[? ?]|//] /=;
        repeat match goal with
          |- Some _ = Some _ -> _ => case=> ?
        end;
        subst
      end; eauto.
Qed.

End WithClasses.
