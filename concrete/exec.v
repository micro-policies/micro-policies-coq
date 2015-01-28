(* Executable formulation of concrete machine semantics *)

Require Import ssreflect ssrfun ssrbool ssrnat eqtype ssrint.
Require Import word partmap.
Require Import lib.utils common.types concrete.concrete.

Import Concrete. Import DoNotation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Masks.

Variable masks : Masks.

Context (mt : machine_types).
Context {ops : machine_ops mt}.

Open Scope word_scope.

Local Notation "x .+1" := (x + 1).

Definition step (st : state mt) : option (state mt) :=
  let 'mkState mem reg cache pc@tpc epc := st in
  do! i <- mem pc;
  do! instr <- decode_instr (vala i);
  let mvec := mkMVec (word_of_op (opcode_of instr)) tpc (taga i) in
  match instr with
  | Nop =>
    let mvec := mvec TNone TNone TNone in
    next_state_pc masks st mvec (pc.+1)
  | Const n r =>
    do! old <- reg r;
    let mvec := mvec (taga old) TNone TNone in
    next_state_reg masks st mvec r (swcast n)
  | Mov r1 r2 =>
    do! v1 <- reg r1;
    do! old <- reg r2;
    let mvec := mvec (taga v1) (taga old) TNone in
    next_state_reg masks st mvec r2 (vala v1)
  | Binop f r1 r2 r3 =>
    do! v1 <- reg r1;
    do! v2 <- reg r2;
    do! old <- reg r3;
    let mvec := mvec (taga v1) (taga v2) (taga old) in
    next_state_reg masks st mvec r3 (binop_denote f (vala v1) (vala v2))
  | Load r1 r2 =>
    do! v1 <- reg r1;
    do! v2 <- mem (vala v1);
    do! old <- reg r2;
    let mvec := mvec (taga v1) (taga v2) (taga old) in
    next_state_reg masks st mvec r2 (vala v2)
  | Store r1 r2 =>
    do! v1 <- reg r1;
    do! v2 <- reg r2;
    do! v3 <- mem (vala v1);
    let mvec := mvec (taga v1) (taga v2) (taga v3) in
    next_state masks st mvec (fun rvec =>
      do! mem' <- updm mem (vala v1) (vala v2)@(ctr rvec);
      Some (mkState mem' reg cache (pc.+1)@(ctrpc rvec) epc))
  | Jump r =>
    do! v <- reg r;
    let mvec := mvec (taga v) TNone TNone in
    next_state_pc masks st mvec (vala v)
  | Bnz r n =>
    do! v <- reg r;
    let mvec := mvec (taga v) TNone TNone in
    let pc' := pc + if (vala v) == 0%w then 1%w else swcast n in
    next_state_pc masks st mvec pc'
  | Jal r =>
    do! v <- reg r;
    do! old <- reg ra;
    let mvec := mvec (taga v) (taga old) TNone in
    next_state_reg_and_pc masks st mvec ra (pc.+1) (vala v)
  | JumpEpc =>
    let mvec := mvec (taga epc) TNone TNone in
    next_state_pc masks st mvec (vala epc)
  | AddRule =>
    let mvec := mvec TNone TNone TNone in
    next_state masks st mvec (fun rvec =>
      do! cache' <- add_rule cache masks mem;
      Some (mkState mem reg cache' (pc.+1)@(ctrpc rvec) epc))
  | GetTag r1 r2 =>
    do! v1 <- reg r1;
    do! old <- reg r2;
    let mvec := mvec (taga v1) (taga old) TNone in
    next_state_reg masks st mvec r2 (taga v1)
  | PutTag r1 r2 r3 =>
    do! v1 <- reg r1;
    do! v2 <- reg r2;
    do! old <- reg r3;
    let mvec := mvec (taga v1) (taga v2) (taga old) in
    next_state masks st mvec (fun rvec =>
      do! reg' <- updm reg r3 (vala v1)@(vala v2);
      Some (mkState mem reg' cache (pc.+1)@(ctrpc rvec) epc))
  | Halt => None
end.

Lemma atom_eta {V T} : forall a : atom V T, a = (vala a)@(taga a).
Proof. destruct a; reflexivity. Qed.

Ltac atom_eta :=
  match goal with
  | |- ?t = _ => apply (eq_trans (atom_eta t) (erefl _))
  end.

Lemma stepP : forall st st', step st = Some st' <->
  Concrete.step _ masks st st'.
Proof.
  intros st st'. split; intros STEP.
  - destruct st as [mem reg cache [pc tpc] epc]. simpl in STEP.
    apply obind_inv in STEP.
    destruct STEP as ([i it] & MEM & STEP).
    apply obind_inv in STEP.
    destruct STEP as (instr & INSTR & STEP).
    destruct instr; try discriminate;

    (* Invert all binds *)
    repeat match goal with
             | STEP : (do! x <- ?t; _) = Some _ |- _ =>
               destruct t eqn:?; simpl in STEP; try discriminate
             | x : atom _ _ |- _ =>
               destruct x; simpl in *
             | rv : RVec _ |- _ =>
               destruct rv; simpl in *
             | H : Some _ = Some _ |- _ =>
               inv H
           end;

    econstructor (solve [eauto | atom_eta]).

  - unfold step.
    inv STEP; rewrite PC; clear PC; simpl;
    rewrite INST; clear INST; simpl; subst mvec; try subst lookup; simpl; try congruence;
    repeat match goal with
    | H : ?X = _ |- context[?X] =>
      rewrite H; trivial
    end; simpl; trivial.
    + rewrite M1. simpl. trivial.
    + rewrite M1. simpl. trivial.
Qed.

Lemma stepP' : forall s1 s2, reflect (Concrete.step _ masks s1 s2) (step s1 == Some s2).
Proof.
  move => s1 s2.
  apply (iffP eqP); by move => /stepP.
Qed.

Definition build_cmvec st : option (Concrete.MVec mt) :=
  match Concrete.mem st (Concrete.pcv st) with
    | Some i =>
      match decode_instr (vala i) with
        | Some op =>
          let part := @Concrete.mkMVec mt (word_of_op (opcode_of op))
                                       (Concrete.pct st) (taga i) in
          match op  with
            | Nop => fun part => Some (part Concrete.TNone Concrete.TNone Concrete.TNone)
            | Const n r =>
              fun part =>
                do! old <- (Concrete.regs st) r;
                  Some (part (taga old) Concrete.TNone Concrete.TNone)
            | Mov r1 r2 =>
              fun part =>
                do! v1 <- (Concrete.regs st) r1;
                do! v2 <- (Concrete.regs st) r2;
                  Some (part (taga v1) (taga v2) Concrete.TNone)
            | Binop _ r1 r2 r3 => fun part =>
              do! v1 <- (Concrete.regs st) r1;
              do! v2 <- (Concrete.regs st) r2;
              do! v3 <- (Concrete.regs st) r3;
                Some (part (taga v1) (taga v2) (taga v3))
            | Load r1 r2 => fun part =>
              do! w1 <- (Concrete.regs st) r1;
              do! w2 <- Concrete.mem st (vala w1);
              do! old <- (Concrete.regs st) r2;
                Some (part (taga w1) (taga w2) (taga old))
            | Store r1 r2 => fun part =>
              do! w1 <- (Concrete.regs st) r1;
              do! w2 <- (Concrete.regs st) r2;
                do! w3 <- Concrete.mem st (vala w1);
                Some (part (taga w1) (taga w2) (taga w3))
            | Jump r => fun part =>
              do! w <- (Concrete.regs st) r;
                Some (part (taga w) Concrete.TNone Concrete.TNone)
            | Bnz r n => fun part =>
              do! w <- (Concrete.regs st) r;
                Some (part (taga w) Concrete.TNone Concrete.TNone)
            | Jal r => fun part =>
              do! w <- (Concrete.regs st) r;
              do! old <- (Concrete.regs st) ra;
                Some (part (taga w) (taga old) Concrete.TNone)
            | JumpEpc =>
              fun part =>
                Some (part (taga (Concrete.epc st)) Concrete.TNone Concrete.TNone)
            | AddRule =>
              fun part =>
                Some (part Concrete.TNone Concrete.TNone Concrete.TNone)
            | GetTag r1 r2 =>
              fun part =>
                do! w1 <- (Concrete.regs st) r1;
                do! old <- (Concrete.regs st) r2;
                Some (part (taga w1) (taga old) Concrete.TNone)
            | PutTag r1 r2 r3 =>
              fun part =>
                do! w1 <- (Concrete.regs st) r1;
                do! w2 <- (Concrete.regs st) r2;
                do! old <- (Concrete.regs st) r3;
                Some (part (taga w1) (taga w2) (taga old))
            | Halt => fun _ => None
          end part
        | None => None
      end
    | None => None
  end.

Lemma step_lookup_success_or_fault cst cst' :
  Concrete.step _ masks cst cst' ->
  exists cmvec,
    build_cmvec cst = Some cmvec /\
    match cache_lookup (cache cst) masks cmvec with
    | Some crvec => pct cst' = ctrpc crvec
    | None =>
      let cmem' := store_mvec (mem cst) cmvec in
      cst' = mkState cmem'
                     (regs cst)
                     (cache cst)
                     (fault_handler_start mt)@TKernel
                     (pc cst)
    end.
Proof.
  move => STEP.
  rewrite /build_cmvec.
  inv STEP; subst; rewrite /pct /=;
  repeat match goal with
  | E : ?x = _ |- context[?x] => rewrite E; clear E; simpl
  end;
  eexists; (split; first by reflexivity);
  subst mvec;
  unfold next_state_reg, next_state_pc,
         next_state_reg_and_pc, next_state, miss_state, pct in *;
  simpl in *; match_inv;
  repeat match goal with
  | E : ?x = _ |- context[?x] => rewrite E; clear E; simpl
  end; reflexivity.
Qed.

Lemma lookup_none_step cst cmvec :
  build_cmvec cst = Some cmvec ->
  Concrete.cache_lookup (Concrete.cache cst) masks cmvec = None ->
  Concrete.step _ masks cst (Concrete.mkState (Concrete.store_mvec (Concrete.mem cst) cmvec)
                                              (Concrete.regs cst)
                                              (Concrete.cache cst)
                                              (Concrete.fault_handler_start mt)@Concrete.TKernel
                                              (Concrete.pc cst)).
Proof.
  move=> CMVEC LOOKUP.
  apply/stepP.
  rewrite (Concrete.state_eta cst) /=.
  move: CMVEC.
  rewrite /build_cmvec.
  case: (getm _ _) => [[i ti]|] //=.
  case: (decode_instr i) => [instr|] //= CMVEC;
  destruct instr; simpl in *; match_inv;
  by rewrite /next_state_reg /next_state_pc /next_state_reg_and_pc /next_state /miss_state //=
             LOOKUP.
Qed.

Lemma step_build_cmvec cst cst' :
  Concrete.step _ masks cst cst' ->
  exists cmvec, build_cmvec cst = Some cmvec.
Proof.
  by move=> /step_lookup_success_or_fault [cmvec [? _]]; eauto.
Qed.

Lemma build_cmvec_ctpc cst cmvec :
  build_cmvec cst = Some cmvec ->
  Concrete.ctpc cmvec = Concrete.pct cst.
Proof.
  case: cst => [mem regs cache [v t] epc].
  rewrite /build_cmvec => H.
  match_inv.
  repeat match goal with
  | H : ?X = _ |- _ =>
    match X with
    | context [match ?Y with _ => _ end] =>
      destruct Y; simpl in H
    end
  end; match_inv;
  solve [ reflexivity | congruence ].
Qed.

Lemma build_cmvec_cop_cti cst cmvec :
  build_cmvec cst = Some cmvec ->
  exists i instr,
    [/\ (Concrete.mem cst) (Concrete.pcv cst) =
        Some i@(Concrete.cti cmvec),
        decode_instr i = Some instr &
        word_of_op (opcode_of instr) = Concrete.cop cmvec].
Proof.
  rewrite /build_cmvec.
  case: (getm _ _) => [[i ti]|] //= MVEC. exists i. move: MVEC.
  case: (decode_instr i) => [instr|] //= MVEC. exists instr.
  destruct instr; match_inv; simpl; eauto using And3.
  discriminate.
Qed.

End Masks.
