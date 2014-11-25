(* Base memory version of concrete machine semantics *)

Require Import ZArith.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Require Import lib.Integers lib.utils lib.partial_maps lib.Coqlib common.common concrete.concrete.
Require Import List.

Import ListNotations.
Import Concrete. Import DoNotation.

Open Scope Z_scope.

Section Masks.

Variable masks : Masks.

Context (mt : machine_types).
Context {ops : machine_ops mt}.

Open Scope word_scope.

Local Notation "x .+1" := (x + Word.one).

Let atom := atom (word mt) (word mt).
Local Notation memory := (word_map mt atom).

Variable basemem : memory. 

Definition get_with_base (m:memory) (k:word mt) : option atom :=
  match PartMaps.get m k with
  | Some a => Some a 
  | None => 
      match PartMaps.get basemem k with
      | Some a => Some a 
      | None => None
      end
  end.

Definition add_rule_b (cache : (rules (word mt))) (masks : Masks) (mem : memory) : option (rules (word mt)) :=
  do! aop   <- get_with_base mem (Mop mt);
  do! atpc  <- get_with_base mem (Mtpc mt);
  do! ati   <- get_with_base mem (Mti mt);
  do! at1   <- get_with_base mem (Mt1 mt);
  do! at2   <- get_with_base mem (Mt2 mt);
  do! at3   <- get_with_base mem (Mt3 mt);
  do! atrpc <- get_with_base mem (Mtrpc mt);
  do! atr   <- get_with_base mem (Mtr mt);
  do! op    <- word_to_op (val aop);
  let dcm := dc (masks false op) in
  Some ((mask_dc dcm (mkMVec (val aop) (val atpc)
                             (val ati) (val at1) (val at2) (val at3)),
         mkRVec (val atrpc) (val atr)) :: cache).

(* TODO: mt should be named t, or vice versa, globally! *)
Definition step (st : state mt) : option (state mt) :=
  let 'mkState mem reg cache pc@tpc epc := st in
  do! i <- get_with_base mem pc;
  do! instr <- decode_instr (val i);
  let mvec := mkMVec (op_to_word (opcode_of instr)) tpc (tag i) in
  match instr with
  | Nop =>
    let mvec := mvec TNone TNone TNone in
    next_state_pc masks st mvec (pc.+1) 
  | Const n r =>
    do! old <- PartMaps.get reg r;
    let mvec := mvec (tag old) TNone TNone in
    next_state_reg masks st mvec r (Word.casts n)
  | Mov r1 r2 =>
    do! v1 <- PartMaps.get reg r1;
    do! old <- PartMaps.get reg r2;
    let mvec := mvec (tag v1) (tag old) TNone in
    next_state_reg masks st mvec r2 (val v1)
  | Binop f r1 r2 r3 =>
    do! v1 <- PartMaps.get reg r1;
    do! v2 <- PartMaps.get reg r2;
    do! old <- PartMaps.get reg r3;
    let mvec := mvec (tag v1) (tag v2) (tag old) in
    next_state_reg masks st mvec r3 (binop_denote f (val v1) (val v2))
  | Load r1 r2 =>
    do! v1 <- PartMaps.get reg r1;
    do! v2 <- get_with_base mem (val v1);
    do! old <- PartMaps.get reg r2;
    let mvec := mvec (tag v1) (tag v2) (tag old) in
    next_state_reg masks st mvec r2 (val v2)
  | Store r1 r2 =>
    do! v1 <- PartMaps.get reg r1;
    do! v2 <- PartMaps.get reg r2;
    do! v3 <- get_with_base mem (val v1);
    let mvec := mvec (tag v1) (tag v2) (tag v3) in
    next_state masks st mvec (fun rvec =>
      do! mem' <- PartMaps.upd mem (val v1) (val v2)@(ctr rvec);
      Some (mkState mem' reg cache (pc.+1)@(ctrpc rvec) epc))
  | Jump r =>
    do! v <- PartMaps.get reg r;
    let mvec := mvec (tag v) TNone TNone in
    next_state_pc masks st mvec (val v)
  | Bnz r n =>
    do! v <- PartMaps.get reg r;
    let mvec := mvec (tag v) TNone TNone in
    let pc' := pc + if (val v) == Word.zero then Word.one else Word.casts n in
    next_state_pc masks st mvec pc'
  | Jal r =>
    do! v <- PartMaps.get reg r;
    do! old <- PartMaps.get reg ra;
    let mvec := mvec (tag v) (tag old) TNone in
    next_state_reg_and_pc masks st mvec ra (pc.+1) (val v)
  | JumpEpc =>
    let mvec := mvec (tag epc) TNone TNone in
    next_state_pc masks st mvec (val epc)
  | AddRule =>
    let mvec := mvec TNone TNone TNone in
    next_state masks st mvec (fun rvec =>
      do! cache' <- add_rule_b cache masks mem;
      Some (mkState mem reg cache' (pc.+1)@(ctrpc rvec) epc))
  | GetTag r1 r2 =>
    do! v1 <- PartMaps.get reg r1;
    do! old <- PartMaps.get reg r2;
    let mvec := mvec (tag v1) (tag old) TNone in
    next_state_reg masks st mvec r2 (tag v1)
  | PutTag r1 r2 r3 =>
    do! v1 <- PartMaps.get reg r1;
    do! v2 <- PartMaps.get reg r2;
    do! old <- PartMaps.get reg r3;
    let mvec := mvec (tag v1) (tag v2) (tag old) in
    next_state masks st mvec (fun rvec =>
      do! reg' <- PartMaps.upd reg r3 (val v1)@(val v2);
      Some (mkState mem reg' cache (pc.+1)@(ctrpc rvec) epc))
  | Halt => None
end.

(*
Lemma atom_eta {V T} : forall a : atom V T, a = (val a)@(tag a).
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

Lemma stepP' : forall s1 s2, ssrbool.reflect (Concrete.step _ masks s1 s2) (step s1 == Some s2).
Proof.
  move => s1 s2.
  apply (iffP eqP); by move => /stepP.
Qed.


Import PartMaps.

Definition build_cmvec st : option (Concrete.MVec (word mt)) :=
  let '(Concrete.mkState mem reg cache pc@tpc epc) := st in
  match get mem pc with
    | Some i =>
      match decode_instr (val i) with
        | Some op =>
          let part := @Concrete.mkMVec (word mt) (op_to_word (opcode_of op))
                                       tpc (common.tag i) in
          match op  with
            | Nop => fun part => Some (part Concrete.TNone Concrete.TNone Concrete.TNone)
            | Const n r =>
              fun part =>
                do! old <- PartMaps.get reg r;
                  Some (part (common.tag old) Concrete.TNone Concrete.TNone)
            | Mov r1 r2 =>
              fun part =>
                do! v1 <- PartMaps.get reg r1;
                do! v2 <- PartMaps.get reg r2;
                  Some (part (common.tag v1) (common.tag v2) Concrete.TNone)
            | Binop _ r1 r2 r3 => fun part =>
              do! v1 <- PartMaps.get reg r1;
              do! v2 <- PartMaps.get reg r2;
              do! v3 <- PartMaps.get reg r3;
                Some (part (common.tag v1) (common.tag v2) (common.tag v3))
            | Load r1 r2 => fun part =>
              do! w1 <- PartMaps.get reg r1;
              do! w2 <- get mem (val w1);
              do! old <- PartMaps.get reg r2;
                Some (part (common.tag w1) (common.tag w2) (common.tag old))
            | Store r1 r2 => fun part =>
              do! w1 <- PartMaps.get reg r1;
              do! w2 <- PartMaps.get reg r2;
                do! w3 <- get mem (val w1);
                Some (part (common.tag w1) (common.tag w2) (common.tag w3))
            | Jump r => fun part =>
              do! w <- PartMaps.get reg r;
                Some (part (common.tag w) Concrete.TNone Concrete.TNone)
            | Bnz r n => fun part =>
              do! w <- PartMaps.get reg r;
                Some (part (common.tag w) Concrete.TNone Concrete.TNone)
            | Jal r => fun part =>
              do! w <- PartMaps.get reg r;
              do! old <- PartMaps.get reg ra;
                Some (part (common.tag w) (common.tag old) Concrete.TNone)
            | JumpEpc =>
              fun part =>
                Some (part (common.tag epc) Concrete.TNone Concrete.TNone)
            | AddRule =>
              fun part =>
                Some (part Concrete.TNone Concrete.TNone Concrete.TNone)
            | GetTag r1 r2 =>
              fun part =>
                do! w1 <- PartMaps.get reg r1;
                do! old <- PartMaps.get reg r2;
                Some (part (common.tag w1) (common.tag old) Concrete.TNone)
            | PutTag r1 r2 r3 =>
              fun part =>
                do! w1 <- PartMaps.get reg r1;
                do! w2 <- PartMaps.get reg r2;
                do! old <- PartMaps.get reg r3;
                Some (part (common.tag w1) (common.tag w2) (common.tag old))
            | Halt => fun _ => None
          end part
        | None => None
      end
    | None => None
  end.

Lemma step_build_cmvec cst cst' :
  Concrete.step _ masks cst cst' ->
  exists cmvec, build_cmvec cst = Some cmvec.
Proof.
  intros STEP.
  inv STEP; try subst mvec;
  unfold next_state_pc, next_state_reg_and_pc, next_state, miss_state in *;
  match_inv; simpl in *;
  repeat match goal with
  | H : ?X = _ |- context[?X] => rewrite H; simpl
  end;
  solve [eauto].
Qed.

Lemma build_cmvec_ctpc cst cmvec :
  build_cmvec cst = Some cmvec ->
  Concrete.ctpc cmvec = common.tag (Concrete.pc cst).
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
*)

End Masks.


