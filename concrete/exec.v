(* Executable formulation of concrete machine semantics *)

Require Import ZArith.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Require Import lib.utils lib.partial_maps lib.Coqlib common.common concrete.concrete.
Require Import List.

Import ListNotations.
Import Concrete. Import DoNotation.

Open Scope Z_scope.

Section Masks.

Variable masks : Masks.

Context (mt : machine_types).
Context {ops : machine_ops mt}.
Context {cp : concrete_params mt}.

Open Scope word_scope.

Local Notation "x .+1" := (x + Z_to_word 1).

Definition step (st : state mt) : option (state mt) :=
  let 'mkState mem reg cache pc@tpc epc := st in
  do! i <- PartMaps.get mem pc;
  do! instr <- decode_instr (val i);
  let mvec := mkMVec (op_to_word (opcode_of instr)) tpc (tag i) in
  match instr with
  | Nop =>
    let mvec := mvec TNone TNone TNone in
    next_state_pc _ masks st mvec (pc.+1)
  | Const n r =>
    let old := TotalMaps.get reg r in
    let mvec := mvec (tag old) TNone TNone in
    next_state_reg _ masks st mvec r (imm_to_word n)
  | Mov r1 r2 =>
    let v1 := TotalMaps.get reg r1 in
    let old := TotalMaps.get reg r2 in
    let mvec := mvec (tag v1) (tag old) TNone in
    next_state_reg _ masks st mvec r2 (val v1)
  | Binop f r1 r2 r3 =>
    let v1 := TotalMaps.get reg r1 in
    let v2 := TotalMaps.get reg r2 in
    let old := TotalMaps.get reg r3 in
    let mvec := mvec (tag v1) (tag v2) (tag old) in
    next_state_reg _ masks st mvec r3 (binop_denote f (val v1) (val v2))
  | Load r1 r2 =>
    let v1 := TotalMaps.get reg r1 in
    do! v2 <- PartMaps.get mem (val v1);
    let old := TotalMaps.get reg r2 in
    let mvec := mvec (tag v1) (tag v2) (tag old) in
    next_state_reg _ masks st mvec r2 (val v2)
  | Store r1 r2 =>
    let v1 := TotalMaps.get reg r1 in
    let v2 := TotalMaps.get reg r2 in
    do! v3 <- PartMaps.get mem (val v1);
    let mvec := mvec (tag v1) (tag v2) (tag v3) in
    next_state _ masks st mvec (fun rvec =>
      do! mem' <- PartMaps.upd mem (val v1) (val v2)@(ctr rvec);
      Some (mkState mem' reg cache (pc.+1)@(ctrpc rvec) epc))
  | Jump r =>
    let v := TotalMaps.get reg r in
    let mvec := mvec (tag v) TNone TNone in
    next_state_pc _ masks st mvec (val v)
  | Bnz r n =>
    let v := TotalMaps.get reg r in
    let mvec := mvec (tag v) TNone TNone in
    let pc' := pc + if (val v) == Z_to_word 0 then Z_to_word 1 else imm_to_word n in
    next_state_pc _ masks st mvec pc'
  | Jal r =>
    let v := TotalMaps.get reg r in
    let old := TotalMaps.get reg ra in
    let mvec := mvec (tag v) (tag old) TNone in
    next_state_reg_and_pc _ masks st mvec ra (pc.+1) (val v)
  | JumpEpc =>
    let mvec := mvec (tag epc) TNone TNone in
    next_state_pc _ masks st mvec (val epc)
  | AddRule =>
    let mvec := mvec TNone TNone TNone in
    next_state _ masks st mvec (fun rvec =>
      do! cache' <- add_rule ops cache masks (is_kernel_tag _ tpc) mem;
      Some (mkState mem reg cache' (pc.+1)@(ctrpc rvec) epc))
  | GetTag r1 r2 =>
    let v1 := TotalMaps.get reg r1 in
    let old := TotalMaps.get reg r2 in
    let mvec := mvec (tag v1) (tag old) TNone in
    next_state_reg _ masks st mvec r2 (tag v1)
  | PutTag r1 r2 r3 =>
    let v1 := TotalMaps.get reg r1 in
    let v2 := TotalMaps.get reg r2 in
    let old := TotalMaps.get reg r3 in
    let mvec := mvec (tag v1) (tag v2) (tag old) in
    next_state _ masks st mvec (fun rvec =>
      let reg' := TotalMaps.upd reg r3 (val v1)@(val v2) in
      Some (mkState mem reg' cache (pc.+1)@(ctrpc rvec) epc))
  | Halt => None
end.

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
    apply bind_inv in STEP.
    destruct STEP as ([i it] & MEM & STEP).
    apply bind_inv in STEP.
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
    | H : _ = _ |- _ =>
    rewrite ->H in *; clear H
    end; simpl; trivial.
    + rewrite M1. simpl. trivial.
    + rewrite M1. simpl. trivial.
Qed.

Fixpoint stepn (max_steps : nat) (st : state mt) : option (state mt) :=
  match max_steps with
  | O => Some st
  | S max_steps' =>
    do! st' <- step st;
    stepn max_steps' st'
  end.

Fixpoint tracen (max_steps : nat) (st : state mt) : list (state mt) :=
  match max_steps with
  | O => []
  | S max_steps' =>
    match step st with
    | None => []
    | Some st' => st' :: tracen max_steps' st'
    end
  end.

Definition trace (st : state mt) := tracen 10000 st.

End Masks.
