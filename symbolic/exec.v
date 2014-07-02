Require Import lib.utils lib.partial_maps lib.Coqlib.
Require Import common.common symbolic.symbolic.
Require Import Coq.Vectors.Vector.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Set Implicit Arguments.

Import DoNotation.
Import PartMaps.

Section WithClasses.

Context {t : machine_types}
        {ops : machine_ops t}
        {sp : @Symbolic.symbolic_params t}.

Variable table : list (Symbolic.syscall t).

Import Vector.VectorNotations.

Definition build_mvec st : option (Symbolic.MVec (Symbolic.tag t))  :=
  let '(Symbolic.State mem reg pc@tpc int) := st in
  match get mem pc with
    | Some i =>
      match decode_instr (common.val i) with
        | Some op =>
          let part := @Symbolic.mkMVec (Symbolic.tag t) (opcode_of op) tpc (common.tag i) in
          match op return (Symbolic.mvec_operands (Symbolic.tag t) (Symbolic.nfields (opcode_of op)) ->
                           Symbolic.MVec (Symbolic.tag t)) -> option (Symbolic.MVec (Symbolic.tag t)) with
            | Nop => fun part => Some (part [])
            | Const n r => fun part => 
                do! old <- get reg r;
                Some (part [common.tag old])
            | Mov r1 r2 => fun part =>
              do! v1 <- get reg r1;
              do! v2 <- get reg r2;
              Some (part [(common.tag v1); (common.tag v2)])
            | Binop _ r1 r2 r3 => fun part =>
              do! v1 <- get reg r1;
              do! v2 <- get reg r2;
              do! v3 <- get reg r3;
              Some (part [(common.tag v1); (common.tag v2); (common.tag v3)])
            | Load  r1 r2 => fun part =>
              do! w1 <- get reg r1;
              do! w2 <- get mem (common.val w1);
              do! old <- get reg r2;
              Some (part [(common.tag w1); (common.tag w2); (common.tag old)])
            | Store  r1 r2 => fun part =>
              do! w1 <- get reg r1;
              do! w2 <- get reg r2;
              do! w3 <- get mem (common.val w1);
              Some (part [(common.tag w1); (common.tag w1); (common.tag w3)])
            | Jump  r => fun part =>
              do! w <- get reg r;
              Some (part [common.tag w])
            | Bnz  r n => fun part =>
              do! w <- get reg r;
              Some (part [common.tag w])
            | Jal  r => fun part =>
              do! w <- get reg r;
              do! old <- get reg ra;
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
      match Symbolic.get_syscall table pc with
        | Some sc =>
          Some (@Symbolic.mkMVec (Symbolic.tag _) SERVICE tpc (Symbolic.entry_tag sc) (Vector.nil _))
        | None => None
      end 
  end.

End WithClasses.