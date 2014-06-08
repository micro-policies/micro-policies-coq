Require Import List Arith ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.SetoidDec.
Require Coq.Vectors.Vector.

Require Import utils common.
Require Import rules.

Set Implicit Arguments.

Import DoNotation.
Import ListNotations.

Module Symbolic.

Open Scope bool_scope.
Open Scope Z_scope.

Section WithClasses.

Context (t : machine_types).
Context {ops : machine_ops t}.

Class symbolic_params := {
  memory : Type;
  registers : Type;

  (* CH: One nice extension could be to distinguish different tag
     types. In many policies the tags on the pc, the tags on registers,
     and the tags on memory (including instructions which are also
     stored in memory) are morally drawn from different types. Sure,
     one can squeeze them all into one big disjoint union, but that's
     inefficient and conceptually inelegant given that we have a
     better way of dealing with overlaps (pc != registers != memory).
     Even for kernel protection itself ENTRY is only used for tagging
     memory, and the is_call flag for USER is only used for the pc tag.
     If we implement this extension the big comment explaining this
     at the beginning of rules.v would become instead a set of types.
     Would this extension be hard to add / complicate other things? *)
  tag : Type;

  internal_state : Type;

  tag_eq :> EqDec (eq_setoid tag);

  get_mem : memory -> word t -> option (atom (word t) tag);
  upd_mem : memory -> word t -> atom (word t) tag -> option memory;

  (* Contrary to concrete machine, here register access and update
     might fail, since they might correspond to kernel registers *)

  get_reg : registers -> reg t -> option (atom (word t) tag);
  upd_reg : registers -> reg t -> atom (word t) tag -> option registers;

  handler : MVec tag -> option (RVec tag)

}.

Class params_spec (ap : symbolic_params) := {

  mem_axioms :> PartMaps.axioms get_mem upd_mem;

  reg_axioms :> PartMaps.axioms get_reg upd_reg

}.

Context {ap : symbolic_params}.

Local Coercion Z_to_word : Z >-> word.
Open Scope word_scope.

Local Notation word := (word t).
Let atom := (atom word tag).
Local Notation "x .+1" := (add_word x (Z_to_word 1)) (at level 60).

Record state := State {
  mem : memory;
  regs : registers;
  pc : atom;
  internal : internal_state
}.

Record syscall := Syscall {
  address : word;
  sem : state -> option state
}.

(* CH: Q: Why is this defined as a Variable, while the tag and handler
   are defined i a type class? Can't this be moved to the
   symbolic_params class? *)
Variable table : list syscall.

Definition get_syscall (addr : word) : option syscall :=
  find (fun sc => address sc ==b addr) table.

Definition next_state (st : state) (mvec : MVec tag)
                      (k : RVec tag -> option state) : option state :=
  do rvec <- handler mvec;
    k rvec.

Definition next_state_reg_and_pc (st : state) (mvec : MVec tag) r x pc' : option state :=
  next_state st mvec (fun rvec =>
    do regs' <- upd_reg (regs st) r x@(tr rvec);
    Some (State (mem st) regs' pc'@(trpc rvec) (internal st))).

Definition next_state_reg (st : state) (mvec : MVec tag) r x : option state :=
  next_state_reg_and_pc st mvec r x (val (pc st).+1).

Definition next_state_pc (st : state) (mvec : MVec tag) x : option state :=
  next_state st mvec (fun rvec =>
    Some (State (mem st) (regs st) x@(trpc rvec) (internal st))).

Import Vector.VectorNotations.

Inductive step (st st' : state) : Prop :=
| step_nop : forall mem reg pc tpc i ti int,
             forall (ST : st = State mem reg pc@tpc int),
             forall (PC : get_mem mem pc = Some i@ti),
             forall (INST : decode_instr i = Some (Nop _)),
             let mvec := mkMVec NOP tpc ti [] in
             forall (NEXT : next_state_pc st mvec (pc.+1) = Some st'),
             step st st'
| step_const : forall mem reg pc tpc i ti n r old told int,
             forall (ST : st = State mem reg pc@tpc int),
             forall (PC : get_mem mem pc = Some i@ti),
             forall (INST : decode_instr i = Some (Const _ n r)),
             forall (OLD : get_reg reg r = Some old@told),
             let mvec := mkMVec CONST tpc ti [told] in
             forall (NEXT : next_state_reg st mvec r (imm_to_word n) = Some st'),
             step st st'
| step_mov : forall mem reg pc tpc i ti r1 w1 t1 r2 old told int,
             forall (ST : st = State mem reg pc@tpc int),
             forall (PC : get_mem mem pc = Some i@ti),
             forall (INST : decode_instr i = Some (Mov _ r1 r2)),
             forall (R1W : get_reg reg r1 = Some w1@t1),
             forall (OLD : get_reg reg r2 = Some old@told),
             let mvec := mkMVec MOV tpc ti [t1; told] in
             forall (NEXT : next_state_reg st mvec r2 w1 = Some st'),
             step st st'
| step_binop : forall mem reg pc tpc i ti op r1 r2 r3 w1 w2 t1 t2 old told int,
             forall (ST : st = State mem reg pc@tpc int),
             forall (PC : get_mem mem pc = Some i@ti),
             forall (INST : decode_instr i = Some (Binop _ op r1 r2 r3)),
             forall (R1W : get_reg reg r1 = Some w1@t1),
             forall (R2W : get_reg reg r2 = Some w2@t2),
             forall (OLD : get_reg reg r3 = Some old@told),
             let mvec := mkMVec (BINOP op) tpc ti [t1; t2; told] in
             forall (NEXT : next_state_reg st mvec r3 (binop_denote op w1 w2) =
                            Some st'),
             step st st'
| step_load : forall mem reg pc tpc i ti r1 r2 w1 w2 t1 t2 old told int,
              forall (ST : st = State mem reg pc@tpc int),
             forall (PC : get_mem mem pc = Some i@ti),
             forall (INST : decode_instr i = Some (Load _ r1 r2)),
             forall (R1W : get_reg reg r1 = Some w1@t1),
             forall (MEM1 : get_mem mem w1 = Some w2@t2),
             forall (OLD : get_reg reg r2 = Some old@told),
             let mvec := mkMVec LOAD tpc ti [t1; t2; told] in
             forall (NEXT : next_state_reg st mvec r2 w2 = Some st'),
             step st st'
| step_store : forall mem reg pc i r1 r2 w1 w2 w3 tpc ti t1 t2 t3 int,
               forall (ST : st = State mem reg pc@tpc int),
             forall (PC : get_mem mem pc = Some i@ti),
             forall (INST : decode_instr i = Some (Store _ r1 r2)),
             forall (R1W : get_reg reg r1 = Some w1@t1),
             forall (R2W : get_reg reg r2 = Some w2@t2),
             forall (OLD : get_mem mem w1 = Some w3@t3),
             let mvec := mkMVec STORE tpc ti [t1; t2; t3] in
             forall (NEXT :
               next_state st mvec (fun rvec =>
                 do mem' <- upd_mem mem w1 w2@(tr rvec);
                 Some (State mem' reg (pc.+1)@(trpc rvec) int)) = Some st'),
             step st st'
| step_jump : forall mem reg pc i r w tpc ti t1 int,
             forall (ST : st = State mem reg pc@tpc int),
             forall (PC : get_mem mem pc = Some i@ti),
             forall (INST : decode_instr i = Some (Jump _ r)),
             forall (RW : get_reg reg r = Some w@t1),
             let mvec := mkMVec JUMP tpc ti [t1] in
             forall (NEXT : next_state_pc st mvec w = Some st'),
             step st st'
| step_bnz : forall mem reg pc i r n w tpc ti t1 int,
             forall (ST : st = State mem reg pc@tpc int),
             forall (PC : get_mem mem pc = Some i@ti),
             forall (INST : decode_instr i = Some (Bnz _ r n)),
             forall (RW : get_reg reg r = Some w@t1),
             let mvec := mkMVec BNZ tpc ti [t1] in
             let pc' := add_word pc (if w ==b Z_to_word 0
                                     then Z_to_word 1 else imm_to_word n) in
             forall (NEXT : next_state_pc st mvec pc' = Some st'),
             step st st'
| step_jal : forall mem reg pc i r w tpc ti t1 old told int,
             forall (ST : st = State mem reg pc@tpc int),
             forall (PC : get_mem mem pc = Some i@ti),
             forall (INST : decode_instr i = Some (Jal _ r)),
             forall (RW : get_reg reg r = Some w@t1),
             forall (NOTCALL : get_syscall w = None),
             forall (OLD : get_reg reg ra = Some old@told),
             let mvec := mkMVec JAL tpc ti [t1; told] in
             forall (NEXT : next_state_reg_and_pc st mvec ra (pc.+1) w = Some st'),
             step st st'
| step_syscall : forall mem reg pc i r w sc tpc ti t1 old told rvec int,
                 forall (ST : st = State mem reg pc@tpc int),
                 forall (PC : get_mem mem pc = Some i@ti),
                 forall (INST : decode_instr i = Some (Jal _ r)),
                 forall (RW : get_reg reg r = Some w@t1),
                 forall (GETCALL : get_syscall w = Some sc),
                 forall (OLD : get_reg reg ra = Some old@told),
                 let mvec := mkMVec JAL tpc ti [t1; told] in
                 forall (ALLOWED : handler mvec = Some rvec),
                 forall (CALL : sem sc (State mem reg pc@tpc int) = Some st'),
                 step st st'.

End WithClasses.

End Symbolic.

Arguments Symbolic.state t {_}.
Arguments Symbolic.memory t {_}.
Arguments Symbolic.registers t {_}.
Arguments Symbolic.syscall t {_}.
Arguments Symbolic.tag t {_}.
Arguments Symbolic.internal_state t {_}.
