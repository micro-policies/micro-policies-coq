Require Import List Arith ZArith.
Require Import Coq.Bool.Bool.
Require Coq.Vectors.Vector.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Require Import lib.utils lib.partial_maps common.common.

Set Implicit Arguments.

Import DoNotation.
Import ListNotations.

Module Symbolic.

(* BCP/AAA: Should some of this be shared with the concrete machine? *)
Definition nfields (op : opcode) : option (nat * nat) :=
  match op with
  | NOP => Some (0, 0)
  | CONST => Some (1, 1)
  | MOV => Some (2, 1)
  | BINOP _ => Some (3, 1)
  | LOAD => Some (3, 1)
  | STORE => Some (3, 1)
  | JUMP => Some (1, 0)
  | BNZ => Some (1, 0)
  | JAL => Some (2, 1)
  | SERVICE => Some (0, 0)
  | JUMPEPC | ADDRULE | GETTAG | PUTTAG | HALT => None
  end.

Definition mvec_operands T (fs : option (nat * nat)) : Type :=
  match fs with
  | Some fs => Vector.t T (fst fs)
  | None => Empty_set
  end.

Record MVec T : Type := mkMVec {
  op  : opcode;
  tpc : T;
  ti  : T;
  ts  : mvec_operands T (nfields op)
}.

Record RVec T : Type := mkRVec {
  trpc : T;
  tr   : T
}.

Open Scope bool_scope.
(* Open Scope Z_scope. *)

Section WithClasses.

Context {t : machine_types}
        {ops : machine_ops t}.

Import PartMaps.

Class symbolic_params := {
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
  (* BCP: One worry that I have about this is that, in some policies,
     it may be convenient to do things like writing a rule that copies
     the tag from the current instruction to the next PC.  If we make
     these type distinctions, such rules would have to be disallowed,
     no? *)
  (* CH: The symbolic handler has to be well-typed, so if the tag
     types are instantiated differently, the error you describe would
     be caught by the (Coq) type checker. It would be allowed if some
     of the tag types are instantiated to the same type though.  If
     all tag types are instantiated with the same type we would
     basically get the current behavior. *)
  tag : eqType;

  handler : MVec tag -> option (RVec tag);

  internal_state : Type;

  memory : Type;
  sm :> partial_map memory (word t) (atom (word t) tag);

  registers : Type;
  sr :> partial_map registers (reg t) (atom (word t) tag)
}.

Context {sp : symbolic_params}.

Open Scope word_scope.

Local Notation word := (word t).
Let atom := (atom word tag).
Local Notation "x .+1" := (add_word x (Z_to_word 1)).

Record state := State {
  mem : memory;
  regs : registers;
  pc : atom;
  internal : internal_state
}.

Record syscall := Syscall {
  address : word;
  entry_tag : tag;
  sem : state -> option state
}.

Variable table : list syscall.

Definition get_syscall (addr : word) : option syscall :=
  find (fun sc => address sc == addr) table.

Definition run_syscall (sc : syscall) (st : state) : option state :=
  match handler (mkMVec SERVICE (common.tag (pc st)) (entry_tag sc) (Vector.nil _)) with
  | Some _ => sem sc st
  | None => None
  end.

Definition next_state (st : state) (mvec : MVec tag)
                      (k : RVec tag -> option state) : option state :=
  do! rvec <- handler mvec;
    k rvec.

Definition next_state_reg_and_pc (st : state) (mvec : MVec tag) r x pc'
    : option state :=
  next_state st mvec (fun rvec =>
    do! regs' <- upd (regs st) r x@(tr rvec);
    Some (State (mem st) regs' pc'@(trpc rvec) (internal st))).

Definition next_state_reg (st : state) (mvec : MVec tag) r x : option state :=
  next_state_reg_and_pc st mvec r x (val (pc st)).+1.

Definition next_state_pc (st : state) (mvec : MVec tag) x : option state :=
  next_state st mvec (fun rvec =>
    Some (State (mem st) (regs st) x@(trpc rvec) (internal st))).

Import Vector.VectorNotations.

Inductive step (st st' : state) : Prop :=
| step_nop : forall mem reg pc tpc i ti int
    (ST   : st = State mem reg pc@tpc int)
    (PC   : get mem pc = Some i@ti)
    (INST : decode_instr i = Some (Nop _)),
    let mvec := mkMVec NOP tpc ti [] in forall
    (NEXT : next_state_pc st mvec (pc.+1) = Some st'),    step st st'
| step_const : forall mem reg pc tpc i ti n r old told int
    (ST   : st = State mem reg pc@tpc int)
    (PC   : get mem pc = Some i@ti)
    (INST : decode_instr i = Some (Const _ n r))
    (OLD  : get reg r = Some old@told),
    let mvec := mkMVec CONST tpc ti [told] in forall
    (NEXT : next_state_reg st mvec r (imm_to_word n) = Some st'),   step st st'
| step_mov : forall mem reg pc tpc i ti r1 w1 t1 r2 old told int
    (ST   : st = State mem reg pc@tpc int)
    (PC   : get mem pc = Some i@ti)
    (INST : decode_instr i = Some (Mov _ r1 r2))
    (R1W  : get reg r1 = Some w1@t1)
    (OLD  : get reg r2 = Some old@told),
    let mvec := mkMVec MOV tpc ti [t1; told] in forall
    (NEXT : next_state_reg st mvec r2 w1 = Some st'),   step st st'
| step_binop : forall mem reg pc tpc i ti op r1 r2 r3 w1 w2 t1 t2 old told int
    (ST   : st = State mem reg pc@tpc int)
    (PC   : get mem pc = Some i@ti)
    (INST : decode_instr i = Some (Binop _ op r1 r2 r3))
    (R1W  : get reg r1 = Some w1@t1)
    (R2W  : get reg r2 = Some w2@t2)
    (OLD  : get reg r3 = Some old@told),
    let mvec := mkMVec (BINOP op) tpc ti [t1; t2; told] in forall
    (NEXT : next_state_reg st mvec r3 (binop_denote op w1 w2) = Some st'),
      step st st'
| step_load : forall mem reg pc tpc i ti r1 r2 w1 w2 t1 t2 old told int
    (ST   : st = State mem reg pc@tpc int)
    (PC   : get mem pc = Some i@ti)
    (INST : decode_instr i = Some (Load _ r1 r2))
    (R1W  : get reg r1 = Some w1@t1)
    (MEM1 : get mem w1 = Some w2@t2)
    (OLD  : get reg r2 = Some old@told),
    let mvec := mkMVec LOAD tpc ti [t1; t2; told] in forall
    (NEXT : next_state_reg st mvec r2 w2 = Some st'),    step st st'
| step_store : forall mem reg pc i r1 r2 w1 w2 w3 tpc ti t1 t2 t3 int
    (ST   : st = State mem reg pc@tpc int)
    (PC   : get mem pc = Some i@ti)
    (INST : decode_instr i = Some (Store _ r1 r2))
    (R1W  : get reg r1 = Some w1@t1)
    (R2W  : get reg r2 = Some w2@t2)
    (OLD  : get mem w1 = Some w3@t3),
    let mvec := mkMVec STORE tpc ti [t1; t2; t3] in forall
    (NEXT : next_state st mvec (fun rvec =>
                 do! mem' <- upd mem w1 w2@(tr rvec);
                 Some (State mem' reg (pc.+1)@(trpc rvec) int)) = Some st'),
              step st st'
| step_jump : forall mem reg pc i r w tpc ti t1 int
    (ST   : st = State mem reg pc@tpc int)
    (PC   : get mem pc = Some i@ti)
    (INST : decode_instr i = Some (Jump _ r))
    (RW   : get reg r = Some w@t1),
    let mvec := mkMVec JUMP tpc ti [t1] in forall
    (NEXT : next_state_pc st mvec w = Some st'),    step st st'
| step_bnz : forall mem reg pc i r n w tpc ti t1 int
    (ST   : st = State mem reg pc@tpc int)
    (PC   : get mem pc = Some i@ti)
    (INST : decode_instr i = Some (Bnz _ r n))
    (RW   : get reg r = Some w@t1),
     let mvec := mkMVec BNZ tpc ti [t1] in
     let pc' := add_word pc (if w == Z_to_word 0
                             then Z_to_word 1 else imm_to_word n) in forall
    (NEXT : next_state_pc st mvec pc' = Some st'),     step st st'
| step_jal : forall mem reg pc i r w tpc ti t1 old told int
    (ST : st = State mem reg pc@tpc int)
    (PC : get mem pc = Some i@ti)
    (INST : decode_instr i = Some (Jal _ r))
    (RW : get reg r = Some w@t1)
    (OLD : get reg ra = Some old@told),
     let mvec := mkMVec JAL tpc ti [t1; told] in forall
    (NEXT : next_state_reg_and_pc st mvec ra (pc.+1) w = Some st'), step st st'
| step_syscall : forall mem reg pc sc tpc int
    (ST : st = State mem reg pc@tpc int)
    (PC : get mem pc = None)
    (GETCALL : get_syscall pc = Some sc)
    (CALL : run_syscall sc st = Some st'), step st st'.

End WithClasses.

End Symbolic.

Arguments Symbolic.state t {_}.
Arguments Symbolic.memory t {_}.
Arguments Symbolic.registers t {_}.
Arguments Symbolic.syscall t {_}.
Arguments Symbolic.tag t {_}.
Arguments Symbolic.internal_state t {_}.
Arguments Symbolic.mkMVec {T} op _ _ _.
