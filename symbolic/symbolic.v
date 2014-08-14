Require Import List Arith ZArith.
Require Import Coq.Bool.Bool.
Require Coq.Vectors.Vector.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Require Import lib.Integers lib.utils lib.partial_maps common.common.
Require Import lib.hlist.

Set Implicit Arguments.

Import DoNotation.
Import ListNotations.

Module Symbolic.

(* BCP/AAA: Should some of this be shared with the concrete machine? *)

(* CH: These could move to common.v?  But they would be useful only if
       we want to make the concrete machine dependently typed too; and
       we probably don't want to do that. *)

Inductive tag_kind : Type := R | M | P.

Definition inputs (op : opcode) : list tag_kind :=
  match op with
  | NOP     => []
  | CONST   => [R]
  | MOV     => [R;R]
  | BINOP _ => [R;R;R]
  | LOAD    => [R;M;R]
  | STORE   => [R;R;M]
  | JUMP    => [R]
  | BNZ     => [R]
  | JAL     => [R;R]
  | SERVICE => []
  (* the other opcodes are not used by the symbolic machine *)
  | JUMPEPC => [P]
  | ADDRULE => []
  | GETTAG  => [R;R]
  | PUTTAG  => [R;R;R]
  | HALT    => [] (* CH: in a way this is used by symbolic machine;
                         it just causes it to get stuck as it should *)
  end.

Definition outputs (op : opcode) : option tag_kind :=
  match op with
  | NOP     => None
  | CONST   => Some R
  | MOV     => Some R
  | BINOP _ => Some R
  | LOAD    => Some R
  | STORE   => Some M
  | JUMP    => None
  | BNZ     => None
  | JAL     => Some R
  | SERVICE => None
  (* the other opcodes are not used by the symbolic machine *)
  | JUMPEPC => None
  | ADDRULE => None
  | GETTAG  => Some R
  | PUTTAG  => None
  | HALT    => None
  end.

Section WithTagTypes.

Variable tag_type : tag_kind -> eqType.

Record IVec : Type := mkIVec {
  op  : opcode;
  tpc : tag_type P;
  ti  : tag_type M;
  ts  : hlist tag_type (inputs op)
}.

Definition type_of_result (o : option tag_kind) :=
  odflt [eqType of unit] (option_map tag_type o).

Record OVec (op : opcode) : Type := mkOVec {
  trpc : tag_type P;
  tr   : type_of_result (outputs op)
}.

End WithTagTypes.

Arguments mkIVec {_} _ _ _ _.

Open Scope bool_scope.
(* Open Scope Z_scope. *)

Section WithClasses.

Context (t : machine_types)
        {ops : machine_ops t}.

Import PartMaps.

Class params := {
  ttypes :> tag_kind -> eqType;

  transfer : forall (iv : IVec ttypes), option (OVec ttypes (op iv));

  internal_state : eqType
}.

Context {sp : params}.

Open Scope word_scope.

Local Notation word := (word t).
Let atom := (atom word).
Local Notation "x .+1" := (Word.add x Word.one).

Local Notation memory := (word_map t (atom (ttypes M))).
Local Notation registers := (reg_map t (atom (ttypes R))).

Record state := State {
  mem : memory;
  regs : registers;
  pc : atom (ttypes P);
  internal : internal_state
}.

(* CH: TODO: should make the entry_tags part of the state
   (for compartmentalization they need to be mutable) *)
Record syscall := Syscall {
  address : word;
  entry_tag : ttypes M;
  sem : state -> option state
}.

Variable table : list syscall.

Definition get_syscall (addr : word) : option syscall :=
  find (fun sc => address sc == addr) table.

Definition run_syscall (sc : syscall) (st : state) : option state :=
  match transfer (mkIVec SERVICE (common.tag (pc st)) (entry_tag sc) tt) with
  | Some _ => sem sc st
  | None => None
  end.

Definition next_state (st : state) (iv : IVec ttypes)
                      (k : OVec ttypes (op iv) -> option state) : option state :=
  do! ov <- transfer iv;
    k ov.

Definition next_state_reg_and_pc (st : state) (iv : @IVec ttypes)
  (r : reg t) (x : word) (pc' : word) : option state :=
  next_state st iv (fun ov =>
    match outputs (op iv) as o return (type_of_result _ o -> option state) with
      | Some R => fun tr' =>
          do! regs' <- upd (regs st) r x@tr';
          Some (State (mem st) regs' pc'@(trpc ov) (internal st))
      | _ => fun _ => None
    end (tr ov)).

Definition next_state_reg (st : state) (mvec : @IVec ttypes) r x : option state :=
  next_state_reg_and_pc st mvec r x (val (pc st)).+1.

Definition next_state_pc (st : state) (mvec : @IVec ttypes) x : option state :=
  next_state st mvec (fun ov =>
    Some (State (mem st) (regs st) x@(trpc ov) (internal st))).

Import HListNotations.

Inductive step (st st' : state) : Prop :=
| step_nop : forall mem reg pc tpc i ti extra
    (ST   : st = State mem reg pc@tpc extra)
    (PC   : get mem pc = Some i@ti)
    (INST : decode_instr i = Some (Nop _)),
    let mvec := mkIVec NOP tpc ti [] in forall
    (NEXT : next_state_pc st mvec (pc.+1) = Some st'),    step st st'
| step_const : forall mem reg pc tpc i ti n r old told extra
    (ST   : st = State mem reg pc@tpc extra)
    (PC   : get mem pc = Some i@ti)
    (INST : decode_instr i = Some (Const n r))
    (OLD  : get reg r = Some old@told),
    let mvec := mkIVec CONST tpc ti [told] in forall
    (NEXT : next_state_reg st mvec r (Word.casts n) = Some st'),   step st st'
| step_mov : forall mem reg pc tpc i ti r1 w1 t1 r2 old told extra
    (ST   : st = State mem reg pc@tpc extra)
    (PC   : get mem pc = Some i@ti)
    (INST : decode_instr i = Some (Mov r1 r2))
    (R1W  : get reg r1 = Some w1@t1)
    (OLD  : get reg r2 = Some old@told),
    let mvec := mkIVec MOV tpc ti [t1; told] in forall
    (NEXT : next_state_reg st mvec r2 w1 = Some st'),   step st st'
| step_binop : forall mem reg pc tpc i ti op r1 r2 r3 w1 w2 t1 t2 old told extra
    (ST   : st = State mem reg pc@tpc extra)
    (PC   : get mem pc = Some i@ti)
    (INST : decode_instr i = Some (Binop op r1 r2 r3))
    (R1W  : get reg r1 = Some w1@t1)
    (R2W  : get reg r2 = Some w2@t2)
    (OLD  : get reg r3 = Some old@told),
    let mvec := mkIVec (BINOP op) tpc ti [t1; t2; told] in forall
    (NEXT : next_state_reg st mvec r3 (binop_denote op w1 w2) = Some st'),
      step st st'
| step_load : forall mem reg pc tpc i ti r1 r2 w1 w2 t1 t2 old told extra
    (ST   : st = State mem reg pc@tpc extra)
    (PC   : get mem pc = Some i@ti)
    (INST : decode_instr i = Some (Load r1 r2))
    (R1W  : get reg r1 = Some w1@t1)
    (MEM1 : get mem w1 = Some w2@t2)
    (OLD  : get reg r2 = Some old@told),
    let mvec := mkIVec LOAD tpc ti [t1; t2; told] in forall
    (NEXT : next_state_reg st mvec r2 w2 = Some st'),    step st st'
| step_store : forall mem reg pc i r1 r2 w1 w2 tpc ti t1 t2 old told extra
    (ST   : st = State mem reg pc@tpc extra)
    (PC   : get mem pc = Some i@ti)
    (INST : decode_instr i = Some (Store r1 r2))
    (R1W  : get reg r1 = Some w1@t1)
    (R2W  : get reg r2 = Some w2@t2)
    (OLD  : get mem w1 = Some old@told),
    let mvec := mkIVec STORE tpc ti [t1; t2; told] in forall
    (NEXT : next_state st mvec (fun ov =>
                 do! mem' <- upd mem w1 w2@(tr ov);
                 Some (State mem' reg (pc.+1)@(trpc ov) extra)) = Some st'),
              step st st'
| step_jump : forall mem reg pc i r w tpc ti t1 extra
    (ST   : st = State mem reg pc@tpc extra)
    (PC   : get mem pc = Some i@ti)
    (INST : decode_instr i = Some (Jump r))
    (RW   : get reg r = Some w@t1),
    let mvec := mkIVec JUMP tpc ti [t1] in forall
    (NEXT : next_state_pc st mvec w = Some st'),    step st st'
| step_bnz : forall mem reg pc i r n w tpc ti t1 extra
    (ST   : st = State mem reg pc@tpc extra)
    (PC   : get mem pc = Some i@ti)
    (INST : decode_instr i = Some (Bnz r n))
    (RW   : get reg r = Some w@t1),
     let mvec := mkIVec BNZ tpc ti [t1] in
     let pc' := Word.add pc (if w == Word.zero
                             then Word.one else Word.casts n) in forall
    (NEXT : next_state_pc st mvec pc' = Some st'),     step st st'
| step_jal : forall mem reg pc i r w tpc ti t1 old told extra
    (ST : st = State mem reg pc@tpc extra)
    (PC : get mem pc = Some i@ti)
    (INST : decode_instr i = Some (Jal r))
    (RW : get reg r = Some w@t1)
    (OLD : get reg ra = Some old@told),
     let mvec := mkIVec JAL tpc ti [t1; told] in forall
    (NEXT : next_state_reg_and_pc st mvec ra (pc.+1) w = Some st'), step st st'
| step_syscall : forall mem reg pc sc tpc extra
    (ST : st = State mem reg pc@tpc extra)
    (PC : get mem pc = None)
    (GETCALL : get_syscall pc = Some sc)
    (CALL : run_syscall sc st = Some st'), step st st'.

End WithClasses.

Notation memory t s := (word_map t (atom (word t) (@ttypes s M))).
Notation registers t s := (reg_map t (atom (word t) (@ttypes s R))).

End Symbolic.

Module Exports.

Import Symbolic.

Definition state_eqb mt p : rel (@state mt p) :=
  [rel s1 s2 | [&& mem s1 == mem s2,
                   regs s1 == regs s2,
                   pc s1 == pc s2 &
                   internal s1 == internal s2 ] ].

Lemma state_eqbP mt p : Equality.axiom (@state_eqb mt p).
Proof.
  move => [? ? ? ?] [? ? ? ?].
  apply (iffP and4P); simpl.
  - by move => [/eqP -> /eqP -> /eqP -> /eqP ->].
  - by move => [-> -> -> ->].
Qed.

Definition state_eqMixin mt p := EqMixin (@state_eqbP mt p).
Canonical state_eqType mt p := Eval hnf in EqType _ (@state_eqMixin mt p).

End Exports.

Export Exports.

Arguments Symbolic.state t {_}.
Arguments Symbolic.State {_ _} _ _ _ _.
Arguments Symbolic.syscall t {_}.
Arguments Symbolic.mkIVec {tag_type} op _ _ _.
Arguments Symbolic.mkOVec {tag_type op} _ _.
