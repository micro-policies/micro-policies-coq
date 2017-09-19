From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From CoqUtils Require Import hseq word fmap.

Require Import lib.utils common.types.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import DoNotation.

Module Symbolic.

(* BCP/AAA: Should some of this be shared with the concrete machine? *)

(* CH: These could move to types.v?  But they would be useful only if
       we want to make the concrete machine dependently typed too; and
       we probably don't want to do that. *)

Inductive tag_kind : Type := R | M | P.

Module Import TagKindEq.
Definition tag_kind_eq (tk1 tk2 : tag_kind) : bool :=
  match tk1, tk2 with
  | R, R | M, M | P, P => true | _, _ => false
  end.

Lemma tag_kind_eqP : Equality.axiom tag_kind_eq.
Proof. by do !case; constructor. Qed.

Definition tag_kind_eqMixin := EqMixin tag_kind_eqP.
Canonical tag_kind_eqType := Eval hnf in EqType tag_kind tag_kind_eqMixin.
End TagKindEq.

Definition inputs (op : opcode) : seq tag_kind :=
  match op with
  | NOP     => [:: ]
  | CONST   => [:: R]
  | MOV     => [:: R;R]
  | BINOP _ => [:: R;R;R]
  | LOAD    => [:: R;M;R]
  | STORE   => [:: R;R;M]
  | JUMP    => [:: R]
  | BNZ     => [:: R]
  | JAL     => [:: R;R]
  (* the other opcodes are not used by the symbolic machine *)
  | JUMPEPC => [:: P]
  | ADDRULE => [::]
  | GETTAG  => [:: R;R]
  | PUTTAG  => [:: R;R;R]
  | HALT    => [::] (* CH: in a way this is used by symbolic machine;
                           it just causes it to get stuck as it should *)
  end.

(* Returns true iff an opcode can only be executed by the monitor *)
Definition privileged_op (op : vopcode) : bool :=
  match op with
  | JUMPEPC
  | ADDRULE
  | GETTAG
  | PUTTAG => true
  | _ => false
  end.

Definition vinputs (vop : vopcode) : seq tag_kind :=
  match vop with
  | OP op => inputs op
  | SERVICE => [::]
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
  (* the other opcodes are not used by the symbolic machine *)
  | JUMPEPC => None
  | ADDRULE => None
  | GETTAG  => Some R
  | PUTTAG  => None
  | HALT    => None
  end.

Section WithTagTypes.

Structure tag_types := {
  pc_tag_type : eqType;
  reg_tag_type : eqType;
  mem_tag_type : eqType;
  entry_tag_type : eqType
}.

Variable tty : tag_types.

Definition tag_type tk :=
  match tk with
  | P => pc_tag_type tty
  | R => reg_tag_type tty
  | M => mem_tag_type tty
  end.

Definition instr_tag (op : vopcode) :=
  match op with
  | SERVICE => entry_tag_type tty
  | _ => mem_tag_type tty
  end.

Record ivec : Type := IVec {
  op  : vopcode;
  tpc : tag_type P;
  ti  : instr_tag op;
  ts  : hseq tag_type (vinputs op)
}.

Lemma ivec_eq_inv op op' tpc tpc' ti ti' ts ts'
                  (p : @IVec op tpc ti ts = @IVec op' tpc' ti' ts') :
  [/\ op = op', tpc = tpc',
      Tagged instr_tag ti = Tagged instr_tag ti' &
      Tagged (hseq tag_type \o vinputs) ts = existT _ op' ts'].
Proof. inversion p. by constructor. Qed.

Definition type_of_result (o : option tag_kind) :=
  odflt [eqType of unit] (option_map tag_type o).

Record ovec (op : opcode) : Type := OVec {
  trpc : tag_type P;
  tr   : type_of_result (outputs op)
}.

Definition vovec (vop : vopcode) : Type :=
  match vop with
  | OP op => ovec op
  | SERVICE => unit
  end.

End WithTagTypes.

Arguments IVec {_} _ _ _ _.

Open Scope bool_scope.

Section WithClasses.

Context (mt : machine_types)
        {ops : machine_ops mt}.

Class params := {
  ttypes :> tag_types;

  transfer : forall (iv : ivec ttypes), option (vovec ttypes (op iv));

  internal_state : eqType
}.

Context {sp : params}.

Open Scope word_scope.

Local Notation word := (mword mt).
Let atom := (atom word).
Local Notation "x .+1" := (x + 1).

Local Notation memory := {fmap word -> atom (tag_type ttypes M)}.
Local Notation registers := {fmap reg mt -> atom (tag_type ttypes R)}.

Record state := State {
  mem : memory;
  regs : registers;
  pc : atom (tag_type ttypes P);
  internal : internal_state
}.

Definition pcv (s : state) := vala (pc s).
Definition pct (s : state) := taga (pc s).

Lemma state_eta st :
  st = State (mem st) (regs st) (pcv st)@(pct st) (internal st).
Proof. by case: st=> ? ? [? ?] ?. Qed.

(* CH: TODO: should make the entry_tags part of the state
   (for compartmentalization they need to be mutable) *)
Record syscall := Syscall {
  entry_tag : entry_tag_type ttypes;
  sem : state -> option state
}.

Definition syscall_table := {fmap mword mt -> syscall}.

Variable table : syscall_table.

Definition run_syscall (sc : syscall) (st : state) : option state :=
  match transfer (IVec SERVICE (taga (pc st)) (entry_tag sc) [hseq]) with
  | Some _ => sem sc st
  | None => None
  end.

Definition next_state (st : state) (iv : ivec ttypes)
                      (k : vovec ttypes (op iv) -> option state) : option state :=
  do! ov <- transfer iv;
    k ov.

Definition next_state_reg_and_pc (st : state) (iv : @ivec ttypes)
  (r : reg mt) (x : word) (pc' : word) : option state :=
  next_state st (
    match op iv as o return vovec _ o -> option state with
    | OP op => fun ov =>
      match outputs op as o return (type_of_result _ o -> option state) with
        | Some R => fun tr' =>
            do! regs' <- updm (regs st) r x@tr';
            Some (State (mem st) regs' pc'@(trpc ov) (internal st))
        | _ => fun _ => None
      end (tr ov)
    | SERVICE => fun _ => None
    end
  ).

Definition next_state_reg (st : state) (mvec : @ivec ttypes) r x : option state :=
  next_state_reg_and_pc st mvec r x (vala (pc st)).+1.

Definition next_state_pc (st : state) (iv : @ivec ttypes)
  (x : word) : option state :=
  next_state st (
    match op iv as o return vovec _ o -> option state with
    | OP op => fun ov =>
                 Some (State (mem st) (regs st) x@(trpc ov) (internal st))
    | SERVICE => fun _ => None
    end
  ).

Inductive step (st st' : state) : Prop :=
| step_nop : forall mem reg pc tpc i ti extra
    (ST   : st = State mem reg pc@tpc extra)
    (PC   : mem pc = Some i@ti)
    (INST : decode_instr i = Some (Nop _)),
    let mvec := IVec NOP tpc ti [hseq] in forall
    (NEXT : next_state_pc st mvec (pc.+1) = Some st'),    step st st'
| step_const : forall mem reg pc tpc i ti n r old (told : tag_type ttypes R) extra
    (ST   : st = State mem reg pc@tpc extra)
    (PC   : mem pc = Some i@ti)
    (INST : decode_instr i = Some (Const n r))
    (OLD  : reg r = Some old@told),
    let mvec := IVec CONST tpc ti [hseq told] in forall
    (NEXT : next_state_reg st mvec r (swcast n) = Some st'),   step st st'
| step_mov : forall mem reg pc tpc i ti r1 w1 t1 r2 old told extra
    (ST   : st = State mem reg pc@tpc extra)
    (PC   : mem pc = Some i@ti)
    (INST : decode_instr i = Some (Mov r1 r2))
    (R1W  : reg r1 = Some w1@t1)
    (OLD  : reg r2 = Some old@told),
    let mvec := IVec MOV tpc ti [hseq t1; told] in forall
    (NEXT : next_state_reg st mvec r2 w1 = Some st'),   step st st'
| step_binop : forall mem reg pc tpc i ti op r1 r2 r3 w1 w2 t1 t2 old told extra
    (ST   : st = State mem reg pc@tpc extra)
    (PC   : mem pc = Some i@ti)
    (INST : decode_instr i = Some (Binop op r1 r2 r3))
    (R1W  : reg r1 = Some w1@t1)
    (R2W  : reg r2 = Some w2@t2)
    (OLD  : reg r3 = Some old@told),
    let mvec := IVec (BINOP op) tpc ti [hseq t1; t2; told] in forall
    (NEXT : next_state_reg st mvec r3 (binop_denote op w1 w2) = Some st'),
      step st st'
| step_load : forall mem reg pc tpc i ti r1 r2 w1 w2 t1 t2 old told extra
    (ST   : st = State mem reg pc@tpc extra)
    (PC   : mem pc = Some i@ti)
    (INST : decode_instr i = Some (Load r1 r2))
    (R1W  : reg r1 = Some w1@t1)
    (MEM1 : mem w1 = Some w2@t2)
    (OLD  : reg r2 = Some old@told),
    let mvec := IVec LOAD tpc ti [hseq t1; t2; told] in forall
    (NEXT : next_state_reg st mvec r2 w2 = Some st'),    step st st'
| step_store : forall mem reg pc i r1 r2 w1 w2 tpc ti t1 t2 old told extra
    (ST   : st = State mem reg pc@tpc extra)
    (PC   : mem pc = Some i@ti)
    (INST : decode_instr i = Some (Store r1 r2))
    (R1W  : reg r1 = Some w1@t1)
    (R2W  : reg r2 = Some w2@t2)
    (OLD  : mem w1 = Some old@told),
    let mvec := IVec STORE tpc ti [hseq t1; t2; told] in forall
    (NEXT : @next_state st mvec (fun ov =>
                 do! mem' <- updm mem w1 w2@(tr ov);
                 Some (State mem' reg (pc.+1)@(trpc ov) extra)) = Some st'),
              step st st'
| step_jump : forall mem reg pc i r w tpc ti t1 extra
    (ST   : st = State mem reg pc@tpc extra)
    (PC   : mem pc = Some i@ti)
    (INST : decode_instr i = Some (Jump r))
    (RW   : reg r = Some w@t1),
    let mvec := IVec JUMP tpc ti [hseq t1] in forall
    (NEXT : next_state_pc st mvec w = Some st'),    step st st'
| step_bnz : forall mem reg pc i r n w tpc ti t1 extra
    (ST   : st = State mem reg pc@tpc extra)
    (PC   : mem pc = Some i@ti)
    (INST : decode_instr i = Some (Bnz r n))
    (RW   : reg r = Some w@t1),
     let mvec := IVec BNZ tpc ti [hseq t1] in
     let pc' := pc + (if w == 0%w
                      then 1%w else swcast n) in forall
    (NEXT : next_state_pc st mvec pc' = Some st'),     step st st'
| step_jal : forall mem reg pc i r w tpc ti t1 old told extra
    (ST : st = State mem reg pc@tpc extra)
    (PC : mem pc = Some i@ti)
    (INST : decode_instr i = Some (Jal r))
    (RW : reg r = Some w@t1)
    (OLD : reg ra = Some old@told),
     let mvec := IVec JAL tpc ti [hseq t1; told] in forall
    (NEXT : next_state_reg_and_pc st mvec ra (pc.+1) w = Some st'), step st st'
| step_syscall : forall mem reg pc sc tpc extra
    (ST : st = State mem reg pc@tpc extra)
    (PC : mem pc = None)
    (GETCALL : table pc = Some sc)
    (CALL : run_syscall sc st = Some st'), step st st'.

End WithClasses.

Notation memory mt s := {fmap mword mt -> atom (mword mt) (@tag_type (@ttypes s) M)}.
Notation registers mt s := {fmap reg mt -> atom (mword mt) (@tag_type (@ttypes s) R)}.

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

Export TagKindEq.

End Exports.

Export Exports.

Arguments Symbolic.state mt {_}.
Arguments Symbolic.State {_ _} _ _ _ _.
Arguments Symbolic.syscall mt {_}.
Arguments Symbolic.syscall_table mt {_}.
Arguments Symbolic.IVec {tty} op _ _ _.
Arguments Symbolic.OVec {tty op} _ _.
