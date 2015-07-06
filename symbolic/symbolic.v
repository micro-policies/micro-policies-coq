Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.ssrnat Ssreflect.seq.
Require Import CoqUtils.hseq CoqUtils.word CoqUtils.partmap.

Require Import lib.utils lib.hseq_utils common.types.

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

Definition type_of_result (o : option tag_kind) :=
  odflt [eqType of unit] (option_map tag_type o).

Definition instr_tag (op : vopcode) :=
  match op with
  | SERVICE => entry_tag_type tty
  | _ => mem_tag_type tty
  end.

Record mvec (op : vopcode) : Type := MVec {
  tpc : tag_type P;
  ti  : instr_tag op;
  ts  : hseq tag_type (vinputs op)
}.

Lemma mvec_eq_inv op tpc tpc' ti ti' ts ts'
                  (p : @MVec op tpc ti ts = @MVec op tpc' ti' ts') :
  [/\ tpc = tpc', ti = ti' & ts = ts'].
Proof. by case: p. Qed.

Definition mvec' : Type := sigT mvec.
Definition MVec' (op : vopcode) (tpc : tag_type P) (ti : instr_tag op) (ts : hseq tag_type (vinputs op)) : mvec'
  := existT _ op (MVec tpc ti ts).

End WithTagTypes.

Arguments MVec  {_} _ _ _ _.
Arguments MVec' {_} _ _ _ _.

Open Scope bool_scope.

Section WithClasses.

Context (mt : machine_types)
        {ops : machine_ops mt}.

Class params := {
  ttypes :> tag_types;

  transfer : forall op : vopcode, mvec ttypes op -> option (mvec ttypes op);

  internal_state : eqType
}.

Context {sp : params}.

Open Scope word_scope.

Local Notation word := (mword mt).
Let atom := (atom word).
Local Notation "x .+1" := (x + 1).

Local Notation memory := {partmap word -> atom (tag_type ttypes M)}.
Local Notation registers := {partmap reg mt -> atom (tag_type ttypes R)}.

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

Definition syscall_table := {partmap mword mt -> syscall}.

Variable table : syscall_table.

Definition run_syscall (sc : syscall) (st : state) : option state :=
  match transfer (MVec SERVICE (taga (pc st)) (entry_tag sc) [hseq]) with
  | Some _ => sem sc st
  | None => None
  end.

Definition tag_loc tk :=
  match tk with
  | P => unit
  | R => reg mt
  | M => mword mt
  end.

Definition tag_get (tk : tag_kind) : tag_loc tk -> state -> option (tag_type ttypes tk) :=
  match tk with
    | P => fun _ s => Some (pct s)
    | R => fun r s => omap taga (getm (regs s) r)
    | M => fun p s => omap taga (getm (mem  s) p)
  end.

Definition tag_get_from (s : state) : forall tk, tag_loc tk -> option (tag_type ttypes tk) :=
  fun _ l => tag_get l s.

Definition tag_upd (tk : tag_kind) : tag_loc tk -> tag_type ttypes tk -> state -> option state :=
  match tk with
    | P => fun _ t s => Some (State (mem s) (regs s) (pcv s)@t (internal s))
    | R => fun r t s => do! regs' <- repm (regs s) r (fun rvt => vala rvt @ t);
                            Some (State (mem s) regs' (pc s) (internal s))
    | M => fun p t s => do! mem' <- repm (mem s) p (fun rvt => vala rvt @ t);
                            Some (State mem' (regs s) (pc s) (internal s))
  end.

(* Without the `Unset/Set Implicit Arguments` jiggery-pokery, `opL` and `lv`
   become implicit and I can't figure out how to undo that.  Similarly,
   functions that use an `mvec ttypes (opL lv)` argument treat the `lv` as
   implicit. *)
Unset Implicit Arguments.
Record lvec : Type := LVec {
  opL  : vopcode;
  tpcL : tag_type ttypes P;
  tiL  : instr_tag ttypes opL;
  tsL  : hseq tag_loc (vinputs opL)
}.

Definition get_lvec (st : state) (lv : lvec) : option (mvec ttypes (opL lv)) :=
  omap (MVec (opL lv) (tpcL lv) (tiL lv)) (hmapo (tag_get_from st) (tsL lv)).

Definition set_lvec (st : state) (lv : lvec) (mv : mvec ttypes (opL lv)) : option state :=
  let writeback_pc    := @tag_upd P tt (tpc mv) in
  let writeback_instr := match opL lv as opL return instr_tag ttypes opL -> _ with
                           | OP _    => @tag_upd M (pcv st)
                           | SERVICE => fun _ _ => None (* Or Some? *)
                         end (ti mv) in
  let writebacks_args := hhomogeneous (hzipwith (@tag_upd) (tsL lv) (ts mv))
  in foldr (@obind _ _) (Some st) [:: writeback_pc, writeback_instr & writebacks_args].

Definition next_state (st : state) (lv : lvec) : option state :=
  do! ivts <- hmapo (tag_get_from st) (tsL lv);
  do! ov   <- transfer (MVec (opL lv) (tpcL lv) (tiL lv) ivts);
  set_lvec st lv ov.
Set Implicit Arguments.

Definition next_state_pc (st : state) (lv : lvec) (pc' : word) : option state :=
  do! st' <- next_state st lv;
  Some (State (mem st') (regs st') pc'@(pct st') (internal st')).

Definition next_state_reg_and_pc (st : state) (lv : lvec)
                                 (r : reg mt) (x : word) (pc' : word) : option state :=
  do! st'   <- next_state_pc st lv pc';
  do! regs' <- repm (regs st') r (fun v => x@(taga v));
  Some (State (mem st') regs' pc'@(pct st') (internal st')).

Definition next_state_reg (st : state) (lv : lvec) (r : reg mt) (x : word) : option state :=
  next_state_reg_and_pc st lv r x (vala (pc st)).+1.

Inductive step (st st' : state) : Prop :=
| step_nop : forall mem reg pc tpc i ti extra
    (ST   : st = State mem reg pc@tpc extra)
    (PC   : mem pc = Some i@ti)
    (INST : decode_instr i = Some (Nop _)),
    let lv := LVec NOP tpc ti [hseq] in forall
    (NEXT : next_state_pc st lv (pc.+1) = Some st'),    step st st'
| step_const : forall mem reg pc tpc i ti n r extra
    (ST   : st = State mem reg pc@tpc extra)
    (PC   : mem pc = Some i@ti)
    (INST : decode_instr i = Some (Const n r)),
    let lv := LVec CONST tpc ti [hseq r] in forall
    (NEXT : next_state_reg st lv r (swcast n) = Some st'),   step st st'
| step_mov : forall mem reg pc tpc i ti r1 r2 w1 extra
    (ST   : st = State mem reg pc@tpc extra)
    (PC   : mem pc = Some i@ti)
    (INST : decode_instr i = Some (Mov r1 r2))
    (R1W  : omap vala (reg r1) = Some w1),
    let lv := LVec MOV tpc ti [hseq r1; r2] in forall
    (NEXT : next_state_reg st lv r2 w1 = Some st'),   step st st'
| step_binop : forall mem reg pc tpc i ti op r1 r2 r3 w1 w2 extra
    (ST   : st = State mem reg pc@tpc extra)
    (PC   : mem pc = Some i@ti)
    (INST : decode_instr i = Some (Binop op r1 r2 r3))
    (R1W  : omap vala (reg r1) = Some w1)
    (R2W  : omap vala (reg r2) = Some w2),
    let lv := LVec (BINOP op) tpc ti [hseq r1; r2; r3] in forall
    (NEXT : next_state_reg st lv r3 (binop_denote op w1 w2) = Some st'),
      step st st'
| step_load : forall mem reg pc tpc i ti r1 r2 w1 w2 extra
    (ST   : st = State mem reg pc@tpc extra)
    (PC   : mem pc = Some i@ti)
    (INST : decode_instr i = Some (Load r1 r2))
    (R1W  : omap vala (reg r1) = Some w1)
    (MEM1 : omap vala (mem w1) = Some w2),
    let lv := LVec LOAD tpc ti [hseq r1; w1; r2] in forall
    (NEXT : next_state_reg st lv r2 w2 = Some st'),    step st st'
| step_store : forall mem reg pc tpc i ti r1 r2 w1 w2 extra
    (ST   : st = State mem reg pc@tpc extra)
    (PC   : mem pc = Some i@ti)
    (INST : decode_instr i = Some (Store r1 r2))
    (R1W  : omap vala (reg r1) = Some w1)
    (R2W  : omap vala (reg r2) = Some w2),
    let lv := LVec STORE tpc ti [hseq r1; r2; w1] in forall
    (NEXT : (do! st'  <- next_state_pc st lv (pc.+1);
             let: State _ reg' pc' extra' := st' in
             do! mem' <- repm mem w1 (fun v => w2@(taga v));
             Some (State mem' reg' pc' extra')) = Some st'),  step st st'
| step_jump : forall mem reg pc tpc i ti r w extra
    (ST   : st = State mem reg pc@tpc extra)
    (PC   : mem pc = Some i@ti)
    (INST : decode_instr i = Some (Jump r))
    (RW   : omap vala (reg r) = Some w),
    let lv := LVec JUMP tpc ti [hseq r] in forall
    (NEXT : next_state_pc st lv w = Some st'),    step st st'
| step_bnz : forall mem reg pc tpc i ti r n w extra
    (ST   : st = State mem reg pc@tpc extra)
    (PC   : mem pc = Some i@ti)
    (INST : decode_instr i = Some (Bnz r n))
    (RW   : omap vala (reg r) = Some w),
    let lv := LVec BNZ tpc ti [hseq r] in
    let pc' := pc + if w == 0%w then 1%w else swcast n in forall
    (NEXT : next_state_pc st lv pc' = Some st'),     step st st'
| step_jal : forall mem reg pc tpc i ti r w extra
    (ST : st = State mem reg pc@tpc extra)
    (PC : mem pc = Some i@ti)
    (INST : decode_instr i = Some (Jal r))
    (RW : omap vala (reg r) = Some w),
    let lv := LVec JAL tpc ti [hseq r; ra] in forall
    (NEXT : next_state_reg_and_pc st lv ra (pc.+1) w = Some st'), step st st'
| step_syscall : forall mem reg pc sc tpc extra
    (ST : st = State mem reg pc@tpc extra)
    (PC : mem pc = None)
    (GETCALL : table pc = Some sc)
    (CALL : run_syscall sc st = Some st'), step st st'.

End WithClasses.

Notation memory mt s := {partmap mword mt -> atom (mword mt) (@tag_type (@ttypes s) M)}.
Notation registers mt s := {partmap reg mt -> atom (mword mt) (@tag_type (@ttypes s) R)}.

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
Arguments Symbolic.MVec  {tty} op _ _ _.
Arguments Symbolic.mvec' / tty.
Arguments Symbolic.MVec' / {tty} op _ _ _.
Arguments Symbolic.LVec  {mt sp} opL _ _ _.
