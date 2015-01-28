Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq ssrint.
Require Import ord word partmap.

Require Import lib.utils common.types.

Import DoNotation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Concrete.

Local Open Scope word_scope.

(* CH (old): Why aren't these Ts instantiated with (word t) right away?  Is
   there any other instantiation of this? If this is so general, why
   doesn't it replace the MVec and RVec in fault_handler_spec.v?  (we
   would need to distinguish between the type of tags and the type of
   opcodes for that) *)
(* CH (new): to me it seems we should just replace T by (word t) *)
Record MVec (T : Type) : Type := mkMVec {
  cop  : T;
  ctpc : T;
  cti  : T;
  ct1  : T;
  ct2  : T;
  ct3  : T
}.

Record RVec (T : Type) : Type := mkRVec {
  ctrpc : T;
  ctr   : T
}.

Definition rule T := (MVec T * RVec T)%type.
Definition rules T := seq (rule T).

Section WithClasses.

Context (mt : machine_types).
Context (ops : machine_ops mt).

Let MVec := MVec (mword mt).
Let RVec := RVec (mword mt).
Let rule := rule (mword mt).
Let rules := rules (mword mt).
Let atom := atom (mword mt) (mword mt).

(* If we were doing good modularization, these would be abstract! *)
Definition cache_line_addr : mword mt := 0%w.
(* BCP: Call it fault_handler_addr? *)
Definition fault_handler_start : mword mt := as_word 8.
Definition TNone   : mword mt := as_word 8.
Definition TKernel : mword mt := 0.

Context {spops : machine_ops_spec ops}.

Definition Mop : mword mt := (cache_line_addr + 0)%w.
Definition Mtpc : mword mt := (cache_line_addr + 1)%w.
Definition Mti : mword mt := (cache_line_addr + as_word 2)%w.
Definition Mt1 : mword mt := (cache_line_addr + as_word 3)%w.
Definition Mt2 : mword mt := (cache_line_addr + as_word 4)%w.
Definition Mt3 : mword mt := (cache_line_addr + as_word 5)%w.
Definition Mtrpc : mword mt := (cache_line_addr + as_word 6)%w.
Definition Mtr : mword mt := (cache_line_addr + as_word 7)%w.

Definition mvec_fields := [:: Mop; Mtpc; Mti; Mt1; Mt2; Mt3].
Definition rvec_fields := [:: Mtrpc; Mtr].
Definition mvec_and_rvec_fields := mvec_fields ++ rvec_fields.

Definition beq_mvec (mv1 mv2 : MVec) : bool :=
  let '(mkMVec op tpc ti t1 t2 t3) := mv1 in
  let '(mkMVec op' tpc' ti' t1' t2' t3') := mv2 in
  (op == op') && (tpc == tpc') && (ti == ti')
  && (t1 == t1') && (t2 == t2') && (t3 == t3').

Inductive mvec_part : Set :=
  | mvp_tpc : mvec_part
  | mvp_ti  : mvec_part
  | mvp_t1  : mvec_part
  | mvp_t2  : mvec_part
  | mvp_t3  : mvec_part.

Definition DCMask := mvec_part -> bool.

Record CTMask : Set := mkCTMask {
  ct_trpc : option mvec_part;
  ct_tr   : option mvec_part
}.

Record Mask : Set := {
  dc : DCMask; (* don't care *)
  ct : CTMask  (* copy through *)
}.

Definition Masks := bool -> opcode -> Mask.

Definition mask_dc (dcm : DCMask) (mv : MVec) : MVec :=
  let '(mkMVec op tpc ti t1 t2 t3) := mv in
  mkMVec op
    (if dcm mvp_tpc then TNone else tpc)
    (if dcm mvp_ti  then TNone else ti)
    (if dcm mvp_t1  then TNone else t1)
    (if dcm mvp_t2  then TNone else t2)
    (if dcm mvp_t3  then TNone else t3).

Definition copy_mvec_part (mv : MVec) (tag : mword mt)
    (x : option mvec_part) : mword mt :=
  match x with
  | Some mvp_tpc => ctpc mv
  | Some mvp_ti  => cti mv
  | Some mvp_t1  => ct1 mv
  | Some mvp_t2  => ct2 mv
  | Some mvp_t3  => ct3 mv
  | None         => tag
  end.

Definition copy (mv : MVec) (rv : RVec) (ctm : CTMask) : RVec :=
  mkRVec (copy_mvec_part mv (ctrpc rv) (ct_trpc ctm))
         (copy_mvec_part mv (ctr   rv) (ct_tr   ctm)).

Definition is_kernel_tag (tpc:mword mt) : bool := tpc == TKernel.

Definition cache_lookup (cache : rules)
    (masks : Masks) (mv : MVec) : option RVec :=
  do! op <- op_of_word (cop mv);
  let mask := masks (is_kernel_tag (ctpc mv)) op in
  let masked_mv := mask_dc (dc mask) mv in
  do! rv <- assoc_list_lookup cache (beq_mvec masked_mv);
  Some (copy mv rv (ct mask)).

Local Notation memory := {partmap mword mt -> atom}.
Local Notation registers := {partmap reg mt -> atom}.

Record state := mkState {
  mem   : memory;
  regs  : registers;
  cache : rules;
  pc    : atom;
  epc   : atom
}.

Definition pcv (s : state) := vala (pc s).
Definition pct (s : state) := taga (pc s).

Lemma state_eta (cst : state) :
  cst = mkState (mem cst)
                (regs cst)
                (cache cst)
                (pcv cst)@(pct cst)
                (epc cst).
Proof. by case: cst=> ? ? ? [? ?] ?. Qed.

(* Need to do this masking both on lookup, and on rule add, right?
   This is optional; the software could do it *)
Definition add_rule (cache : rules) (masks : Masks) (mem : memory) : option rules :=
  do! aop   <- mem Mop;
  do! atpc  <- mem Mtpc;
  do! ati   <- mem Mti;
  do! at1   <- mem Mt1;
  do! at2   <- mem Mt2;
  do! at3   <- mem Mt3;
  do! atrpc <- mem Mtrpc;
  do! atr   <- mem Mtr;
  do! op    <- op_of_word (vala aop);
  let dcm := dc (masks false op) in
  Some ((mask_dc dcm (mkMVec (vala aop) (vala atpc)
                             (vala ati) (vala at1) (vala at2) (vala at3)),
         mkRVec (vala atrpc) (vala atr)) :: cache).

Definition store_mvec (mem : memory) (mv : MVec) : memory :=
  unionm [partmap (Mop, (cop mv)@TKernel);
                  (Mtpc, (ctpc mv)@TKernel);
                  (Mti, (cti mv)@TKernel);
                  (Mt1, (ct1 mv)@TKernel);
                  (Mt2, (ct2 mv)@TKernel);
                  (Mt3, (ct3 mv)@TKernel)]
         mem.

Section ConcreteSection.

Variable masks : Masks.

Local Notation "x .+1" := (x + 1)%w.

(* The mvector is written at fixed locations in kernel memory where
   the fault handler can access them (using the same addresses as for
   add_rule: Mop, Mtpc, etc.) *)
Definition miss_state (st : state) (mvec : MVec) : state :=
  let mem' := store_mvec (mem st) mvec in
  mkState mem' (regs st) (cache st) fault_handler_start@TKernel (pc st).


(* The next functions build the next state by looking up on the cache,
   finding the appropriate tag values for the results and using those
   combined with its arguments (new register value and/or new pc value
   *)
(* TODO: find better name for these ... lookup? *)
(* BCP: check? *)

Definition next_state (st : state) (mvec : MVec)
                      (k : RVec -> option state) : option state :=
  let lookup := cache_lookup (cache st) masks mvec in
  match lookup with
  | Some rvec => k rvec
  | None => Some (miss_state st mvec)
  end.

Definition next_state_reg_and_pc (st : state) (mvec : MVec) (r : reg mt) x pc' : option state :=
  next_state st mvec (fun rvec =>
    do! reg' <- updm (regs st) r x@(ctr rvec);
    Some (mkState (mem st) reg' (cache st) pc'@(ctrpc rvec) (epc st))).

Definition next_state_reg (st : state) (mvec : MVec) r x : option state :=
  next_state_reg_and_pc st mvec r x (vala (pc st)).+1.

Definition next_state_pc (st : state) (mvec : MVec) x : option state :=
  next_state st mvec (fun rvec =>
    Some (mkState (mem st) (regs st) (cache st) x@(ctrpc rvec) (epc st))).

Inductive step (st st' : state) : Prop :=
| step_nop :
    forall mem reg cache pc epc tpc i ti,
    forall (ST : st = mkState mem reg cache pc@tpc epc),
    forall (PC : mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (Nop _)),
    let mvec := mkMVec (word_of_op NOP) tpc ti TNone TNone TNone in
    forall (NEXT : next_state_pc st mvec (pc.+1) = Some st'),
      step st st'
| step_const :
    forall mem reg cache pc epc n r tpc i ti old told,
    forall (ST : st = mkState mem reg cache pc@tpc epc),
    forall (PC : mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (Const n r)),
    forall (OLD : reg r = Some old@told),
    let mvec := mkMVec (word_of_op CONST) tpc ti told TNone TNone in
    forall (NEXT : next_state_reg st mvec r (swcast n) = Some st'),
      step st st'
| step_mov :
    forall mem reg cache pc epc r1 w1 r2 tpc i ti t1 old told,
    forall (ST : st = mkState mem reg cache pc@tpc epc),
    forall (PC : mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (Mov r1 r2)),
    forall (REG1 : reg r1 = Some w1@t1),
    forall (OLD : reg r2 = Some old@told),
    let mvec := mkMVec (word_of_op MOV) tpc ti t1 told TNone in
    forall (NEXT : next_state_reg st mvec r2 w1 = Some st'),
      step st st'
| step_binop :
    forall mem reg cache pc epc op r1 r2 r3 w1 w2 tpc i ti t1 t2 old told,
    forall (ST : st = mkState mem reg cache pc@tpc epc),
    forall (PC : mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (Binop op r1 r2 r3)),
    forall (REG1 : reg r1 = Some w1@t1),
    forall (REG2 : reg r2 = Some w2@t2),
    forall (OLD : reg r3 = Some old@told),
    let mvec := mkMVec (word_of_op (BINOP op)) tpc ti t1 t2 told in
    forall (NEXT : next_state_reg st mvec r3 (binop_denote op w1 w2) =
                   Some st'),
      step st st'
| step_load :
    forall mem reg cache pc epc r1 r2 w1 w2 tpc i ti t1 t2 old told,
    forall (ST : st = mkState mem reg cache pc@tpc epc),
    forall (PC : mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (Load r1 r2)),
    forall (REG1 : reg r1 = Some w1@t1),
    forall (M1 : mem w1 = Some w2@t2),
    forall (OLD : reg r2 = Some old@told),
    let mvec := mkMVec (word_of_op LOAD) tpc ti t1 t2 told in
    forall (NEXT : next_state_reg st mvec r2 w2 = Some st'),
      step st st'
| step_store :
    forall mem reg cache pc epc r1 r2 w1 w2 w3 tpc i ti t1 t2 t3,
    forall (ST : st = mkState mem reg cache pc@tpc epc),
    forall (PC : mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (Store r1 r2)),
    forall (REG1 : reg r1 = Some w1@t1),
    forall (REG2 : reg r2 = Some w2@t2),
    forall (M1 : mem w1 = Some w3@t3),
    let mvec := mkMVec (word_of_op STORE) tpc ti t1 t2 t3 in
    forall (NEXT :
      next_state st mvec (fun rvec =>
        do! mem' <- updm mem w1 w2@(ctr rvec);
        Some (mkState mem' reg cache (pc.+1)@(ctrpc rvec) epc)) = Some st'),
      step st st'
| step_jump :
    forall mem reg cache pc epc r w tpc i ti t1,
    forall (ST : st = mkState mem reg cache pc@tpc epc),
    forall (PC : mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (Jump r)),
    forall (REG : reg r = Some w@t1),
    let mvec := mkMVec (word_of_op JUMP) tpc ti t1 TNone TNone in
    forall (NEXT : next_state_pc st mvec w = Some st'),
      step st st'
| step_bnz :
    forall mem reg cache pc epc r n w tpc i ti t1,
    forall (ST : st = mkState mem reg cache pc@tpc epc),
    forall (PC : mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (Bnz r n)),
    forall (REG : reg r = Some w@t1),
    let mvec := mkMVec (word_of_op BNZ) tpc ti t1 TNone TNone in
    let pc' := pc + if w == 0 then 1 else swcast n in
    forall (NEXT : next_state_pc st mvec pc' = Some st'),
      step st st'
| step_jal :
    forall mem reg cache pc epc r w tpc i ti t1 old told,
    forall (ST : st = mkState mem reg cache pc@tpc epc),
    forall (PC : mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (Jal r)),
    forall (REG : reg r = Some w@t1),
    forall (OLD: reg ra = Some old@told),
    let mvec := mkMVec (word_of_op JAL) tpc ti t1 told TNone in
    forall (NEXT : next_state_reg_and_pc st mvec ra (pc.+1) w = Some st'),
      step st st'
| step_jumpepc :
    forall mem reg cache pc tpc w tepc i ti,
    forall (ST : st = mkState mem reg cache pc@tpc w@tepc),
    forall (PC : mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (JumpEpc _)),
    let mvec := mkMVec (word_of_op JUMPEPC) tpc ti tepc TNone TNone in
    forall (NEXT : next_state_pc st mvec w = Some st'),
      step st st'
| step_addrule :
    forall mem reg cache pc epc tpc i ti,
    forall (ST : st = mkState mem reg cache pc@tpc epc),
    forall (PC : mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (AddRule _)),
    let mvec :=
        mkMVec (word_of_op ADDRULE) tpc ti TNone TNone TNone in
    forall (NEXT :
      next_state st mvec (fun rvec =>
        do! cache' <- add_rule cache masks mem;
        Some (mkState mem reg cache' (pc.+1)@(ctrpc rvec) epc)) = Some st'),
      step st st'
| step_gettag :
    forall mem reg cache pc epc r1 r2 w tpc i ti t1 old told,
    forall (ST : st = mkState mem reg cache pc@tpc epc),
    forall (PC : mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (GetTag r1 r2)),
    forall (REG : reg r1 = Some w@t1),
    forall (OLD : reg r2 = Some old@told),
    let mvec := mkMVec (word_of_op GETTAG) tpc ti t1 told TNone in
    forall (NEXT : next_state_reg st mvec r2 t1 = Some st'),
      step st st'
| step_puttag :
    forall mem reg cache pc epc r1 r2 r3 w t tpc i ti t1 t2 old told,
    forall (ST : st = mkState mem reg cache pc@tpc epc),
    forall (PC : mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (PutTag r1 r2 r3)),
    forall (REG1 : reg r1 = Some w@t1),
    forall (REG2 : reg r2 = Some t@t2),
    forall (OLD: reg r3 = Some old@told),
    let mvec := mkMVec (word_of_op PUTTAG) tpc ti t1 t2 told in
    forall (NEXT :
      next_state st mvec (fun rvec =>
        do! reg' <- updm reg r3 w@t;
        Some (mkState mem reg' cache (pc.+1@(ctrpc rvec)) epc)) = Some st'),
      step st st'.

End ConcreteSection.

End WithClasses.

Notation memory mt := {partmap mword mt -> atom (mword mt) (mword mt)}.
Notation registers mt := {partmap reg mt -> atom (mword mt) (mword mt)}.

End Concrete.

Module Exports.

Import Concrete.
Require Import seq.

Definition mvec_eqb (T : eqType) (m1 m2 : MVec T) : bool :=
  [&& cop m1 == cop m2,
      ctpc m1 == ctpc m2,
      cti m1 == cti m2,
      ct1 m1 == ct1 m2 &
      ct2 m1 == ct2 m2] && (ct3 m1 == ct3 m2).

Lemma mvec_eqbP T : Equality.axiom (@mvec_eqb T).
Proof.
  move => m1 m2.
  case: m1 => *. case: m2 => *.
  apply (iffP andP); simpl.
  - by move => [/and5P [/eqP -> /eqP -> /eqP -> /eqP -> /eqP ->] /eqP ->].
  - move => [-> -> -> -> -> ->]. by rewrite !eqxx.
Qed.

Definition mvec_eqMixin T := EqMixin (@mvec_eqbP T).
Canonical mvec_eqType (T : eqType) :=
  Eval hnf in EqType (MVec T) (@mvec_eqMixin T).

Definition rvec_eqb (T : eqType) (r1 r2 : RVec T) : bool :=
  [&& ctrpc r1 == ctrpc r2 & ctr r1 == ctr r2].

Lemma rvec_eqbP T : Equality.axiom (@rvec_eqb T).
Proof.
  move => r1 r2.
  case: r1 => *. case: r2 => *.
  apply (iffP andP); simpl.
  - by move => [/eqP -> /eqP ->].
  - move => [-> ->]. by rewrite !eqxx.
Qed.

Definition rvec_eqMixin T := EqMixin (@rvec_eqbP T).
Canonical rvec_eqType (T : eqType) :=
  Eval hnf in EqType (RVec T) (rvec_eqMixin T).

Definition state_eqb mt : rel (state mt) :=
  [rel s1 s2 | [&& mem s1 == mem s2,
                   regs s1 == regs s2,
                   cache s1 == cache s2,
                   pc s1 == pc s2 &
                   epc s1 == epc s2] ].

Lemma state_eqbP mt : Equality.axiom (@state_eqb mt).
Proof.
  move => [? ? ? ? ?] [? ? ? ? ?].
  apply (iffP and5P); simpl.
  - by move => [/eqP -> /eqP -> /eqP -> /eqP -> /eqP ->].
  - by move => [-> -> -> -> ->].
Qed.

Definition state_eqMixin mt := EqMixin (@state_eqbP mt).
Canonical state_eqType mt := EqType (state mt) (@state_eqMixin mt).

End Exports.

Export Exports.

Arguments Concrete.state mt.
Arguments Concrete.mkState {_} _ _ _ _ _.
Arguments Concrete.TNone {mt}.
Arguments Concrete.TKernel {mt}.
