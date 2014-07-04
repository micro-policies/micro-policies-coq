Require Import List Arith ZArith Bool. Import ListNotations.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Require Import lib.utils lib.partial_maps common.common.

Import DoNotation.

Set Implicit Arguments.

Module Concrete.

Open Scope bool_scope.
Open Scope Z_scope.
Open Scope word_scope.

(* CH: Why aren't these Ts instantiated with (word t) right away?  Is
   there any other instantiation of this? If this is so general, why
   doesn't it replace the MVec and RVec in fault_handler_spec.v?  (we
   would need to distinguish between the type of tags and the type of
   opcodes for that) *)
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
Definition rules T := list (rule T).

Section WithClasses.

Context (t : machine_types).
Context (ops : machine_ops t).

Let MVec := MVec (word t).
Let RVec := RVec (word t).
Let rule := rule (word t).
Let rules := rules (word t).
Let atom := atom (word t) (word t).

(* If we were doing good modularization, these would be abstract! *)
Definition cache_line_addr : word t := Z_to_word 0.
(* BCP: Call it fault_handler_addr? *)
Definition fault_handler_start : word t := Z_to_word 8.
Definition TNone   : word t := Z_to_word 42.  (* Recognizable enough? *)
Definition TKernel : word t := Z_to_word 0.

Context {spops : machine_ops_spec ops}.

Lemma store_same_tag (cmem cmem' : word_map t _) addr addr' (w tg : word t) :
  (exists w, PartMaps.get cmem addr = Some w@tg) ->
  PartMaps.upd cmem addr' w@tg = Some cmem' ->
  exists w, PartMaps.get cmem' addr = Some w@tg.
Proof.
  move=> [w' GET] UPD.
  have [<-|/eqP neq_addr] := altP (addr' =P addr).
  - erewrite PartMaps.get_upd_eq; eauto.
    apply word_map_axioms.
  - erewrite PartMaps.get_upd_neq; eauto.
    apply word_map_axioms.
Qed.

Definition Mop : word t := add_word cache_line_addr (Z_to_word 0).
Definition Mtpc : word t := add_word cache_line_addr (Z_to_word 1).
Definition Mti : word t := add_word cache_line_addr (Z_to_word 2).
Definition Mt1 : word t := add_word cache_line_addr (Z_to_word 3).
Definition Mt2 : word t := add_word cache_line_addr (Z_to_word 4).
Definition Mt3 : word t := add_word cache_line_addr (Z_to_word 5).
Definition Mtrpc : word t := add_word cache_line_addr (Z_to_word 6).
Definition Mtr : word t := add_word cache_line_addr (Z_to_word 7).

Definition mvec_fields := [Mop; Mtpc; Mti; Mt1; Mt2; Mt3].
Definition rvec_fields := [Mtrpc; Mtr].
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

Definition copy_mvec_part (mv : MVec) (tag : word t)
    (x : option mvec_part) : word t :=
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

Definition is_kernel_tag (tpc:word t) : bool := tpc == TKernel.

Definition cache_lookup (cache : rules)
    (masks : Masks) (mv : MVec) : option RVec :=
  do! op <- word_to_op (cop mv);
  let mask := masks (is_kernel_tag (ctpc mv)) op in
  let masked_mv := mask_dc (dc mask) mv in
  do! rv <- assoc_list_lookup cache (beq_mvec masked_mv);
  Some (copy mv rv (ct mask)).

Local Notation memory := (word_map t atom).
Local Notation registers := (reg_tmap t atom).

Record state := mkState {
  mem   : memory;
  regs  : registers;
  cache : rules;
  pc    : atom;
  epc   : atom
}.

(* Need to do this masking both on lookup, and on rule add, right?
   This is optional; the software could do it *)
Definition add_rule (cache : rules) (masks : Masks) (mem : memory) : option rules :=
  do! aop   <- PartMaps.get mem Mop;
  do! atpc  <- PartMaps.get mem Mtpc;
  do! ati   <- PartMaps.get mem Mti;
  do! at1   <- PartMaps.get mem Mt1;
  do! at2   <- PartMaps.get mem Mt2;
  do! at3   <- PartMaps.get mem Mt3;
  do! atrpc <- PartMaps.get mem Mtrpc;
  do! atr   <- PartMaps.get mem Mtr;
  do! op    <- word_to_op (val aop);
  let dcm := dc (masks false op) in
  Some ((mask_dc dcm (mkMVec (val aop) (val atpc)
                             (val ati) (val at1) (val at2) (val at3)),
         mkRVec (val atrpc) (val atr)) :: cache).

Definition store_mvec (mem : memory) (mv : MVec) : option (memory) :=
  PartMaps.upd_list mem
                    [(Mop, (cop mv)@TKernel);
                     (Mtpc, (ctpc mv)@TKernel);
                     (Mti, (cti mv)@TKernel);
                     (Mt1, (ct1 mv)@TKernel);
                     (Mt2, (ct2 mv)@TKernel);
                     (Mt3, (ct3 mv)@TKernel)].

Section ConcreteSection.

Variable masks : Masks.

Local Notation "x .+1" := (add_word x (Z_to_word 1)).

(* The mvector is written at fixed locations in kernel memory where
   the fault handler can access them (using the same addresses as for
   add_rule: Mop, Mtpc, etc.) *)
Definition miss_state (st : state) (mvec : MVec) : option state :=
  match store_mvec (mem st) mvec with
  | Some mem' =>
    Some (mkState mem' (regs st) (cache st) fault_handler_start@TKernel (pc st))
  | None => None
  end.

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
  | None => miss_state st mvec
  end.

Definition next_state_reg_and_pc (st : state) (mvec : MVec) (r : reg t) x pc' : option state :=
  next_state st mvec (fun rvec =>
    let reg' := TotalMaps.upd (regs st) r x@(ctr rvec) in
    Some (mkState (mem st) reg' (cache st) pc'@(ctrpc rvec) (epc st))).

Definition next_state_reg (st : state) (mvec : MVec) r x : option state :=
  next_state_reg_and_pc st mvec r x (val (pc st)).+1.

Definition next_state_pc (st : state) (mvec : MVec) x : option state :=
  next_state st mvec (fun rvec =>
    Some (mkState (mem st) (regs st) (cache st) x@(ctrpc rvec) (epc st))).

Inductive step (st st' : state) : Prop :=
| step_nop :
    forall mem reg cache pc epc tpc i ti,
    forall (ST : st = mkState mem reg cache pc@tpc epc),
    forall (PC : PartMaps.get mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (Nop _)),
    let mvec := mkMVec (op_to_word NOP) tpc ti TNone TNone TNone in
    forall (NEXT : next_state_pc st mvec (pc.+1) = Some st'),
      step st st'
| step_const :
    forall mem reg cache pc epc n r tpc i ti old told,
    forall (ST : st = mkState mem reg cache pc@tpc epc),
    forall (PC : PartMaps.get mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (Const _ n r)),
    forall (OLD : TotalMaps.get reg r = old@told),
    let mvec := mkMVec (op_to_word CONST) tpc ti told TNone TNone in
    forall (NEXT : next_state_reg st mvec r (imm_to_word n) = Some st'),
      step st st'
| step_mov :
    forall mem reg cache pc epc r1 w1 r2 tpc i ti t1 old told,
    forall (ST : st = mkState mem reg cache pc@tpc epc),
    forall (PC : PartMaps.get mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (Mov _ r1 r2)),
    forall (REG1 : TotalMaps.get reg r1 = w1@t1),
    forall (OLD : TotalMaps.get reg r2 = old@told),
    let mvec := mkMVec (op_to_word MOV) tpc ti t1 told TNone in
    forall (NEXT : next_state_reg st mvec r2 w1 = Some st'),
      step st st'
| step_binop :
    forall mem reg cache pc epc op r1 r2 r3 w1 w2 tpc i ti t1 t2 old told,
    forall (ST : st = mkState mem reg cache pc@tpc epc),
    forall (PC : PartMaps.get mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (Binop _ op r1 r2 r3)),
    forall (REG1 : TotalMaps.get reg r1 = w1@t1),
    forall (REG2 : TotalMaps.get reg r2 = w2@t2),
    forall (OLD : TotalMaps.get reg r3 = old@told),
    let mvec := mkMVec (op_to_word (BINOP op)) tpc ti t1 t2 told in
    forall (NEXT : next_state_reg st mvec r3 (binop_denote op w1 w2) =
                   Some st'),
      step st st'
| step_load :
    forall mem reg cache pc epc r1 r2 w1 w2 tpc i ti t1 t2 old told,
    forall (ST : st = mkState mem reg cache pc@tpc epc),
    forall (PC : PartMaps.get mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (Load _ r1 r2)),
    forall (REG1 : TotalMaps.get reg r1 = w1@t1),
    forall (M1 : PartMaps.get mem w1 = Some w2@t2),
    forall (OLD : TotalMaps.get reg r2 = old@told),
    let mvec := mkMVec (op_to_word LOAD) tpc ti t1 t2 told in
    forall (NEXT : next_state_reg st mvec r2 w2 = Some st'),
      step st st'
| step_store :
    forall mem reg cache pc epc r1 r2 w1 w2 w3 tpc i ti t1 t2 t3,
    forall (ST : st = mkState mem reg cache pc@tpc epc),
    forall (PC : PartMaps.get mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (Store _ r1 r2)),
    forall (REG1 : TotalMaps.get reg r1 = w1@t1),
    forall (REG2 : TotalMaps.get reg r2 = w2@t2),
    forall (M1 : PartMaps.get mem w1 = Some w3@t3),
    let mvec := mkMVec (op_to_word STORE) tpc ti t1 t2 t3 in
    forall (NEXT :
      next_state st mvec (fun rvec =>
        do! mem' <- PartMaps.upd mem w1 w2@(ctr rvec);
        Some (mkState mem' reg cache (pc.+1)@(ctrpc rvec) epc)) = Some st'),
      step st st'
| step_jump :
    forall mem reg cache pc epc r w tpc i ti t1,
    forall (ST : st = mkState mem reg cache pc@tpc epc),
    forall (PC : PartMaps.get mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (Jump _ r)),
    forall (REG : TotalMaps.get reg r = w@t1),
    let mvec := mkMVec (op_to_word JUMP) tpc ti t1 TNone TNone in
    forall (NEXT : next_state_pc st mvec w = Some st'),
      step st st'
| step_bnz :
    forall mem reg cache pc epc r n w tpc i ti t1,
    forall (ST : st = mkState mem reg cache pc@tpc epc),
    forall (PC : PartMaps.get mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (Bnz _ r n)),
    forall (REG : TotalMaps.get reg r = w@t1),
    let mvec := mkMVec (op_to_word BNZ) tpc ti t1 TNone TNone in
    let pc' := pc + if w == Z_to_word 0 then Z_to_word 1 else imm_to_word n in
    forall (NEXT : next_state_pc st mvec pc' = Some st'),
      step st st'
| step_jal :
    forall mem reg cache pc epc r w tpc i ti t1 old told,
    forall (ST : st = mkState mem reg cache pc@tpc epc),
    forall (PC : PartMaps.get mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (Jal _ r)),
    forall (REG : TotalMaps.get reg r = w@t1),
    forall (OLD: TotalMaps.get reg ra = old@told),
    let mvec := mkMVec (op_to_word JAL) tpc ti t1 told TNone in
    forall (NEXT : next_state_reg_and_pc st mvec ra (pc.+1) w = Some st'),
      step st st'
| step_jumpepc :
    forall mem reg cache pc tpc w tepc i ti,
    forall (ST : st = mkState mem reg cache pc@tpc w@tepc),
    forall (PC : PartMaps.get mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (JumpEpc _)),
    let mvec := mkMVec (op_to_word JUMPEPC) tpc ti tepc TNone TNone in
    forall (NEXT : next_state_pc st mvec w = Some st'),
      step st st'
| step_addrule :
    forall mem reg cache pc epc tpc i ti,
    forall (ST : st = mkState mem reg cache pc@tpc epc),
    forall (PC : PartMaps.get mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (AddRule _)),
    let mvec :=
        mkMVec (op_to_word ADDRULE) tpc ti TNone TNone TNone in
    forall (NEXT :
      next_state st mvec (fun rvec =>
        do! cache' <- add_rule cache masks mem;
        Some (mkState mem reg cache' (pc.+1)@(ctrpc rvec) epc)) = Some st'),
      step st st'
| step_gettag :
    forall mem reg cache pc epc r1 r2 w tpc i ti t1 old told,
    forall (ST : st = mkState mem reg cache pc@tpc epc),
    forall (PC : PartMaps.get mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (GetTag _ r1 r2)),
    forall (REG : TotalMaps.get reg r1 = w@t1),
    forall (OLD : TotalMaps.get reg r2 = old@told),
    let mvec := mkMVec (op_to_word GETTAG) tpc ti t1 told TNone in
    forall (NEXT : next_state_reg st mvec r2 t1 = Some st'),
      step st st'
| step_puttag :
    forall mem reg cache pc epc r1 r2 r3 w t tpc i ti t1 t2 old told,
    forall (ST : st = mkState mem reg cache pc@tpc epc),
    forall (PC : PartMaps.get mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (PutTag _ r1 r2 r3)),
    forall (REG1 : TotalMaps.get reg r1 = w@t1),
    forall (REG2 : TotalMaps.get reg r2 = t@t2),
    forall (OLD: TotalMaps.get reg r3 = old@told),
    let mvec := mkMVec (op_to_word PUTTAG) tpc ti t1 t2 told in
    forall (NEXT :
      next_state st mvec (fun rvec =>
        let reg' := TotalMaps.upd reg r3 w@t in
        Some (mkState mem reg' cache (pc.+1@(ctrpc rvec)) epc)) = Some st'),
      step st st'.

End ConcreteSection.

End WithClasses.

Notation memory t := (word_map t (atom (word t) (word t))).
Notation registers t := (reg_tmap t (atom (word t) (word t))).

End Concrete.

Arguments Concrete.state t.
Arguments Concrete.mkState {_} _ _ _ _ _.
Arguments Concrete.TNone {t _}.
Arguments Concrete.TKernel {t _}.
