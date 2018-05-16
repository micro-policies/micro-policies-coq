From mathcomp Require Import
  ssreflect ssrfun ssrbool eqtype ssrnat seq choice ssrint.
From extructures Require Import ord fmap.
From CoqUtils Require Import word.

Require Import lib.utils common.types.

Import DoNotation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Concrete.

Local Open Scope word_scope.

Record mvec (mt : machine_types) : Type := MVec {
  cop  : opcode;
  ctpc : mword mt;
  cti  : mword mt;
  ct1  : mword mt;
  ct2  : mword mt;
  ct3  : mword mt
}.

Definition mvec_eqb mt (m1 m2 : mvec mt) : bool :=
  [&& cop m1 == cop m2,
      ctpc m1 == ctpc m2,
      cti m1 == cti m2,
      ct1 m1 == ct1 m2 &
      ct2 m1 == ct2 m2] && (ct3 m1 == ct3 m2).

Lemma mvec_eqbP mt : Equality.axiom (@mvec_eqb mt).
Proof.
  move => m1 m2.
  case: m1 => *. case: m2 => *.
  apply (iffP andP); simpl.
  - by move => [/and5P [/eqP -> /eqP -> /eqP -> /eqP -> /eqP ->] /eqP ->].
  - move => [-> -> -> -> -> ->]. by rewrite !eqxx.
Qed.

Definition mvec_eqMixin mt := EqMixin (@mvec_eqbP mt).
Canonical mvec_eqType mt :=
  Eval hnf in EqType (mvec mt) (@mvec_eqMixin mt).

Section MVecOrdType.

Variable mt : machine_types.

Definition tuple_of_mvec (mv : mvec mt) :=
  (cop mv, ctpc mv, cti mv, ct1 mv, ct2 mv, ct3 mv).

Definition mvec_of_tuple tup : mvec mt :=
  let: (cop, ctpc, cti, ct1, ct2, ct3) := tup in
  MVec cop ctpc cti ct1 ct2 ct3.

Lemma tuple_of_mvecK : cancel tuple_of_mvec mvec_of_tuple.
Proof. by case. Qed.

Definition mvec_choiceMixin := CanChoiceMixin tuple_of_mvecK.
Canonical mvec_choiceType := Eval hnf in ChoiceType (mvec mt) mvec_choiceMixin.
Definition mvec_ordMixin := CanOrdMixin tuple_of_mvecK.
Canonical mvec_ordType := Eval hnf in OrdType (mvec mt) mvec_ordMixin.

End MVecOrdType.

Record rvec (mt : machine_types) : Type := RVec {
  ctrpc : mword mt;
  ctr   : mword mt
}.

Definition rvec_eqb mt (r1 r2 : rvec mt) : bool :=
  [&& ctrpc r1 == ctrpc r2 & ctr r1 == ctr r2].

Lemma rvec_eqbP mt : Equality.axiom (@rvec_eqb mt).
Proof.
  move => r1 r2.
  case: r1 => *. case: r2 => *.
  apply (iffP andP); simpl.
  - by move => [/eqP -> /eqP ->].
  - move => [-> ->]. by rewrite !eqxx.
Qed.

Definition rvec_eqMixin mt := EqMixin (@rvec_eqbP mt).
Canonical rvec_eqType mt :=
  Eval hnf in EqType (rvec mt) (rvec_eqMixin mt).

Definition rules mt := {fmap mvec mt -> rvec mt}.

Section WithClasses.

Context (mt : machine_types).
Context (ops : machine_ops mt).

Let mvec := mvec mt.
Let rvec := rvec mt.
Let rules := rules mt.
Let atom := atom (mword mt) (mword mt).

(* If we were doing good modularization, these would be abstract! *)
Definition cache_line_addr : mword mt := 0%w.
(* BCP: Call it fault_handler_addr? *)
Definition fault_handler_start : mword mt := as_word 8.
Definition TNone   : mword mt := as_word 8.
Definition TMonitor : mword mt := 0.

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

Definition mask_dc (dcm : DCMask) (mv : mvec) : mvec :=
  let '(MVec op tpc ti t1 t2 t3) := mv in
  MVec op
    (if dcm mvp_tpc then TNone else tpc)
    (if dcm mvp_ti  then TNone else ti)
    (if dcm mvp_t1  then TNone else t1)
    (if dcm mvp_t2  then TNone else t2)
    (if dcm mvp_t3  then TNone else t3).

Definition copy_mvec_part (mv : mvec) (tag : mword mt)
    (x : option mvec_part) : mword mt :=
  match x with
  | Some mvp_tpc => ctpc mv
  | Some mvp_ti  => cti mv
  | Some mvp_t1  => ct1 mv
  | Some mvp_t2  => ct2 mv
  | Some mvp_t3  => ct3 mv
  | None         => tag
  end.

Definition copy (mv : mvec) (rv : rvec) (ctm : CTMask) : rvec :=
  RVec (copy_mvec_part mv (ctrpc rv) (ct_trpc ctm))
         (copy_mvec_part mv (ctr   rv) (ct_tr   ctm)).

Definition is_monitor_tag (tpc:mword mt) : bool := tpc == TMonitor.

Definition cache_lookup (cache : rules)
    (masks : Masks) (mv : mvec) : option rvec :=
  let mask := masks (is_monitor_tag (ctpc mv)) (cop mv) in
  let masked_mv := mask_dc (dc mask) mv in
  do! rv <- getm cache masked_mv;
  Some (copy mv rv (ct mask)).

Local Notation memory := {fmap mword mt -> atom}.
Local Notation registers := {fmap reg mt -> atom}.

Record state := State {
  mem   : memory;
  regs  : registers;
  cache : rules;
  pc    : atom;
  epc   : atom
}.

Definition pcv (s : state) := vala (pc s).
Definition pct (s : state) := taga (pc s).

Lemma state_eta (cst : state) :
  cst = State (mem cst)
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
  let mv := mask_dc dcm (MVec op (vala atpc)
                              (vala ati) (vala at1) (vala at2) (vala at3)) in
  Some (setm cache mv (RVec (vala atrpc) (vala atr))).

Definition store_mvec (mem : memory) (mv : mvec) : memory :=
  unionm [fmap (Mop, (word_of_op (cop mv))@TMonitor);
               (Mtpc, (ctpc mv)@TMonitor);
               (Mti, (cti mv)@TMonitor);
               (Mt1, (ct1 mv)@TMonitor);
               (Mt2, (ct2 mv)@TMonitor);
               (Mt3, (ct3 mv)@TMonitor)]
         mem.

Section ConcreteSection.

Variable masks : Masks.

Local Notation "x .+1" := (x + 1)%w.

(* The mvector is written at fixed locations in monitor memory where
   the fault handler can access them (using the same addresses as for
   add_rule: Mop, Mtpc, etc.) *)
Definition miss_state (st : state) (mvec : mvec) : state :=
  let mem' := store_mvec (mem st) mvec in
  State mem' (regs st) (cache st) fault_handler_start@TMonitor (pc st).


(* The next functions build the next state by looking up on the cache,
   finding the appropriate tag values for the results and using those
   combined with its arguments (new register value and/or new pc value
   *)
(* TODO: find better name for these ... lookup? *)
(* BCP: check? *)

Definition next_state (st : state) (mvec : mvec)
                      (k : rvec -> option state) : option state :=
  let lookup := cache_lookup (cache st) masks mvec in
  match lookup with
  | Some rvec => k rvec
  | None => Some (miss_state st mvec)
  end.

Definition next_state_reg_and_pc (st : state) (mvec : mvec) (r : reg mt) x pc' : option state :=
  next_state st mvec (fun rvec =>
    do! reg' <- updm (regs st) r x@(ctr rvec);
    Some (State (mem st) reg' (cache st) pc'@(ctrpc rvec) (epc st))).

Definition next_state_reg (st : state) (mvec : mvec) r x : option state :=
  next_state_reg_and_pc st mvec r x (vala (pc st)).+1.

Definition next_state_pc (st : state) (mvec : mvec) x : option state :=
  next_state st mvec (fun rvec =>
    Some (State (mem st) (regs st) (cache st) x@(ctrpc rvec) (epc st))).

Inductive step (st st' : state) : Prop :=
| step_nop :
    forall mem reg cache pc epc tpc i ti,
    forall (ST : st = State mem reg cache pc@tpc epc),
    forall (PC : mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (Nop _)),
    let mv := MVec NOP tpc ti TNone TNone TNone in
    forall (NEXT : next_state_pc st mv (pc.+1) = Some st'),
      step st st'
| step_const :
    forall mem reg cache pc epc n r tpc i ti old told,
    forall (ST : st = State mem reg cache pc@tpc epc),
    forall (PC : mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (Const n r)),
    forall (OLD : reg r = Some old@told),
    let mv := MVec CONST tpc ti told TNone TNone in
    forall (NEXT : next_state_reg st mv r (swcast n) = Some st'),
      step st st'
| step_mov :
    forall mem reg cache pc epc r1 w1 r2 tpc i ti t1 old told,
    forall (ST : st = State mem reg cache pc@tpc epc),
    forall (PC : mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (Mov r1 r2)),
    forall (REG1 : reg r1 = Some w1@t1),
    forall (OLD : reg r2 = Some old@told),
    let mv := MVec MOV tpc ti t1 told TNone in
    forall (NEXT : next_state_reg st mv r2 w1 = Some st'),
      step st st'
| step_binop :
    forall mem reg cache pc epc op r1 r2 r3 w1 w2 tpc i ti t1 t2 old told,
    forall (ST : st = State mem reg cache pc@tpc epc),
    forall (PC : mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (Binop op r1 r2 r3)),
    forall (REG1 : reg r1 = Some w1@t1),
    forall (REG2 : reg r2 = Some w2@t2),
    forall (OLD : reg r3 = Some old@told),
    let mv := MVec (BINOP op) tpc ti t1 t2 told in
    forall (NEXT : next_state_reg st mv r3 (binop_denote op w1 w2) =
                   Some st'),
      step st st'
| step_load :
    forall mem reg cache pc epc r1 r2 w1 w2 tpc i ti t1 t2 old told,
    forall (ST : st = State mem reg cache pc@tpc epc),
    forall (PC : mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (Load r1 r2)),
    forall (REG1 : reg r1 = Some w1@t1),
    forall (M1 : mem w1 = Some w2@t2),
    forall (OLD : reg r2 = Some old@told),
    let mv := MVec LOAD tpc ti t1 t2 told in
    forall (NEXT : next_state_reg st mv r2 w2 = Some st'),
      step st st'
| step_store :
    forall mem reg cache pc epc r1 r2 w1 w2 w3 tpc i ti t1 t2 t3,
    forall (ST : st = State mem reg cache pc@tpc epc),
    forall (PC : mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (Store r1 r2)),
    forall (REG1 : reg r1 = Some w1@t1),
    forall (REG2 : reg r2 = Some w2@t2),
    forall (M1 : mem w1 = Some w3@t3),
    let mv := MVec STORE tpc ti t1 t2 t3 in
    forall (NEXT :
      next_state st mv (fun rvec =>
        do! mem' <- updm mem w1 w2@(ctr rvec);
        Some (State mem' reg cache (pc.+1)@(ctrpc rvec) epc)) = Some st'),
      step st st'
| step_jump :
    forall mem reg cache pc epc r w tpc i ti t1,
    forall (ST : st = State mem reg cache pc@tpc epc),
    forall (PC : mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (Jump r)),
    forall (REG : reg r = Some w@t1),
    let mv := MVec JUMP tpc ti t1 TNone TNone in
    forall (NEXT : next_state_pc st mv w = Some st'),
      step st st'
| step_bnz :
    forall mem reg cache pc epc r n w tpc i ti t1,
    forall (ST : st = State mem reg cache pc@tpc epc),
    forall (PC : mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (Bnz r n)),
    forall (REG : reg r = Some w@t1),
    let mv := MVec BNZ tpc ti t1 TNone TNone in
    let pc' := pc + if w == 0 then 1 else swcast n in
    forall (NEXT : next_state_pc st mv pc' = Some st'),
      step st st'
| step_jal :
    forall mem reg cache pc epc r w tpc i ti t1 old told,
    forall (ST : st = State mem reg cache pc@tpc epc),
    forall (PC : mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (Jal r)),
    forall (REG : reg r = Some w@t1),
    forall (OLD: reg ra = Some old@told),
    let mv := MVec JAL tpc ti t1 told TNone in
    forall (NEXT : next_state_reg_and_pc st mv ra (pc.+1) w = Some st'),
      step st st'
| step_jumpepc :
    forall mem reg cache pc tpc w tepc i ti,
    forall (ST : st = State mem reg cache pc@tpc w@tepc),
    forall (PC : mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (JumpEpc _)),
    let mv := MVec JUMPEPC tpc ti tepc TNone TNone in
    forall (NEXT : next_state_pc st mv w = Some st'),
      step st st'
| step_addrule :
    forall mem reg cache pc epc tpc i ti,
    forall (ST : st = State mem reg cache pc@tpc epc),
    forall (PC : mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (AddRule _)),
    let mv := MVec ADDRULE tpc ti TNone TNone TNone in
    forall (NEXT :
      next_state st mv (fun rvec =>
        do! cache' <- add_rule cache masks mem;
        Some (State mem reg cache' (pc.+1)@(ctrpc rvec) epc)) = Some st'),
      step st st'
| step_gettag :
    forall mem reg cache pc epc r1 r2 w tpc i ti t1 old told,
    forall (ST : st = State mem reg cache pc@tpc epc),
    forall (PC : mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (GetTag r1 r2)),
    forall (REG : reg r1 = Some w@t1),
    forall (OLD : reg r2 = Some old@told),
    let mv := MVec GETTAG tpc ti t1 told TNone in
    forall (NEXT : next_state_reg st mv r2 t1 = Some st'),
      step st st'
| step_puttag :
    forall mem reg cache pc epc r1 r2 r3 w t tpc i ti t1 t2 old told,
    forall (ST : st = State mem reg cache pc@tpc epc),
    forall (PC : mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (PutTag r1 r2 r3)),
    forall (REG1 : reg r1 = Some w@t1),
    forall (REG2 : reg r2 = Some t@t2),
    forall (OLD: reg r3 = Some old@told),
    let mv := MVec PUTTAG tpc ti t1 t2 told in
    forall (NEXT :
      next_state st mv (fun rvec =>
        do! reg' <- updm reg r3 w@t;
        Some (State mem reg' cache (pc.+1@(ctrpc rvec)) epc)) = Some st'),
      step st st'.

End ConcreteSection.

End WithClasses.

Notation memory mt := {fmap mword mt -> atom (mword mt) (mword mt)}.
Notation registers mt := {fmap reg mt -> atom (mword mt) (mword mt)}.

End Concrete.

Module Exports.

Import Concrete.

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

Arguments Concrete.State {_} _ _ _ _ _.
Arguments Concrete.TNone {mt}.
Arguments Concrete.TMonitor {mt}.
