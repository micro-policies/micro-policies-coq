Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool.
Require Import Ssreflect.eqtype Ssreflect.ssrnat Ssreflect.choice.
Require Import Ssreflect.seq MathComp.ssrint.
Require Import CoqUtils.ord CoqUtils.word CoqUtils.partmap.

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

Inductive tag_loc (mt : machine_types) := LReg of reg mt | LMem of mword mt | LEPC | LNone.
Arguments LReg  {mt} r.
Arguments LMem  {mt} a.
Arguments LEPC  {mt}.
Arguments LNone {mt}.

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
Definition mvec_partOrdMixin := CanPartOrdMixin tuple_of_mvecK.
Canonical mvec_partOrdType :=
  Eval hnf in PartOrdType (mvec mt) mvec_partOrdMixin.
Definition mvec_ordMixin := CanOrdMixin tuple_of_mvecK.
Canonical mvec_ordType := Eval hnf in OrdType (mvec mt) mvec_ordMixin.

End MVecOrdType.

(* TODO: This has 3 indistinguishable slots for the arguments.  Should it
  instead have separate slots for things to write to registers vs. things to
  write to memory? *)
Record rvec (mt : machine_types) : Type := RVec {
  ctrpc : mword mt;
  ctri  : mword mt;
  ctr1  : mword mt;
  ctr2  : mword mt;
  ctr3  : mword mt
}.

Definition rvec_eqb mt (r1 r2 : rvec mt) : bool :=
  [&& ctrpc r1 == ctrpc r2 ,
      ctri  r1 == ctri  r2 ,
      ctr1  r1 == ctr1  r2 ,
      ctr2  r1 == ctr2  r2 &
      ctr3  r1 == ctr3  r2 ].

Lemma rvec_eqbP mt : Equality.axiom (@rvec_eqb mt).
Proof.
  move => r1 r2.
  case: r1 => *. case: r2 => *.
  apply (iffP and5P); simpl.
  - by move => [/eqP -> /eqP -> /eqP -> /eqP -> /eqP ->].
  - move => [-> -> -> -> ->]. by rewrite !eqxx.
Qed.

Definition rvec_eqMixin mt := EqMixin (@rvec_eqbP mt).
Canonical rvec_eqType mt :=
  Eval hnf in EqType (rvec mt) (rvec_eqMixin mt).

Definition rules mt := {partmap mvec mt -> rvec mt}.

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
Definition fault_handler_start : mword mt := as_word 11.
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
Definition Mtri : mword mt := (cache_line_addr + as_word 7)%w.
Definition Mtr1 : mword mt := (cache_line_addr + as_word 8)%w.
Definition Mtr2 : mword mt := (cache_line_addr + as_word 9)%w.
Definition Mtr3 : mword mt := (cache_line_addr + as_word 10)%w.

Definition mvec_fields := [:: Mop; Mtpc; Mti; Mt1; Mt2; Mt3].
Definition rvec_fields := [:: Mtrpc; Mtri; Mtr1; Mtr2; Mtr3].
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
  ct_tri  : option mvec_part;
  ct_tr1  : option mvec_part;
  ct_tr2  : option mvec_part;
  ct_tr3  : option mvec_part
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
       (copy_mvec_part mv (ctri  rv) (ct_tri  ctm))
       (copy_mvec_part mv (ctr1  rv) (ct_tr1  ctm))
       (copy_mvec_part mv (ctr2  rv) (ct_tr2  ctm))
       (copy_mvec_part mv (ctr3  rv) (ct_tr3  ctm)).

Definition is_monitor_tag (tpc:mword mt) : bool := tpc == TMonitor.

Definition cache_lookup (cache : rules)
    (masks : Masks) (mv : mvec) : option rvec :=
  let mask := masks (is_monitor_tag (ctpc mv)) (cop mv) in
  let masked_mv := mask_dc (dc mask) mv in
  do! rv <- getm cache masked_mv;
  Some (copy mv rv (ct mask)).

Local Notation memory := {partmap mword mt -> atom}.
Local Notation registers := {partmap reg mt -> atom}.

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
  do! atri  <- mem Mtri;
  do! atr1  <- mem Mtr1;
  do! atr2  <- mem Mtr2;
  do! atr3  <- mem Mtr3;
  do! op    <- op_of_word (vala aop);
  let dcm := dc (masks false op) in
  let mv := mask_dc dcm (MVec op (vala atpc)
                              (vala ati) (vala at1) (vala at2) (vala at3)) in
  Some (setm cache mv (RVec (vala atrpc) (vala atri) (vala atr1) (vala atr2) (vala atr3))).

Definition store_mvec (mem : memory) (mv : mvec) : memory :=
  unionm [partmap (Mop, (word_of_op (cop mv))@TMonitor);
                  (Mtpc, (ctpc mv)@TMonitor);
                  (Mti, (cti mv)@TMonitor);
                  (Mt1, (ct1 mv)@TMonitor);
                  (Mt2, (ct2 mv)@TMonitor);
                  (Mt3, (ct3 mv)@TMonitor)]
         mem.

Section ConcreteSection.

Variable masks : Masks.

Local Notation "x .+1" := (x + 1)%w.

Definition get_tag_loc (st : state) (l : tag_loc mt) : option (mword mt) :=
  match l with
    | LReg r => omap taga ((regs st) r)
    | LMem a => omap taga ((mem  st) a)
    | LEPC   => Some (taga (epc st))
    | LNone  => Some TNone
  end.

Definition upd_tag_loc (st : state) (l : tag_loc mt) (t : mword mt) : option state :=
  match l with
    | LReg r => do! regs' <- repm (regs st) r (fun v => vala v @ t);
                Some (State (mem st) regs' (cache st) (pc st) (epc st))
    | LMem a => do! mem' <- repm (mem st) a (fun v => vala v @ t);
                Some (State mem' (regs st) (cache st) (pc st) (epc st))
    | LEPC   => Some (State (mem st) (regs st) (cache st) (pc st) (vala (epc st))@t)
    | LNone  => Some st
  end.

Record lvec : Type := LVec {
  copL  : opcode;
  ctpcL : mword mt;
  ctiL  : mword mt;
  ct1L  : tag_loc mt;
  ct2L  : tag_loc mt;
  ct3L  : tag_loc mt
}.

Definition get_lvec (st : state) (lv : lvec) : option mvec :=
  do! ct1 <- get_tag_loc st (ct1L lv);
  do! ct2 <- get_tag_loc st (ct2L lv);
  do! ct3 <- get_tag_loc st (ct3L lv);
  Some (MVec (copL lv) (ctpcL lv) (ctiL lv) ct1 ct2 ct3).

Definition set_lvec (st0 : state) (lv : lvec) (rv : rvec) : option state :=
  do! st1 <- upd_tag_loc st0 (LMem (pcv st0)) (ctri rv);
  do! st2 <- upd_tag_loc st1 (ct1L lv)        (ctr1 rv);
  do! st3 <- upd_tag_loc st2 (ct2L lv)        (ctr2 rv);
  do! st4 <- upd_tag_loc st3 (ct3L lv)        (ctr3 rv);
  Some (State (mem st4) (regs st4) (cache st4) (pcv st4)@(ctrpc rv) (epc st4)).

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

Definition next_state (st : state) (lv : lvec) : option state :=
  do! mv <- get_lvec st lv;
  let lookup := cache_lookup (cache st) masks mv in
  match lookup with
  | Some rv => set_lvec st lv rv
  | None    => Some (miss_state st mv)
  end.

Definition next_state_pc (st : state) (lv : lvec) (pc' : mword mt) : option state :=
  do! st' <- next_state st lv;
  Some (State (mem st') (regs st') (cache st') pc'@(pct st') (epc st')).

Definition next_state_reg_and_pc (st : state) (lv : lvec)
                                 (r : reg mt) (x : mword mt) (pc' : mword mt) : option state :=
  do! st'   <- next_state_pc st lv pc';
  do! regs' <- repm (regs st') r (fun v => x@(taga v));
  Some (State (mem st') regs' (cache st') (pc st') (epc st')).

Definition next_state_reg (st : state) (lv : lvec) (r : reg mt) (x : mword mt) : option state :=
  next_state_reg_and_pc st lv r x (vala (pc st)).+1.

Inductive step (st st' : state) : Prop :=
| step_nop :
    forall mem reg cache pc epc tpc i ti,
    forall (ST : st = State mem reg cache pc@tpc epc),
    forall (PC : mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (Nop _)),
    let lv := LVec NOP tpc ti LNone LNone LNone in
    forall (NEXT : next_state_pc st lv (pc.+1) = Some st'),
      step st st'
| step_const :
    forall mem reg cache pc epc n r tpc i ti,
    forall (ST : st = State mem reg cache pc@tpc epc),
    forall (PC : mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (Const n r)),
    let lv := LVec CONST tpc ti (LReg r) LNone LNone in
    forall (NEXT : next_state_reg st lv r (swcast n) = Some st'),
      step st st'
| step_mov :
    forall mem reg cache pc epc r1 w1 r2 tpc i ti,
    forall (ST : st = State mem reg cache pc@tpc epc),
    forall (PC : mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (Mov r1 r2)),
    forall (REG1 : omap vala (reg r1) = Some w1),
    let lv := LVec MOV tpc ti (LReg r1) (LReg r2) LNone in
    forall (NEXT : next_state_reg st lv r2 w1 = Some st'),
      step st st'
| step_binop :
    forall mem reg cache pc epc op r1 r2 r3 w1 w2 tpc i ti,
    forall (ST : st = State mem reg cache pc@tpc epc),
    forall (PC : mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (Binop op r1 r2 r3)),
    forall (REG1 : omap vala (reg r1) = Some w1),
    forall (REG2 : omap vala (reg r2) = Some w2),
    let lv := LVec (BINOP op) tpc ti (LReg r1) (LReg r2) (LReg r3) in
    forall (NEXT : next_state_reg st lv r3 (binop_denote op w1 w2) =
                   Some st'),
      step st st'
| step_load :
    forall mem reg cache pc epc r1 r2 w1 w2 tpc i ti,
    forall (ST : st = State mem reg cache pc@tpc epc),
    forall (PC : mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (Load r1 r2)),
    forall (REG1 : omap vala (reg r1) = Some w1),
    forall (M1   : omap vala (mem w1) = Some w2),
    let lv := LVec LOAD tpc ti (LReg r1) (LMem w1) (LReg r2) in
    forall (NEXT : next_state_reg st lv r2 w2 = Some st'),
      step st st'
| step_store :
    forall mem reg cache pc epc r1 r2 w1 w2 tpc i ti,
    forall (ST : st = State mem reg cache pc@tpc epc),
    forall (PC : mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (Store r1 r2)),
    forall (REG1 : omap vala (reg r1) = Some w1),
    forall (REG2 : omap vala (reg r2) = Some w2),
    let lv := LVec STORE tpc ti (LReg r1) (LReg r2) (LMem w1) in
    forall (NEXT : (do! st'  <- next_state_pc st lv (pc.+1);
                    let: State mem' reg' cache' pc' epc' := st' in
                    do! mem'' <- repm mem' w1 (fun v => w2@(taga v));
                    Some (State mem'' reg' cache' pc' epc'))
                   = Some st'),
      step st st'
| step_jump :
    forall mem reg cache pc epc r w tpc i ti,
    forall (ST : st = State mem reg cache pc@tpc epc),
    forall (PC : mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (Jump r)),
    forall (REG : omap vala (reg r) = Some w),
    let lv := LVec JUMP tpc ti (LReg r) LNone LNone in
    forall (NEXT : next_state_pc st lv w = Some st'),
      step st st'
| step_bnz :
    forall mem reg cache pc epc r n w tpc i ti,
    forall (ST : st = State mem reg cache pc@tpc epc),
    forall (PC : mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (Bnz r n)),
    forall (REG : omap vala (reg r) = Some w),
    let lv := LVec BNZ tpc ti (LReg r) LNone LNone in
    let pc' := pc + if w == 0 then 1 else swcast n in
    forall (NEXT : next_state_pc st lv pc' = Some st'),
      step st st'
| step_jal :
    forall mem reg cache pc epc r w tpc i ti,
    forall (ST : st = State mem reg cache pc@tpc epc),
    forall (PC : mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (Jal r)),
    forall (REG : omap vala (reg r) = Some w),
    let lv := LVec JAL tpc ti (LReg r) (LReg ra) LNone in
    forall (NEXT : next_state_reg_and_pc st lv ra (pc.+1) w = Some st'),
      step st st'
| step_jumpepc :
    forall mem reg cache pc tpc w tepc i ti,
    forall (ST : st = State mem reg cache pc@tpc w@tepc),
    forall (PC : mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (JumpEpc _)),
    let lv := LVec JUMPEPC tpc ti LEPC LNone LNone in
    forall (NEXT : next_state_pc st lv w = Some st'),
      step st st'
| step_addrule :
    forall mem reg cache pc epc tpc i ti,
    forall (ST : st = State mem reg cache pc@tpc epc),
    forall (PC : mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (AddRule _)),
    let lv := LVec ADDRULE tpc ti LNone LNone LNone in
    forall (NEXT : (do! st' <- next_state_pc st lv (pc.+1);
                    let: State mem' reg' cache' pc' epc' := st' in
                    do! cache'' <- add_rule cache' masks mem';
                    Some (State mem' reg' cache'' pc' epc'))
                   = Some st'),
      step st st'
| step_gettag :
    forall mem reg cache pc epc r1 r2 tpc i ti t1,
    forall (ST : st = State mem reg cache pc@tpc epc),
    forall (PC : mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (GetTag r1 r2)),
    forall (REG : omap taga (reg r1) = Some t1),
    let lv := LVec GETTAG tpc ti (LReg r1) (LReg r2) LNone in
    forall (NEXT : next_state_reg st lv r2 t1 = Some st'),
      step st st'
| step_puttag :
    forall mem reg cache pc epc r1 r2 r3 w t tpc i ti,
    forall (ST : st = State mem reg cache pc@tpc epc),
    forall (PC : mem pc = Some i@ti),
    forall (INST : decode_instr i = Some (PutTag r1 r2 r3)),
    forall (REG1 : omap vala (reg r1) = Some w),
    forall (REG2 : omap vala (reg r2) = Some t),
    let lv := LVec PUTTAG tpc ti (LReg r1) (LReg r2) (LReg r3) in
    forall (NEXT : (do! st' <- next_state_pc st lv (pc.+1);
                    let: State mem' reg' cache' pc' epc' := st' in
                    do! reg'' <- updm reg' r3 w@t;
                    Some (State mem' reg'' cache' pc' epc'))
                   = Some st'),
      step st st'.

End ConcreteSection.

End WithClasses.

Notation memory mt := {partmap mword mt -> atom (mword mt) (mword mt)}.
Notation registers mt := {partmap reg mt -> atom (mword mt) (mword mt)}.

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

Arguments Concrete.state mt.
Arguments Concrete.State {_} _ _ _ _ _.
Arguments Concrete.TNone {mt}.
Arguments Concrete.TMonitor {mt}.
