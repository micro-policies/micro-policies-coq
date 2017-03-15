From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice seq.
From CoqUtils Require Import ord word fset partmap nominal.
Require Import lib.utils common.types common.segment sealing.classes.

Import DoNotation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Abs.

Section WithClasses.

Context (mt : machine_types)
        {ops : machine_ops mt}
        {scr : syscall_regs mt}
        {ssa : @sealing_syscall_addrs mt}.

Inductive value :=
| VData   : mword mt         -> value
| VKey    :             name -> value
| VSealed : mword mt -> name -> value.

Definition value_eq (v1 v2 : value) : bool :=
  match v1, v2 with
  | VData x1, VData x2 => x1 == x2
  | VKey k1, VKey k2 => k1 == k2
  | VSealed x1 k1, VSealed x2 k2 => (x1 == x2) && (k1 == k2)
  | _, _ => false
  end.

Lemma value_eqP : Equality.axiom value_eq.
Proof.
move=> v1 v2; apply/(iffP idP)=> [|<- {v2}].
  by case: v1 v2 => [x1|k1|x1 k1] [x2|k2|x2 k2] //=
                 => [/eqP ->|/eqP ->|/andP [/eqP -> /eqP ->]].
by case: v1=> * /=; rewrite !eqxx.
Qed.

Definition value_eqMixin := EqMixin value_eqP.
Canonical value_eqType := EqType value value_eqMixin.

Definition sum_of_value v :=
  match v with
  | VData x => inl x
  | VKey k => inr (inl k)
  | VSealed x k => inr (inr (x, k))
  end.

Definition value_of_sum v :=
  match v with
  | inl x => VData x
  | inr (inl k) => VKey k
  | inr (inr (x, k)) => VSealed x k
  end.

Lemma sum_of_valueK : cancel sum_of_value value_of_sum.
Proof. by case. Qed.

Lemma value_of_sumK : cancel value_of_sum sum_of_value.
Proof. do 3![case=>//]. Qed.

Definition value_choiceMixin := CanChoiceMixin sum_of_valueK.
Canonical value_choiceType := Eval hnf in ChoiceType value value_choiceMixin.
Definition value_ordMixin := CanOrdMixin sum_of_valueK.
Canonical value_ordType := Eval hnf in OrdType value value_ordMixin.
Definition value_nominalMixin := BijNominalMixin sum_of_valueK value_of_sumK.
Canonical value_nominalType :=
  Eval hnf in NominalType value value_nominalMixin.

Local Notation memory := {partmap mword mt -> value}.
Local Notation registers := {partmap reg mt -> value}.

Open Scope word_scope.

Local Notation "x .+1" := (x + 1) (at level 60).

Record state := State {
  mem : memory;
  regs : registers;
  pc : mword mt
}.

Definition state_eq (s1 s2 : state) :=
  [&& mem s1 == mem s2, regs s1 == regs s2 & pc s1 == pc s2].

Lemma state_eqP : Equality.axiom state_eq.
Proof.
move=> s1 s2; apply/(iffP idP) => [|<- {s2}].
  by case: s1 s2=> [???] [???] /and3P [/= /eqP -> /eqP -> /eqP ->].
by case: s1 => [???]; rewrite /state_eq !eqxx.
Qed.

Definition state_eqMixin := EqMixin state_eqP.
Canonical state_eqType := EqType state state_eqMixin.

Definition tuple_of_state (s : state) := (mem s, regs s, pc s).
Definition state_of_tuple s := let: (m, rs, pc) := s in State m rs pc.

Lemma tuple_of_stateK : cancel tuple_of_state state_of_tuple.
Proof. by case. Qed.

Lemma state_of_tupleK : cancel state_of_tuple tuple_of_state.
Proof. by do 2!case. Qed.

Definition state_choiceMixin := CanChoiceMixin tuple_of_stateK.
Canonical state_choiceType := Eval hnf in ChoiceType state state_choiceMixin.
Definition state_ordMixin := CanOrdMixin tuple_of_stateK.
Canonical state_ordType := Eval hnf in OrdType state state_ordMixin.
Definition state_nominalMixin :=
  BijNominalMixin tuple_of_stateK state_of_tupleK.
Canonical state_nominalType :=
  Eval hnf in NominalType state state_nominalMixin.

Lemma mem_names_state k (s : state) :
  (k \in names s) = (k \in names (mem s)) || (k \in names (regs s)).
Proof. by case: s=> [m rs p] /=; rewrite 2!in_fsetU /= in_fset0 orbF. Qed.

Definition syscall_addrs := [:: mkkey_addr; seal_addr; unseal_addr].

Notation "x '=?' y" := (x = Some y) (at level 99).

Definition decode (mem : memory) (pc : mword mt) :=
  match mem pc with
    | Some (VData i) => decode_instr i
    | _              => None
  end.

Inductive step (st st' : state) : Prop :=
| step_nop : forall mem reg pc
    (ST   : st = State mem reg pc)
    (INST : decode mem pc =? Nop _)
    (NEXT : st' = State mem reg (pc.+1)),   step st st'
| step_const : forall mem reg reg' pc n r
    (ST   : st = State mem reg pc)
    (INST : decode mem pc =? Const n r)
    (UPD  : updm reg r (VData (swcast n)) =? reg')
    (NEXT : st' = State mem reg' (pc.+1)),   step st st'
| step_mov : forall mem reg reg' pc r1 v1 r2
    (ST   : st = State mem reg pc)
    (INST : decode mem pc =? Mov r1 r2)
    (R1W  : reg r1 =? v1)
    (UPD  : updm reg r2 v1 =? reg')
    (NEXT : st' = State mem reg' (pc.+1)),   step st st'
| step_binop : forall mem reg reg' pc op r1 r2 r3 w1 w2
    (ST   : st = State mem reg pc)
    (INST : decode mem pc =? Binop op r1 r2 r3)
    (R1W  : reg r1 =? VData w1)
    (R2W  : reg r2 =? VData w2)
    (UPD  : updm reg r3 (VData (binop_denote op w1 w2)) =? reg')
    (NEXT : st' = State mem reg' (pc.+1)),   step st st'
| step_load : forall mem reg reg' pc r1 r2 w1 v2
    (ST   : st = State mem reg pc)
    (INST : decode mem pc =? Load r1 r2)
    (R1W  : reg r1 =? VData w1)
    (MEM1 : mem w1 =? v2)
    (UPD  : updm reg r2 v2 =? reg')
    (NEXT : st' = State mem reg' (pc.+1)),   step st st'
| step_store : forall mem mem' reg pc r1 r2 w1 v2
    (ST   : st = State mem reg pc)
    (INST : decode mem pc =? Store r1 r2)
    (R1W  : reg r1 =? VData w1)
    (R2W  : reg r2 =? v2)
    (UPDM : updm mem w1 v2 =? mem')
    (NEXT : st' = State mem' reg (pc.+1)),   step st st'
| step_jump : forall mem reg pc r w
    (ST   : st = State mem reg pc)
    (INST : decode mem pc =? Jump r)
    (RW   : reg r =? VData w)
    (NEXT : st' = State mem reg w),   step st st'
| step_bnz : forall mem reg pc r n w
    (ST   : st = State mem reg pc)
    (INST : decode mem pc =? Bnz r n)
    (RW   : reg r =? VData w),
    let pc' := pc + (if w == 0
                     then 1 else swcast n) in forall
    (NEXT : st' = State mem reg pc'),   step st st'
| step_jal : forall mem reg reg' pc r w
    (ST   : st = State mem reg pc)
    (INST : decode mem pc =? Jal r)
    (RW   : reg r =? VData w)
    (UPD  : updm reg ra (VData (pc.+1)) =? reg')
    (NEXT : st' = State mem reg' w),   step st st'
| step_mkkey : forall mem reg reg' pc
    (ST   : st = State mem reg mkkey_addr)
    (INST : decode mem mkkey_addr = None)
    (UPD  : updm reg syscall_ret (VKey (fresh (names st))) =? reg')
    (RET  : reg ra =? VData pc)
    (NEXT : st' = State mem reg' pc),   step st st'
| step_seal : forall mem reg reg' pc payload key
    (ST   : st = State mem reg seal_addr)
    (INST : decode mem seal_addr = None)
    (R1   : reg syscall_arg1 =? VData payload)
    (R2   : reg syscall_arg2 =? VKey key)
    (UPD  : updm reg syscall_ret (VSealed payload key) =? reg')
    (RET  : reg ra =? VData pc)
    (NEXT : st' = State mem reg' pc),   step st st'
| step_unseal : forall mem reg reg' pc payload key
    (ST   : st = State mem reg unseal_addr)
    (INST : decode mem unseal_addr = None)
    (R1   : reg syscall_arg1 =? VSealed payload key)
    (R2   : reg syscall_arg2 =? VKey key)
    (UPD  : updm reg syscall_ret (VData payload) =? reg')
    (RET  : reg ra =? VData pc)
    (NEXT : st' = State mem reg' pc),   step st st'.

Definition stepf (st : state) : option state :=
  let 'State mem reg pc := st in
  match decode mem pc with
    | Some Nop =>
      Some (State mem reg (pc.+1))
    | Some (Const n r) =>
      do! reg' <- updm reg r (VData (swcast n));
      Some (State mem reg' (pc.+1))
    | Some (Mov r1 r2) =>
      do! v <- reg r1;
      do! reg' <- updm reg r2 v;
      Some (State mem reg' (pc.+1))
    | Some (Binop b r1 r2 r3) =>
      do! v1 <- reg r1;
      do! v2 <- reg r2;
      if v1 is VData i1 then if v2 is VData i2 then
        do! reg' <- updm reg r3 (VData (binop_denote b i1 i2));
        Some (State mem reg' (pc.+1))
      else None else None
    | Some (Load r1 r2) =>
      do! v <- reg r1;
      if v is VData i then
        do! v' <- mem i;
        do! reg' <- updm reg r2 v';
        Some (State mem reg' (pc.+1))
      else None
    | Some (Store r1 r2) =>
      do! v1 <- reg r1;
      do! v2 <- reg r2;
      if v1 is VData i1 then
        do! mem' <- updm mem i1 v2;
        Some (State mem' reg (pc.+1))
      else None
    | Some (Jump r) =>
      do! v <- reg r;
      if v is VData i then
        Some (State mem reg i)
      else None
    | Some (Bnz r n) =>
      do! vr <- reg r;
      if vr is VData c then
        let pc' := pc + if c == 0
                        then 1 else swcast n in
        Some (State mem reg pc')
      else None
    | Some (Jal r) =>
      do! vr <- reg r;
      if vr is VData i then
        do! reg' <- updm reg ra (VData (pc.+1));
        Some (State mem reg' i)
      else None
    | Some JumpEpc | Some AddRule | Some (GetTag _ _)
    | Some (PutTag _ _ _) | Some Halt =>
    None
    | None =>
    if pc == mkkey_addr then
      let k := fresh (names st) in
      do! reg' <- updm reg syscall_ret (VKey k);
      do! ret <- reg ra;
      if ret is VData pc' then
        Some (State mem reg' pc')
      else None
    else if pc == seal_addr then
      do! v1 <- reg syscall_arg1;
      do! v2 <- reg syscall_arg2;
      if v1 is VData payload then if v2 is VKey k then
        do! reg' <- updm reg syscall_ret (VSealed payload k);
        do! ret <- reg ra;
        if ret is VData pc' then
          Some (State mem reg' pc')
        else None
      else None else None
    else if pc == unseal_addr then
      do! v1 <- reg syscall_arg1;
      do! v2 <- reg syscall_arg2;
      if v1 is VSealed payload k then if v2 is VKey k' then
        if k == k' then
          do! reg' <- updm reg syscall_ret (VData payload);
          do! ret <- reg ra;
          if ret is VData pc' then
            Some (State mem reg' pc')
          else None
        else None
      else None else None
    else
      None
    end.

(* TODO: Prove correctness *)

(* ---------------------------------------------------------------------- *)
(* Building initial machine states *)

Program Definition abstract_initial_state
      (user_mem : relocatable_segment (sealing_syscall_addrs mt) value)
      (base_addr : mword mt)
      (user_regs : seq (reg mt))
    : state :=
  let (_, gen) := user_mem in
  let mem_contents := gen base_addr ssa in
  let mem :=
    snd (foldl
      (fun x c => let: (i,m) := x in
                  (1 + i, setm m i c))
      (base_addr, emptym)
      mem_contents)

      in
  let regs :=
        foldl
          (fun regs r => setm regs r (VData 0))
           emptym user_regs in
  {|
    mem := mem;
    regs := regs;
    pc := base_addr
  |}.

End WithClasses.

Notation memory mt := {partmap mword mt -> @value mt}.
Notation registers mt := {partmap reg mt -> @value mt}.

End Abs.

Canonical Abs.value_eqType.
Canonical Abs.value_nominalType.
Canonical Abs.state_eqType.
Canonical Abs.state_nominalType.
