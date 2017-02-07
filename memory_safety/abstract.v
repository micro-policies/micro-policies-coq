From mathcomp Require Import
  ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype ssrint.
From CoqUtils Require Import ord word fset partmap nominal.
Require Import lib.utils.
Require Import common.types memory_safety.classes.

Import DoNotation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Abstract.

Open Scope bool_scope.

Section WithClasses.

Context (mt : machine_types).
Context {ops : machine_ops mt}.

Definition pointer := (name * mword mt)%type.

Inductive value :=
| VData : mword mt -> value
| VPtr : pointer -> value.

Definition sum_of_value v :=
  match v with
  | VData w => inl w
  | VPtr p => inr p
  end.

Definition value_of_sum v :=
  match v with
  | inl w => VData w
  | inr p => VPtr p
  end.

Lemma sum_of_valueK : cancel sum_of_value value_of_sum.
Proof. by case. Qed.

Lemma value_of_sumK : cancel value_of_sum sum_of_value.
Proof. by case. Qed.

Definition value_eq v1 v2 :=
  match v1, v2 with
  | VData w1, VData w2 => w1 == w2
  | VPtr p1, VPtr p2 => p1 == p2
  | _, _ => false
  end.

Lemma value_eqP : Equality.axiom value_eq.
Proof.
move=> [w1|p1] [w2|p2] /=; try by constructor.
  apply/(iffP eqP); congruence.
apply/(iffP eqP); congruence.
Qed.

Definition value_eqMixin := EqMixin value_eqP.
Canonical value_eqType := Eval hnf in EqType value value_eqMixin.
Definition value_choiceMixin := CanChoiceMixin sum_of_valueK.
Canonical value_choiceType := Eval hnf in ChoiceType value value_choiceMixin.
Definition value_ordMixin := CanOrdMixin sum_of_valueK.
Canonical value_ordType := Eval hnf in OrdType value value_ordMixin.
Definition value_nominalMixin :=
  BijNominalMixin sum_of_valueK value_of_sumK.
Canonical value_nominalType :=
  Eval hnf in NominalType value value_nominalMixin.

Lemma names_valueE (v : value) :
  names v = if v is VPtr p then fset1 p.1 else fset0.
Proof. by case: v=> [w|p] //=; rewrite -[RHS]fsetU0. Qed.

Definition frame := seq value.

Definition memory := {partmap name -> frame}.
Definition registers := {partmap reg mt -> value}.

Open Scope word_scope.

Local Notation word := (mword mt).
Local Notation "x .+1" := (fst x, snd x + 1).

Record state := State {
  mem : memory;
  regs : registers;
  pc : value
}.

Implicit Type s : state.

Definition tuple_of_state s := (mem s, regs s, pc s).

Definition state_of_tuple t :=
  let: (m, r, p) := t in State m r p.

Lemma tuple_of_stateK : cancel tuple_of_state state_of_tuple.
Proof. by case. Qed.

Lemma state_of_tupleK : cancel state_of_tuple tuple_of_state.
Proof. by case=> [[] ?]. Qed.

Definition state_eq s1 s2 :=
  [&& mem s1 == mem s2, regs s1 == regs s2 & pc s1 == pc s2].

Lemma state_eqP : Equality.axiom state_eq.
Proof.
case=> [m1 r1 pc1] [m2 r2 pc2] /=; apply/(iffP and3P) => /=.
  by case; do 3!move/eqP => ->.
by case; do 3!move=> ->; rewrite !eqxx.
Qed.

Definition state_eqMixin := EqMixin state_eqP.
Canonical state_eqType := Eval hnf in EqType state state_eqMixin.
Definition state_choiceMixin := CanChoiceMixin tuple_of_stateK.
Canonical state_choiceType := Eval hnf in ChoiceType state state_choiceMixin.
Definition state_ordMixin := CanOrdMixin tuple_of_stateK.
Canonical state_ordType := Eval hnf in OrdType state state_ordMixin.
Definition state_nominalMixin :=
  BijNominalMixin tuple_of_stateK state_of_tupleK.
Canonical state_nominalType :=
  Eval hnf in NominalType state state_nominalMixin.

Local Open Scope fset_scope.

Definition blocks s := names s.

CoInductive blocks_spec b s : Prop :=
| BlocksReg r ptr of regs s r = Some (VPtr ptr) & ptr.1 = b
| BlocksFrame of b \in domm (mem s)
| BlocksMem b' ptr fr of mem s b' = Some fr & ptr.1 = b & VPtr ptr \in fr
| BlocksPc ptr of pc s = VPtr ptr & ptr.1 = b.

Lemma in_blocks b s : reflect (blocks_spec b s) (b \in blocks s).
Proof.
case: s => [m rs p]; apply/(iffP idP).
  rewrite /blocks 2!in_fsetU /= -!orbA /=; case/or3P.
  - case/namesmP=>
      [b' fr m_b' /namesnP ?|
       b' fr m_b' /namessP [[w|ptr] in_fr]].
    + by subst b'; apply: BlocksFrame; rewrite /= mem_domm m_b'.
    + by rewrite in_fset0.
    rewrite in_fsetU namesT in_fset0 orbF.
    by move=> /namesnP ?; subst b; eapply BlocksMem; eauto.
  - case/namesmP=> [//|r [w|ptr] //= rs_r free].
    eapply BlocksReg; eauto.
    have {free} := free : b \in (fset1 ptr.1 :|: fset0).
    by rewrite fsetU0 in_fset1=>/eqP.
  case: p=> [w|p] //=.
  move=> free; eapply BlocksPc=> //=; eauto.
  have {free} := free : b \in (fset1 p.1 :|: fset0).
  by rewrite fsetU0 in_fset1=>/eqP.
rewrite /blocks 2!in_fsetU /= -!orbA; case=> [r ptr| |b' ptr fr|ptr] /=.
- move=> rs_r <- {b}; apply/or3P/Or32/namesmP.
  by eapply PMFreeNamesVal; eauto; rewrite in_fsetU in_fset1 eqxx.
- move=> /dommP [fr m_b]; apply/or3P/Or31/namesmP.
  eapply PMFreeNamesKey; eauto; exact/namesnP.
- move=> m_b' <- {b} h_ptr; apply/or3P/Or31/namesmP.
  eapply PMFreeNamesVal; eauto; apply/namessP.
  by exists (VPtr ptr); eauto; rewrite in_fsetU in_fset1 eqxx.
by move=> -> {p} ?; subst b; apply/or3P/Or33; rewrite in_fsetU in_fset1 eqxx.
Qed.

Implicit Type reg : registers.

Definition getv (mem : memory) (ptr : pointer) :=
  match mem ptr.1 with
  | None => None
  | Some fr => if ptr.2 < size fr then
                 Some (nth (VData 0) fr ptr.2)
               else
                 None
  end.

Definition updv (mem : memory) (ptr : pointer) (v : value) :=
  match mem ptr.1 with
  | None => None
  | Some fr =>
    if ptr.2 < size fr then
      let fr' := take ptr.2 fr ++ v :: drop ptr.2.+1%N fr in
      Some (setm mem ptr.1 fr')
    else None
  end.

Definition malloc_fun (mem : memory) bl (sz : word) : memory * name :=
  let b  := fresh bl in
  let fr := nseq sz (VData 0) in
  (setm mem b fr, b).

Lemma malloc_fresh : forall mem sz mem' bl b,
  malloc_fun mem bl sz = (mem',b) -> b \notin bl.
Proof.
move=> m sz m' bl b; rewrite /malloc_fun => - [_ <-].
exact: freshP.
Qed.

Lemma malloc_get : forall mem sz mem' bl b off,
  malloc_fun mem bl sz = (mem',b) ->
  (off < sz)%ord -> getv mem' (b,off) = Some (VData 0).
Proof.
move=> m sz m' bl b off; rewrite /malloc_fun/getv => - [<- <-] {m' b} /=.
rewrite setmE eqxx size_nseq Ord.ltNge -!val_ordE /= /Ord.leq/= -ltnNge.
by move=> in_bounds; rewrite in_bounds nth_nseq in_bounds.
Qed.

Lemma malloc_get_out_of_bounds : forall mem sz mem' bl b off,
  malloc_fun mem bl sz = (mem', b) ->
  (sz <= off)%ord -> getv mem' (b,off) = None.
Proof.
move=> m sz m' bl b off; rewrite /malloc_fun/getv => - [<- <-] {m' b} /=.
by rewrite setmE eqxx size_nseq -!val_ordE /= /Ord.leq/= ltnNge => ->.
Qed.

Lemma malloc_get_neq : forall mem bl b sz mem' b',
  malloc_fun mem bl sz = (mem',b') ->
  b <> b' ->
  mem' b = mem b.
Proof.
move=> m bl b sz m' b'; rewrite /malloc_fun=> -[<- <-] /(introF eqP).
by rewrite setmE => ->.
Qed.

Definition free_fun (m : memory) b :=
  if m b then Some (remm m b) else None.

Lemma free_Some : forall (mem : memory) b fr,
  mem b = Some fr ->
  exists mem', free_fun mem b = Some mem'.
Proof. by move=> m b fr h; rewrite /free_fun h /=; eauto. Qed.

Lemma free_get_fail : forall mem mem' b,
  free_fun mem b = Some mem' -> mem' b = None.
Proof.
move=> m m' b; rewrite /free_fun.
by case: (m b) => [fr|] //= [<-]; rewrite remmE eqxx.
Qed.

Lemma free_get : forall mem mem' b b',
  free_fun mem b = Some mem' ->
  b != b' -> mem' b' = mem b'.
Proof.
move=> m m' b b'; rewrite /free_fun.
by case: (m b) => [fr|] //= [<-]; rewrite remmE eq_sym => /negbTE ->.
Qed.

Context `{syscall_regs mt} `{memory_syscall_addrs mt}.

Definition lift_binop (f : binop) (x y : value) :=
  match f with
  | ADD => match x, y with
           | VData w1, VData w2 => Some (VData (binop_denote f w1 w2))
           | VPtr (b,w1), VData w2 => Some (VPtr (b, binop_denote f w1 w2))
           | VData w1, VPtr (b,w2) => Some (VPtr (b, binop_denote f w1 w2))
           | _, _ => None
           end
  | SUB => match x, y with
           | VData w1, VData w2 => Some (VData (binop_denote f w1 w2))
           | VPtr(b,w1), VData w2 => Some (VPtr (b, binop_denote f w1 w2))
           | VPtr(b1,w1), VPtr (b2,w2)=>
             if b1 == b2 then Some (VData (binop_denote f w1 w2))
             else None
           | _, _ => None
           end
  | EQ => match x, y with
         | VData w1, VData w2 => Some (VData (binop_denote f w1 w2))
         | VPtr(b1,w1), VPtr (b2,w2)=>
           if b1 == b2 then Some (VData (binop_denote f w1 w2))
           else None
          | _, _ => None
         end
  | _ => match x, y with
         | VData w1, VData w2 => Some (VData (binop_denote f w1 w2))
         | _, _ => None
         end
  end.

Inductive step : state -> state -> Prop :=
| step_nop : forall mem reg pc i,
             forall (PC :    getv mem pc = Some (VData i)),
             forall (INST :  decode_instr i = Some (Nop _)),
             step (State mem reg (VPtr pc)) (State mem reg (VPtr pc.+1))
| step_const : forall mem reg reg' pc i n r,
             forall (PC :    getv mem pc = Some (VData i)),
             forall (INST :  decode_instr i = Some (Const n r)),
             forall (UPD :   updm reg r (VData (swcast n)) = Some reg'),
             step (State mem reg (VPtr pc)) (State mem reg' (VPtr pc.+1))
| step_mov : forall mem reg reg' pc i r1 r2 w1,
             forall (PC :    getv mem pc = Some (VData i)),
             forall (INST :  decode_instr i = Some (Mov r1 r2)),
             forall (R1W :   reg r1 = Some w1),
             forall (UPD :   updm reg r2 w1 = Some reg'),
             step (State mem reg (VPtr pc)) (State mem reg' (VPtr pc.+1))
| step_binop : forall mem reg reg' pc i f r1 r2 r3 v1 v2 v3,
             forall (PC :    getv mem pc = Some (VData i)),
             forall (INST :  decode_instr i = Some (Binop f r1 r2 r3)),
             forall (R1W :   reg r1 = Some v1),
             forall (R2W :   reg r2 = Some v2),
             forall (BINOP : lift_binop f v1 v2 = Some v3),
             forall (UPD :   updm reg r3 v3 = Some reg'),
             step (State mem reg (VPtr pc)) (State mem reg' (VPtr pc.+1))
| step_load : forall mem reg reg' pc i r1 r2 pt v,
             forall (PC :    getv mem pc = Some (VData i)),
             forall (INST :  decode_instr i = Some (Load r1 r2)),
             forall (R1W :   reg r1 = Some (VPtr pt)),
             forall (MEM1 :  getv mem pt = Some v),
             forall (UPD :   updm reg r2 v = Some reg'),
             step (State mem reg (VPtr pc)) (State mem reg' (VPtr pc.+1))
| step_store : forall mem mem' reg pc ptr i r1 r2 v,
             forall (PC :    getv mem pc = Some (VData i)),
             forall (INST :  decode_instr i = Some (Store r1 r2)),
             forall (R1W :   reg r1 = Some (VPtr ptr)),
             forall (R2W :   reg r2 = Some v),
             forall (UPD :   updv mem ptr v = Some mem'),
             step (State mem reg (VPtr pc)) (State mem' reg (VPtr pc.+1))
| step_jump : forall mem reg pc i r pt,
             forall (PC :    getv mem pc = Some (VData i)),
             forall (INST :  decode_instr i = Some (Jump r)),
             forall (RW :    reg r = Some (VPtr pt)),
             step (State mem reg (VPtr pc)) (State mem reg (VPtr pt))
| step_bnz : forall mem reg pc i r n w,
             forall (PC :    getv mem pc = Some (VData i)),
             forall (INST :  decode_instr i = Some (Bnz r n)),
             forall (RW :    reg r = Some (VData w)),
             let             off_pc' := snd pc + (if w == 0
                                                  then 1
                                                  else swcast n) in
             step (State mem reg (VPtr pc)) (State mem reg (VPtr (fst pc,off_pc')))
| step_jal : forall mem reg reg' pc i r v,
             forall (PC :       getv mem pc = Some (VData i)),
             forall (INST :     decode_instr i = Some (Jal r)),
             forall (RW :       reg r = Some v),
             forall (UPD :      updm reg ra (VPtr (pc.+1)) = Some reg'),
             step (State mem reg (VPtr pc)) (State mem reg' v)
| step_malloc : forall mem mem' reg reg' sz b pc'
    (SIZE  : reg syscall_arg1 = Some (VData sz))
    (ALLOC : malloc_fun mem (blocks (State mem reg (VData (addr Malloc)))) sz = (mem', b))
    (UPD   : updm reg syscall_ret (VPtr (b,0)) = Some reg')
    (RA    : reg ra = Some (VPtr pc')),
    step (State mem reg (VData (addr Malloc))) (State mem' reg' (VPtr pc'))
| step_free : forall mem mem' reg ptr pc'
    (PTR  : reg syscall_arg1 = Some (VPtr ptr))
    (FREE : free_fun mem ptr.1 = Some mem')
    (RA   : reg ra = Some (VPtr pc')),
    step (State mem reg (VData (addr Free))) (State mem' reg (VPtr pc'))
(*
| step_size : forall mem reg reg' b o fr bl pc'
    (PTR  : reg syscall_arg1 = Some (VPtr (b,o)))
    (MEM  : mem b = Some fr),
    let size := VData (Z_to_word (Z_of_nat (List.length fr))) in forall
    (UPD  : upd reg syscall_ret size = Some reg')
    (RA   : reg ra = Some (VPtr pc')),
    step (State mem reg bl (VData size_addr)) (State mem reg' bl (VPtr pc'))
*)
| step_base : forall mem reg reg' b o pc'
    (PTR  : reg syscall_arg1 = Some (VPtr (b,o)))
    (UPD  : updm reg syscall_ret (VPtr (b,0)) = Some reg')
    (RA   : reg ra = Some (VPtr pc')),
    step (State mem reg (VData (addr Base))) (State mem reg' (VPtr pc'))
| step_eq : forall mem reg reg' v1 v2 pc'
    (V1   : reg syscall_arg1 = Some v1)
    (V2   : reg syscall_arg2 = Some v2),
    let v := VData (as_word (v1 == v2)) in forall
    (UPD  : updm reg syscall_ret v = Some reg')
    (RA   : reg ra = Some (VPtr pc')),
    step (State mem reg (VData (addr Eq))) (State mem reg' (VPtr pc')).

Variable initial_pc : pointer.
Variable initial_mem  : memory.
Variable initial_regs : registers.
Hypothesis initial_ra : initial_regs ra = Some (VPtr initial_pc).

Definition initial_state : state :=
  State initial_mem initial_regs (VPtr initial_pc).

End WithClasses.

End Abstract.

Arguments Abstract.state mt.
Arguments Abstract.memory mt.
Arguments Abstract.registers mt.

Canonical Abstract.value_eqType.
Canonical Abstract.value_ordType.
Canonical Abstract.value_nominalType.
Canonical Abstract.state_eqType.
Canonical Abstract.state_ordType.
Canonical Abstract.state_nominalType.
