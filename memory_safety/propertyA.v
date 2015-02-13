Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool.
Require Import Ssreflect.ssrnat Ssreflect.seq Ssreflect.eqtype Ssreflect.fintype.

Require Import MathComp.path MathComp.fingraph.

Require Import CoqUtils.ord CoqUtils.word CoqUtils.partmap CoqUtils.fset.

Require Import lib.utils common.types.
Require Import memory_safety.property memory_safety.abstract.
Require Import memory_safety.classes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section MemorySafety.

Local Open Scope fset_scope.

Import Abstract.

Variable mt : machine_types.
Variable ops : machine_ops mt.
Variable sr : syscall_regs mt.
Variable block : ordType.
Variable alloc : allocator mt block.
Variable addrs : memory_syscall_addrs mt.

Hypothesis allocP : allocator_spec alloc.

Local Notation state := (state mt block).
Local Notation pointer := [eqType of pointer mt block].
Local Notation value := (value mt block).

Implicit Type m : memory mt block.
Implicit Type rs : registers mt block.
Implicit Type s : state.
Implicit Type b : block.
Implicit Type p : pointer.
Implicit Type bs : {fset block}.

Definition references m b b' :=
  [exists offs : mword mt * mword mt,
    getv m (b, offs.1) == Some (VPtr (b', offs.2))].

Inductive reachable pc rs m b : Prop :=
| ReachBasePc p of pc = VPtr p & p.1 = b
| ReachBaseReg r p of rs r = Some (VPtr p) & p.1 = b
| ReachHop b' of reachable pc rs m b' & references m b' b.
Hint Constructors reachable.

Definition reachable_blocks pc rs m bs :=
  forall b, b \in bs <-> reachable pc rs m b.

Definition live_blocks s bs :=
  reachable_blocks (pc s) (regs s) (mem s) bs /\
  (forall b, b \in bs -> b \in blocks s).

(* FIXME: Right now, this doesn't say anything about memory reads. *)
CoInductive valid_step s bs s' bs' : Prop :=
| ValidNop of mem s = mem s' & {subset bs' <= bs}
| ValidWrite p v of updv (mem s) p v = Some (mem s')
                  & {subset bs' <= bs} & p.1 \in bs
| ValidAlloc b of malloc_fun (mem s) (blocks s) 0%w = (mem s', b)
                & {subset bs' <= b |: bs}
| ValidFree b of Abstract.free_fun (Abstract.mem s) b = Some (Abstract.mem s')
               & {subset bs' <= bs} & b \in bs.

CoInductive value_ok pc rs m : value -> Prop :=
| VOkData x : value_ok pc rs m (VData _ x)
| VOkPtr p of reachable pc rs m p.1 : value_ok pc rs m (VPtr p).
Hint Constructors value_ok.

CoInductive valid_pc_upd (pc pc' : value) rs m : Prop :=
| ValidPcUpd of value_ok pc rs m pc'.
Hint Constructors valid_pc_upd.

CoInductive valid_reg_upd pc rs rs' m : Prop :=
| ValidRegSame of rs = rs'
| ValidRegUpd v r of updm rs r v = Some rs' & value_ok pc rs m v.
Hint Constructors valid_reg_upd.

Lemma upd_reachable pc pc' rs rs' m bs bs' :
  reachable_blocks pc rs m bs ->
  reachable_blocks pc' rs' m bs' ->
  valid_pc_upd pc pc' rs m ->
  valid_reg_upd pc rs rs' m ->
  {subset bs' <= bs}.
Proof.
move=> hbs hbs' v_pc v_rs b /hbs' reach_b; apply/hbs.
elim: b / reach_b {hbs hbs'} => [b [b' off] /= hpc' hb'|b r [b' off]/=|b b' _].
- rewrite {}hb' {b'} in hpc'.
  case: v_pc => v_pc.
  by case: pc' / v_pc hpc' => [//|[b' off'] /= ? [<- _]].
- move=> hr hb'; move: hr; rewrite {}hb' {b'}.
  case: v_rs => [-> hr|v r' upd_rs]; first by eapply ReachBaseReg; eauto.
  move: {upd_rs} (updm_set upd_rs)=> upd_rs v_ok.
  rewrite {}upd_rs {rs'} getm_set.
  have [_{r}[vE]|_ hr] := altP eqP.
    by case: v / v_ok vE => // - [b' off'] /= ? [<- _].
  by eapply ReachBaseReg; eauto.
by eapply ReachHop.
Qed.

Lemma get_reg_ok pc rs r m v bs :
  rs r = Some v -> value_ok pc rs m v.
Proof.
case: v => [?|[b off get_rs]]; constructor.
by eapply ReachBaseReg; eauto.
Qed.

Lemma get_mem_ok pc rs m p v :
  value_ok pc rs m (VPtr p) ->
  getv m p = Some v ->
  value_ok pc rs m v.
Proof.
move=> p_ok; move: {1 2}(VPtr p) p_ok (erefl (VPtr p))=> v'.
case: v' / => // - [b off] b_reach [<-].
case: v => [?|[b' off' get_p]]; constructor.
eapply ReachHop; eauto; apply/existsP; exists (off,off')=> /=.
by apply/eqP.
Qed.

Lemma lift_binop_ok pc rs m o v1 v2 v3 :
  value_ok pc rs m v1 ->
  value_ok pc rs m v2 ->
  lift_binop o v1 v2 = Some v3 ->
  value_ok pc rs m v3.
Proof.
rewrite /lift_binop.
case: v1 / => [v1|[b1 off1] hb1]; case: v2 / => [v2|[b2 off2] hb2];
case: o=> //;
try match goal with
| |- context[?b1 == ?b2] =>
  have [b1_eq_b2|b1_neq_b2] // := altP (b1 =P b2)
end;
move=> [<-]; constructor; done.
Qed.

Ltac simple_intros :=
  move=> /= *;
  repeat match goal with
  | H : live_blocks ?s ?bs |- _ =>
    let live := fresh "live" in
    let sub := fresh "sub" in
    case: H => [/= live sub]
  end;
  apply: ValidNop; first done.

Ltac solve_simple_cases :=
  simple_intros;
  first [ solve [ eapply upd_reachable; try eassumption;
                  eauto using get_reg_ok, get_mem_ok, lift_binop_ok;
                  done ]
        | failwith "solve_simple_cases" ].

Lemma safe_step s bs s' bs' :
  step s s' ->
  live_blocks s bs ->
  live_blocks s' bs' ->
  valid_step s bs s' bs'.
Proof.
case: s s' / => /=; try solve_simple_cases.
- move=> m m' rs b pc ptr i r1 r2 v _ _ get_ptr _ upd_m [/= hbs _] [/= hbs' _].
  eapply ValidWrite; eauto.
    admit.
  by apply/hbs; apply/(@ReachBaseReg _ _ _ ptr.1 r1 ptr); simpl; eauto.
- move=> m m' rs rs' bs'' sz b pc' _ hm' hrs' _ [/= hbs hsub] [/= hbs' hsub'].
  generalize (Abstract.malloc_fresh hm'); rewrite hsub //; apply/hbs'.
  apply: (@ReachBase _ _ syscall_ret 0%w) => /=.
  by rewrite (updm_set hrs') getm_set eqxx.
move=> m m' r ptr bs' pc' harg hm' _ [hbs1 _] hbs2 _.
right; eapply ValidFree; simpl; first by eauto.
apply/hbs1.
eapply (@ReachBase _ _ syscall_arg1 ptr.2); simpl; eauto.
case: ptr harg {hm'} => /=; eauto.
Qed.

Definition get_events (s : state) : seq (event pointer block) :=
  match Abstract.pc s with
  | Abstract.VData _ => [::]
  | Abstract.VPtr ptr =>
    match Abstract.getv (Abstract.mem s) ptr with
    | Some (Abstract.VData i) =>
      match decode_instr i with
      | Some (Load r1 r2) =>
        match Abstract.regs s r1 with
        | Some (Abstract.VPtr ptr') => [:: MemRead ptr ptr.1; MemRead ptr' ptr'.1]
        | _ => [:: MemRead ptr ptr.1]
        end
      | Some (Store r1 r2) =>
        match Abstract.regs s r2 with
        | Some (Abstract.VPtr ptr') => [:: MemRead ptr ptr.1; MemWrite ptr' ptr'.1]
        | _ => [:: MemRead ptr ptr.1]
        end
      | _ => [:: MemRead ptr ptr.1]
      end
    | _ => [:: MemRead ptr ptr.1]
    end
  end.

Definition abstract_msm : memory_safety_machine :=
  @MSMachine [eqType of state] pointer block (fun ptr b => ptr.1 == b)
             get_events (fun s s' => Abstract.step s s').

Lemma abstract_machine_has_memory_safety : memory_safety abstract_msm.
Proof.
move=> t x y H.
elim: t x y / H=> [s|s s' s'' ss] /=.
  rewrite cats0 /get_events.
  case pcE: (Abstract.pc s) => [?|ptr] //=.
  case iE: (Abstract.getv _ _)=> [[i|?]|] //=; try by rewrite eqxx.
  case instrE: (decode_instr i)=> [[]|]; try by move => *; rewrite /= eqxx.
    case: (Abstract.regs s _)=> [[]|]; by move=> *; rewrite /= !eqxx.
  case: (Abstract.regs s _)=> [[]|]; by move=> *; rewrite /= !eqxx.
rewrite all_cat => _ _ ->.
rewrite /get_events.
case pcE: (Abstract.pc s) => [?|ptr] //=.
case iE: (Abstract.getv _ _)=> [[i|?]|] //=; try by rewrite eqxx.
case instrE: (decode_instr i)=> [[]|]; try by move => *; rewrite /= eqxx.
  case: (Abstract.regs s _)=> [[]|]; by move=> *; rewrite /= !eqxx.
case: (Abstract.regs s _)=> [[]|]; by move=> *; rewrite /= !eqxx.
Qed.

End MemorySafety.
