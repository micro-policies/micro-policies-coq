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

Variable mt : machine_types.
Variable ops : machine_ops mt.
Variable sr : syscall_regs mt.
Variable block : ordType.
Variable allocator : Abstract.allocator mt block.
Variable addrs : memory_syscall_addrs mt.

Hypothesis allocatorP : Abstract.allocator_spec allocator.

Local Notation state := (Abstract.state mt block).
Local Notation pointer := [eqType of Abstract.pointer mt block].

Implicit Type s : state.
Implicit Type b : block.
Implicit Type p : pointer.
Implicit Type bs : {fset block}.

Definition references s b b' :=
  [exists offs : mword mt * mword mt,
    Abstract.getv (Abstract.mem s) (b, offs.1) ==
    Some (Abstract.VPtr (b', offs.2))].

Inductive reachable s b : Prop :=
| ReachBase r off of Abstract.regs s r = Some (Abstract.VPtr (b, off))
| ReachHop b' of reachable s b' & references s b' b.

Definition live_blocks s bs :=
  (forall b, b \in bs <-> reachable s b) /\
  (forall b, b \in bs -> b \in Abstract.blocks s).

CoInductive valid_write s s' bs : Prop :=
| ValidWrite p v
  of Abstract.updv (Abstract.mem s) p v = Some (Abstract.mem s')
  &  p.1 \in bs.

CoInductive valid_free s s' bs : Prop :=
| ValidFree b
  of Abstract.free_fun (Abstract.mem s) b = Some (Abstract.mem s')
  &  b \in bs.

Ltac contradict_equal_mem :=
  match goal with
  | H : is_true (?x != ?x) |- _ => by rewrite eqxx in H
  end.

Lemma change_no_alloc s s' bs :
  Abstract.step s s' ->
  live_blocks s bs ->
  live_blocks s' bs ->
  Abstract.mem s != Abstract.mem s' ->
  valid_write s s' bs \/ valid_free s s' bs.
Proof.
case: s s' / => /=; try (move=> *; contradict_equal_mem).
- move=> m m' rs b pc ptr i r1 r2 v _ _ get_ptr _ upd_m [hbs _] _ _.
  left; econstructor; eauto.
  apply/hbs; apply/(@ReachBase _ ptr.1 r1 ptr.2); simpl; eauto.
  by case: {upd_m get_ptr} ptr get_ptr.
- move=> m m' rs rs' bs' sz b pc' _ hm' hrs' _ [/= /(_ b) hbs /(_ b) hsub]
         [/= /(_ b) hbs' /(_ b) hsub'] _.
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
