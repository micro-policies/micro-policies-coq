From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq fintype finfun.
From CoqUtils Require Import hseq ord fset partmap word.
From MicroPolicies
Require Import lib.utils common.types symbolic.symbolic symbolic.exec rif.common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import DoNotation.

Section Dev.

Local Open Scope fset_scope.
Local Open Scope rif_scope.

Variable Σ : finType.
Variable mt : machine_types.
Variable mops : machine_ops mt.

Local Notation rifAutomaton := (rifAutomaton Σ).
Local Notation rifLabel := (rifLabel Σ).
Local Notation event := (event Σ mt).

Implicit Types r : rifAutomaton.

(** Definition of tags for locations (cf. [rif_tags] below). The data
    are tagged as follows:

    - The program counter is tagged with a current label and a
      possible reclassifier, which is only present if the last
      executed instruction was a JAL. This is used to make sure that
      the reclassification system service can only be invoked after a
      JAL.

    - Registers are tagged with labels, as usual.

    - Memory is split among data and instructions. Instructions are
      immutable and cannot be inspected as data. They may be tagged
      with a reclassifier, which is only relevant when invoking the
      reclassify system service with a JAL. Data is tagged with labels
      as usual.

    - Service entry points don't carry tags. *)

Inductive mem_tag :=
| MemInstr of option Σ
| MemData  of rifLabel.

Definition sum_of_mem_tag t :=
  match t with
  | MemInstr F => inl F
  | MemData l => inr l
  end.

Definition mem_tag_of_sum t :=
  match t with
  | inl F => MemInstr F
  | inr l => MemData l
  end.

Lemma sum_of_mem_tagK : cancel sum_of_mem_tag mem_tag_of_sum.
Proof. by case. Qed.

Definition mem_tag_eqMixin := CanEqMixin sum_of_mem_tagK.
Canonical mem_tag_eqType := EqType mem_tag mem_tag_eqMixin.

Import Symbolic.

Definition rif_tags := {|
  pc_tag_type    := [eqType of rifLabel * option Σ];
  reg_tag_type   := [eqType of rifLabel];
  mem_tag_type   := mem_tag_eqType;
  entry_tag_type := unit_eqType
|}.

(** Tag propagation rules. *)

Definition instr_rules
  (op : opcode) (tpc : rifLabel) (ti : option Σ) (ts : hseq (tag_type rif_tags) (inputs op)) :
  option (ovec rif_tags op) :=
  let ret := fun rtpc (rt : type_of_result rif_tags (outputs op)) => Some (@OVec rif_tags op rtpc rt) in
  match op, ts, ret with
  | NOP, _, ret                             => ret (tpc, None) tt
  | CONST, [hseq lold], ret                 => ret (tpc, None) ⊥ₗ
  | MOV, [hseq l; lold], ret                => ret (tpc, None) l
  | BINOP b, [hseq l1; l2; lold], ret       => ret (tpc, None) (l1 ⊔ₗ l2)
  | LOAD, [hseq l1; MemData l2; lold], ret  => ret (tpc, None) (l1 ⊔ₗ l2)
  | STORE, [hseq l1; l2; MemData lold], ret => if l1 ⊔ₗ tpc ⊑ₗ lold then
                                                 ret (tpc, None) (MemData (l1 ⊔ₗ l2 ⊔ₗ tpc))
                                               else None
  | JUMP, [hseq l], ret                     => ret (l ⊔ₗ tpc, None) tt
  | BNZ, [hseq l], ret                      => ret (l ⊔ₗ tpc, None) tt
  | JAL, [hseq l1; lold], ret               => ret (l1 ⊔ₗ tpc, ti) (l1 ⊔ₗ tpc)
  | _, _, _                                 => None
  end.

Definition transfer (iv : ivec rif_tags) : option (vovec rif_tags (op iv)) :=
  match iv with
  | IVec (OP op) (tpc, _) ti ts =>
    match ti with
    | MemInstr F => @instr_rules op tpc F ts
    | MemData _ => None
    end
  | IVec SERVICE (tpc, b) _ _ =>
    if b then Some tt else None
  end.

Global Instance sym_rif : params := {
  ttypes := rif_tags;

  transfer := transfer;

  internal_state := [eqType of seq event]
}.

Local Notation state := (@Symbolic.state mt sym_rif).

Implicit Types st : state.

Variable output_addr : mword mt.
Variable reclassify_addr : mword mt.
Variable r_arg : reg mt.

Definition output_fun st : option state :=
  do! raddr <- regs st ra;
  do! out   <- regs st r_arg;
  let r_pc  := rif_readers _ (rif_state (taga raddr)) in
  let r_out := rif_readers _ (rif_state (taga out)) in
  Some (State (mem st) (regs st) (Atom (vala raddr) (taga raddr, None))
              (rcons (internal st) (Output _ (vala out) (r_pc ⊔ᵣ r_out)))).

Definition reclassify_fun st : option state :=
  do! raddr <- regs st ra;
  do! arg   <- regs st r_arg;
  if (taga (pc st)).2 is Some F then
    do! regs  <- updm (regs st) r_arg (vala arg)@(rl_trans (taga arg) F);
    Some (State (mem st) regs
                (vala raddr)@(taga raddr, None)
                (rcons (internal st) (Reclassify _ (taga arg) F)))
  else None.

Definition rif_syscalls : syscall_table mt :=
  [partmap (output_addr, Syscall tt output_fun);
           (reclassify_addr, Syscall tt reclassify_fun)].

Local Notation step  := (@Symbolic.step mt mops sym_rif rif_syscalls).
Local Notation ratom := (atom (mword mt) (tag_type rif_tags R)).
Local Notation matom := (atom (mword mt) (tag_type rif_tags M)).

Hint Unfold stepf.
Hint Unfold next_state_pc.
Hint Unfold next_state_reg.
Hint Unfold next_state_reg_and_pc.
Hint Unfold next_state.

Ltac step_event_app :=
  simpl in *; repeat autounfold;
  intros; subst; simpl in *;
  repeat match goal with
  | t : (_ * _)%type |- _ => destruct t; simpl in *
  end;
  match_inv; simpl; exists [::]; rewrite cats0.

Lemma step_event_app s s' :
  step s s' ->
  exists t, internal s' = internal s ++ t.
Proof.
  case; try by step_event_app.
  move=> /= m rs pc sc [rl [oF|]] t -> {s} _;
  rewrite /rif_syscalls /run_syscall mkpartmapE //=.
  case: ifP=> [_ [<-] {sc}|_] /=.
    rewrite /output_fun /= => e; match_inv=> /=.
    rewrite -cats1; eexists; eauto.
  case: ifP=> [_ [<-] {sc}|_] //=.
  rewrite /reclassify_fun /= => e; match_inv=> /=.
  by rewrite -cats1; eexists; eauto.
Qed.

CoInductive s_indist rs st1 st2 : Prop :=
| SIndistLow of rl_readers (taga (pc st1)).1 ⊑ᵣ rs
             &  rl_readers (taga (pc st2)).1 ⊑ᵣ rs
             &  pc st1 = pc st2
             &  (forall rg, indist (oapp (@rl_readers _ \o taga) Anybody)
                                   rs (regs st1 rg) (regs st2 rg))
             &  (forall a, indist (oapp (fun t =>
                                           if taga t is MemData rl'
                                           then rl_readers rl'
                                           else Anybody) Anybody)
                                  rs (mem st1 a) (mem st2 a))
             &  observe rs (internal st1) = observe rs (internal st2)
| SIndistHigh of ~~ (rl_readers (taga (pc st1)).1 ⊑ᵣ rs)
              &  ~~ (rl_readers (taga (pc st2)).1 ⊑ᵣ rs).


Lemma high_step rs st1 st2 st1' :
  s_indist rs st1 st2 ->
  rl_readers (taga (pc st1)).1 ⊑ᵣ rs ->
  step st1 st1' ->
  exists2 st2',
    s_indist rs st1' st2' &
    step st2 st2'.
Proof.
move=> h_indist h_low1 /stepP h_step1.
suff h : match @stepf _ mops _ rif_syscalls st2 return Prop with
         | Some st2' => s_indist rs st1' st2'
         | None => False
         end.
  case h_step2: stepf h => [st2'|] // h_indist'; move/stepP in h_step2; eauto.
case: h_indist; last by rewrite h_low1.
case: st1 h_step1 h_low1 => m1 r1 [pc1 [rl1 oF1]] t1 /= h_step1 h_low1.
case: st2=> m2 r2 [pc2 [rl2 oF2]] t2 /= _ h_low2 h_pc r_ind m_ind i_ind.
move: pc1 rl1 oF1 h_pc h_step1 h_low1 {h_low2} => pc rl oF [<- <- <-] {pc2 rl2 oF2}.
move: (m_ind pc).
case: (m1 pc) => [[i1 ti1]|] /=.
(*  (* Not syscall *)
  case: (m2 pc) => [[i2 ti2]|]; rewrite /indist /=.*)
Admitted.

Lemma noninterference rs st1 st2 st1' st2' :
  s_indist rs st1 st2 ->
  exec step st1 st1' ->
  exec step st2 st2' ->
  observe rs (internal st1') = observe rs (internal st2').
Proof.
Admitted.

End Dev.
