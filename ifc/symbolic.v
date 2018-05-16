From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq fintype finfun.
From extructures Require Import ord fmap.
From CoqUtils Require Import hseq word.
From MicroPolicies
Require Import lib.utils common.types symbolic.symbolic symbolic.exec
ifc.labels ifc.common.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import DoNotation.

Section Dev.

Local Open Scope label_scope.

Variable L : labType.
Variable mt : machine_types.
Variable mops : machine_ops mt.
Context {sregs : syscall_regs mt}.
Context {addrs : ifc_addrs mt}.

Inductive mem_tag :=
| MemInstr
| MemData of L.

Definition option_of_mem_tag t :=
  match t with
  | MemInstr => None
  | MemData l => Some l
  end.

Definition mem_tag_of_option t :=
  match t with
  | None => MemInstr
  | Some l => MemData l
  end.

Lemma option_of_mem_tagK : cancel option_of_mem_tag mem_tag_of_option.
Proof. by case. Qed.

Definition mem_tag_eqMixin := CanEqMixin option_of_mem_tagK.
Canonical mem_tag_eqType := EqType mem_tag mem_tag_eqMixin.

Import Symbolic.

Definition ifc_tags := {|
  pc_tag_type    := [eqType of L];
  reg_tag_type   := [eqType of L];
  mem_tag_type   := mem_tag_eqType;
  entry_tag_type := unit_eqType
|}.

(** Tag propagation rules. *)

Definition instr_rules
  (op : opcode) (tpc : L) (ts : hseq (tag_type ifc_tags) (inputs op)) :
  option (ovec ifc_tags op) :=
  let ret := fun rtpc (rt : type_of_result ifc_tags (outputs op)) => Some (@OVec ifc_tags op rtpc rt) in
  match op, ts, ret with
  | NOP, _, ret                             => ret tpc tt
  | CONST, [hseq lold], ret                 => ret tpc ⊥
  | MOV, [hseq l; lold], ret                => ret tpc l
  | BINOP b, [hseq l1; l2; lold], ret       => ret tpc (l1 ⊔ l2)
  | LOAD, [hseq l1; MemData l2; lold], ret  => ret tpc (l1 ⊔ l2)
  | STORE, [hseq l1; l2; MemData lold], ret => if l1 ⊔ tpc ⊑ lold then
                                                 ret tpc (MemData (l1 ⊔ l2 ⊔ tpc))
                                               else None
  | JUMP, [hseq l], ret                     => ret (l ⊔ tpc) tt
  | BNZ, [hseq l], ret                      => ret (l ⊔ tpc) tt
  | JAL, [hseq l1; lold], ret               => ret (l1 ⊔ tpc) ⊥
  | _, _, _                                 => None
  end.

Definition transfer (iv : ivec ifc_tags) : option (vovec ifc_tags (op iv)) :=
  match iv with
  | IVec (OP op) tpc ti ts =>
    match ti with
    | MemInstr => @instr_rules op tpc ts
    | MemData _ => None
    end
  | IVec SERVICE tpc _ _ => Some tt
  end.

(** The internal state for the IFC policy is simply a sequence of atoms that has
    been output during execution. *)

Record int_ifc := IntIFC {
  outputs : seq (atom (mword mt) L);
  call_stack : seq (call_frame mt L)
}.

Definition tuple_of_int_ifc x :=
  (outputs x, call_stack x).

Definition int_ifc_of_tuple x :=
  IntIFC x.1 x.2.

Lemma tuple_of_int_ifcK : cancel tuple_of_int_ifc int_ifc_of_tuple.
Proof. by case. Qed.

Definition int_ifc_eqMixin := CanEqMixin tuple_of_int_ifcK.
Canonical int_ifc_eqType := Eval hnf in EqType int_ifc int_ifc_eqMixin.

Global Instance sym_ifc : params := {
  ttypes := ifc_tags;

  transfer := transfer;

  internal_state := int_ifc_eqType
}.

Local Notation state := (@Symbolic.state mt sym_ifc).

Implicit Types st : state.

(* Note that we often need to adjust the tag on the caller pc because it may be
   lower than the one on the current pc; for example, if we jump to the service
   via BNZ instead of JAL. *)

Definition return_fun st : option state :=
  if call_stack (internal st) is cf :: stk then
    do! retv <- regs st syscall_ret;
    do! rs' <- updm (cf_regs cf) syscall_ret (vala retv)@(taga (pc st) ⊔ taga retv);
    Some (State (mem st) rs' (cf_pc cf)
                {| outputs := outputs (internal st);
                   call_stack := stk |})
  else None.

Definition call_fun st : option state :=
  do! caller_pc <- regs st ra;
  let caller_pc := (vala caller_pc)@(taga caller_pc ⊔ taga (pc st)) in
  do! called_pc <- regs st syscall_arg1;
  Some (State (mem st) (regs st)
              (vala called_pc)@(taga called_pc ⊔ taga caller_pc)
              {| outputs := outputs (internal st);
                 call_stack :=
                   CallFrame caller_pc (regs st)
                   :: call_stack (internal st)
              |}).

Definition output_fun st : option state :=
  do! raddr <- regs st ra;
  let r_pc  := taga raddr ⊔ taga (pc st) in
  let raddr := (vala raddr)@r_pc in
  do! out   <- regs st syscall_arg1;
  let r_out := taga out in
  Some (State (mem st) (regs st) raddr
              {| outputs := rcons (outputs (internal st))
                                  (vala out)@(taga (pc st) ⊔ r_out);
                 call_stack := call_stack (internal st)
              |}).

Definition ifc_syscalls : syscall_table mt :=
  [fmap
     (return_addr, (Syscall tt return_fun));
     (call_addr, (Syscall tt call_fun));
     (output_addr, (Syscall tt output_fun))
  ].

Definition trace n st :=
  let st' := iter n (fun st' => odflt st' (stepf ifc_syscalls st')) st in
  drop (size (outputs (internal st))) (outputs (internal st')).

Local Notation step  := (@Symbolic.step mt mops sym_ifc ifc_syscalls).
Local Notation ratom := (atom (mword mt) (tag_type ifc_tags R)).
Local Notation matom := (atom (mword mt) (tag_type ifc_tags M)).

Hint Unfold stepf.
Hint Unfold next_state_pc.
Hint Unfold next_state_reg.
Hint Unfold next_state_reg_and_pc.
Hint Unfold next_state.

Ltac step_event_cat :=
  simpl in *; repeat autounfold;
  intros; subst; simpl in *;
  repeat match goal with
  | t : (_ * _)%type |- _ => destruct t; simpl in *
  end;
  match_inv; simpl; exists [::]; rewrite cats0.

Lemma step_event_cat s s' :
  step s s' ->
  exists t, outputs (internal s') = outputs (internal s) ++ t.
Proof.
  case; try by step_event_cat.
  move=> /= m rs pc sc rl [t stk] -> {s} _.
  rewrite /ifc_syscalls /run_syscall mkfmapE //=.
  case: ifP=> [_ [<-] {sc}|_] /=.
    rewrite /return_fun /= => e; match_inv=> /=.
    by exists [::]; rewrite cats0.
  case: ifP=> [_ [<-] {sc}|_] /=.
    rewrite /call_fun /= => e; match_inv=> /=.
    by exists [::]; rewrite cats0.
  case: ifP=> [_ [<-] {sc}|_] //=.
  rewrite /output_fun /= => e; match_inv=> /=.
  by rewrite -cats1; eexists; eauto.
Qed.

End Dev.
