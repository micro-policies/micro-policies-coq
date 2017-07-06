From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq fintype finfun.
From CoqUtils Require Import hseq ord partmap word.
From MicroPolicies
Require Import lib.utils common.types symbolic.symbolic symbolic.exec ifc.labels.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import DoNotation.

Section Dev.

Local Open Scope label_scope.

Variable L : labType.
Variable mt : machine_types.
Variable mops : machine_ops mt.
Variable r_arg : reg mt.
Variable output_addr : mword mt.

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
  | JAL, [hseq l1; lold], ret               => ret (l1 ⊔ tpc) (l1 ⊔ tpc)
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
  outputs : seq (atom (mword mt) L)
}.

Definition seq_of_int_ifc (x : int_ifc) :=
  outputs x.

Definition int_ifc_of_seq x := IntIFC x.

Lemma seq_of_int_ifcK : cancel seq_of_int_ifc int_ifc_of_seq.
Proof. by case. Qed.

Definition int_ifc_eqMixin := CanEqMixin seq_of_int_ifcK.
Canonical int_ifc_eqType := Eval hnf in EqType int_ifc int_ifc_eqMixin.

Global Instance sym_ifc : params := {
  ttypes := ifc_tags;

  transfer := transfer;

  internal_state := int_ifc_eqType
}.

Local Notation state := (@Symbolic.state mt sym_ifc).

Implicit Types st : state.

Definition output_fun st : option state :=
  do! raddr <- regs st ra;
  do! out   <- regs st r_arg;
  let r_pc  := taga raddr in
  let r_out := taga out in
  Some (State (mem st) (regs st) (vala raddr)@(taga raddr)
              {| outputs := rcons (outputs (internal st))
                                  (vala out)@(r_pc ⊔ r_out) |}).

Definition ifc_syscalls : syscall_table mt :=
  [partmap (output_addr, (Syscall tt output_fun))].

Local Notation step  := (@Symbolic.step mt mops sym_ifc ifc_syscalls).
Local Notation ratom := (atom (mword mt) (tag_type ifc_tags R)).
Local Notation matom := (atom (mword mt) (tag_type ifc_tags M)).

Hint Unfold stepf.
Hint Unfold next_state_pc.
Hint Unfold next_state_reg.
Hint Unfold next_state_reg_and_pc.
Hint Unfold next_state.

End Dev.
