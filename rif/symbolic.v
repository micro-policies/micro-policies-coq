From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq fintype finfun.
From CoqUtils Require Import hseq ord partmap word.
From MicroPolicies
Require Import lib.utils common.types symbolic.symbolic symbolic.exec rif.labels.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import DoNotation.

Section Dev.

Local Open Scope label_scope.

Variable L : labType.
Variable mt : machine_types.
Variable mops : machine_ops mt.

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

Global Instance sym_ifc : params := {
  ttypes := ifc_tags;

  transfer := transfer;

  internal_state := unit_eqType
}.

Local Notation state := (@Symbolic.state mt sym_ifc).

Implicit Types st : state.

Definition ifc_syscalls : syscall_table mt := emptym.

Local Notation step  := (@Symbolic.step mt mops sym_ifc ifc_syscalls).
Local Notation ratom := (atom (mword mt) (tag_type ifc_tags R)).
Local Notation matom := (atom (mword mt) (tag_type ifc_tags M)).

Hint Unfold stepf.
Hint Unfold next_state_pc.
Hint Unfold next_state_reg.
Hint Unfold next_state_reg_and_pc.
Hint Unfold next_state.

End Dev.
