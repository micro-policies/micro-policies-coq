Require Import List. Import ListNotations.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Require Import lib.hlist lib.Integers lib.utils lib.ordered lib.partial_maps common.common.
Require Import symbolic.symbolic symbolic.rules.

Import Symbolic.

Set Implicit Arguments.

Module Sym.

Section WithClasses.

Import PartMaps.

Context {t : machine_types}
        {ops : machine_ops t}
        {opss : machine_ops_spec ops}
        {scr : @syscall_regs t}.

Inductive ttag := DUMMY.

Definition ttag_eq (t1 t2:ttag) := true.

Lemma ttag_eqP : Equality.axiom ttag_eq.
Proof.
econstructor. destruct x; destruct y; auto.
Qed.

Definition ttag_eqMixin := EqMixin ttag_eqP.
Canonical ttag_eqType := Eval hnf in EqType ttag ttag_eqMixin.

Definition ttags : tag_kind -> eqType := fun _ => [eqType of ttag].

Section WithHLists.
Import HListNotations.

Definition permissive_handler (iv : IVec ttags) : option (OVec ttags (op iv)) :=
  match iv with
  | mkIVec NOP       _ _ []        => Some (@mkOVec ttags NOP DUMMY tt)
  | mkIVec CONST     _ _ [_]       => Some (@mkOVec ttags CONST DUMMY DUMMY)
  | mkIVec MOV       _ _ [_; _]    => Some (@mkOVec ttags MOV DUMMY DUMMY)
  | mkIVec (BINOP o) _ _ [_; _; _] => Some (@mkOVec ttags (BINOP o) DUMMY DUMMY)
  | mkIVec LOAD      _ _ [_; _; _] => Some (@mkOVec ttags LOAD DUMMY DUMMY)
  | mkIVec STORE     _ _ [_; _; _] => Some (@mkOVec ttags STORE DUMMY DUMMY)
  | mkIVec JUMP      _ _ [_]       => Some (@mkOVec ttags JUMP DUMMY tt)
  | mkIVec BNZ       _ _ [_]       => Some (@mkOVec ttags BNZ DUMMY tt)
  | mkIVec JAL       _ _ [_; _]    => Some (@mkOVec ttags JAL DUMMY DUMMY)
  | mkIVec SERVICE   _ _    []     => Some (@mkOVec ttags SERVICE DUMMY tt)
  | mkIVec _         _ _ _         => None
  end.

End WithHLists.

Program Instance sym_trivial : params := {
  ttypes := ttags;

  transfer := permissive_handler;

  internal_state := [eqType of unit] 
}.

Import DoNotation.

Definition trivial_syscalls : list (syscall t) := [].

Definition step := step trivial_syscalls.

End WithClasses.

Notation memory t := (Symbolic.memory t sym_trivial).
Notation registers t := (Symbolic.registers t sym_trivial).

End Sym.
