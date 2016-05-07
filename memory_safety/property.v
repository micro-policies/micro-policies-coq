From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype.

Require Import lib.utils.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Events.

Variables (pT rT : eqType).
Variable can_access : pT -> rT -> bool.

Inductive event :=
| MemRead of pT & rT
| MemWrite of pT & rT.

Definition event_eq e1 e2 :=
  match e1, e2 with
  | MemRead ptr1 reg1, MemRead ptr2 reg2 =>
    (ptr1 == ptr2) && (reg1 == reg2)
  | MemWrite ptr1 reg1, MemWrite ptr2 reg2 =>
    (ptr1 == ptr2) && (reg1 == reg2)
  | _, _ => false
  end.

Lemma event_eqP : Equality.axiom event_eq.
Proof.
move=> [ptr1 reg1|ptr1 reg1] [ptr2 reg2|ptr2 reg2] /=; try by constructor.
  by apply/(equivP andP); split=> [[/eqP -> /eqP ->]|[-> ->]].
by apply/(equivP andP); split=> [[/eqP -> /eqP ->]|[-> ->]].
Qed.

Definition event_eqMixin := EqMixin event_eqP.
Canonical event_eqType := Eval hnf in EqType event event_eqMixin.

End Events.

Structure memory_safety_machine := MSMachine {
  state : eqType;
  pointer : eqType;
  region : eqType;
  can_access : pointer -> region -> bool;
  get_events : state -> seq (event pointer region);
  step : state -> state -> Prop
}.

Section FixMachine.

Variable m : memory_safety_machine.

Local Notation pT := (pointer m).
Local Notation rT := (region m).
Local Notation event := (event pT rT).

Implicit Type e : event.

Definition event_ok e :=
  match e with
  | MemRead ptr reg => can_access ptr reg
  | MemWrite ptr reg => can_access ptr reg
  end.

Definition memory_safety :=
  forall t x y, intermr (@step m) t x y ->
                all event_ok (flatten (map (@get_events m) t)).

End FixMachine.
