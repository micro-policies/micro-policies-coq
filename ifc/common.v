From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From CoqUtils Require Import hseq ord partmap word.
From MicroPolicies Require Import lib.utils common.types ifc.labels.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section CallFrame.

Variable mt : machine_types.
Variable L : labType.

Record call_frame := CallFrame {
  cf_pc   : atom (mword mt) L;
  cf_lab  : L;
  cf_regs : {partmap reg mt -> atom (mword mt) L}
}.

Definition tuple_of_call_frame cf :=
  (cf_pc cf, cf_lab cf, cf_regs cf).

Definition call_frame_of_tuple cf :=
  let: (pc, lab, regs) := cf in
  CallFrame pc lab regs.

Lemma tuple_of_call_frameK : cancel tuple_of_call_frame call_frame_of_tuple.
Proof. by case. Qed.

Definition call_frame_eqMixin := CanEqMixin tuple_of_call_frameK.
Canonical call_frame_eqType :=
  Eval hnf in EqType call_frame call_frame_eqMixin.

End CallFrame.
