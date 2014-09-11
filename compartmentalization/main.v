Require Import ssreflect ssrbool eqtype.

Require Import lib.Coqlib.
Require Import lib.utils.
Require Import common.common.
Require Import concrete.concrete.
Require Import concrete.int_32.
Require Import symbolic.symbolic.
Require Import symbolic.int_32.
Require Import symbolic.refinement_common.
Require Import symbolic.backward.
Require Import symbolic.rules.
Require Import compartmentalization.common.
Require Import compartmentalization.symbolic.
Require Import compartmentalization.abstract.
Require Import compartmentalization.refinementSA.

Section Refinement.

Let t := concrete_int_32_t.
Let sp := @Sym.sym_compartmentalization t.
Existing Instance concrete_int_32_ops.
Existing Instance concrete_int_32_ops_spec.
Existing Instance sp.

Context {enc : encodable t [eqType of @Sym.stag t]}
        {monitor_invariant : kernel_invariant}
        {syscall_addrs : compartmentalization_syscall_addrs t}.

Inductive refine_state (ast : Abs.state t) (cst : Concrete.state t) : Prop :=
| rs_intro : forall (sst : Symbolic.state t),
               Abs.good_state ast ->
               refinement_common.refine_state monitor_invariant Sym.syscalls sst cst ->
               refinementSA.refine ast sst ->
               refine_state ast cst.
Hint Constructors refine_state.

Hypothesis implementation_correct :
  kernel_code_correctness monitor_invariant Sym.syscalls.

Lemma backwards_refinement_as ast sst sst' :
  Abs.good_state ast ->
  refinementSA.refine ast sst ->
  exec (Symbolic.step Sym.syscalls) sst sst' ->
  exists ast',
    exec (fun ast ast' => Abs.step ast ast') ast ast' /\
    Abs.good_state ast' /\
    refinementSA.refine ast' sst'.
Proof.
  move => GOOD REF EXEC.
  elim: EXEC ast GOOD REF => {sst sst'} [sst _ |sst sst' sst'' _ STEPS EXEC IH] ast GOOD REF; first by eauto 7.
  exploit backward_simulation; eauto.
  intros (ast' & STEPA & REF').
  have GOOD' := Abs.good_state_preserved (spec := concrete_int_32_ops_spec)
                                         STEPA GOOD.
  exploit IH; eauto.
  intros (ast'' & EXECA & GOOD'' & REF'').
  eauto 7.
Qed.

Lemma backwards_refinement ast cst cst' :
  refine_state ast cst ->
  exec (@Concrete.step t _ masks) cst cst' ->
  in_user cst' = true ->
  exists ast',
    exec (fun ast ast' => Abs.step ast ast') ast ast' /\
    refine_state ast' cst'.
Proof.
  move => [sst GOOD SC AS] EXECC INUSER.
  exploit @backward.backwards_refinement; eauto.
  intros (sst' & EXECS & SC').
  exploit backwards_refinement_as; eauto.
  intros (ast' & EXECA & GOOD' & AS'). eauto 7.
Qed.

End Refinement.
