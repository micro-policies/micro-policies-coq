Require Import ssreflect ssrbool.

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
Require Import memory_safety.classes.
Require Import memory_safety.symbolic.
Require Import memory_safety.abstract.
Require Import memory_safety.refinementAS.

Section Refinement.

Let t := concrete_int_32_t.
Existing Instance concrete_int_32_ops.
Existing Instance concrete_int_32_ops_spec.
Instance sp : Symbolic.params := Sym.sym_memory_safety t.

(* XXX: Right now, it is actually contradictory to assume that
   symbolic tags for memory safety are encodable, because they are
   defined to be the same type as regular words. Thus, there aren't
   enough bits to define the encoding. We should fix this by choosing
   a different type for blocks.*)

Context {enc : encodable (@Symbolic.tag (Sym.sym_memory_safety t))}
        {monitor_invariant : @kernel_invariant _ _ _ enc}
        {syscall_addrs : @memory_syscall_addrs t}
        {ap : Abstract.abstract_params (word t)}
        {apspec : Abstract.params_spec ap}
        {alloc : @Abstract.allocator t _ _}.

Inductive refine_state (ast : Abstract.state t) (cst : Concrete.state t) : Prop :=
| rs_intro : forall (sst : Symbolic.state t) m,
               refinement_common.refine_state monitor_invariant (@Sym.memsafe_syscalls _ _ _ _) sst cst ->
               refinementAS.refine_state m ast sst ->
               refine_state ast cst.
Hint Constructors refine_state.

Hypothesis implementation_correct :
  kernel_code_correctness monitor_invariant (@Sym.memsafe_syscalls _ _ _ _).

Lemma backwards_refinement_as ast m sst sst' :
  refinementAS.refine_state m ast sst ->
  exec (Symbolic.step (@Sym.memsafe_syscalls _ _ _ _)) sst sst' ->
  exists ast' m',
    exec (fun ast ast' => Abstract.step ast ast') ast ast' /\
    refinementAS.refine_state m' ast' sst'.
Proof.
  move => REF EXEC.
  elim: EXEC m ast REF => {sst sst'} [sst _ |sst sst' sst'' _ STEPS EXEC IH] m ast REF; first by eauto 7.
  exploit backward_simulation; eauto.
  intros (ast' & m' & STEPA & REF').
  exploit (IH m' ast'); eauto.
  intros (ast'' & m'' & EXECA & REF'').
  eauto 7.
Qed.

Lemma backwards_refinement (ast : Abstract.state t) (cst cst' : Concrete.state t) :
  refine_state ast cst ->
  exec (Concrete.step _ masks) cst cst' ->
  in_user cst' = true ->
  exists ast',
    exec (fun ast ast' => Abstract.step ast ast') ast ast' /\
    refine_state ast' cst'.
Proof.
  move => [sst m SC AS] EXECC INUSER.
  exploit @backward.backwards_refinement; eauto.
  intros (sst' & EXECS & SC').
  exploit backwards_refinement_as; eauto.
  intros (ast' & EXECA & GOOD' & AS'). eauto 7.
Qed.

End Refinement.
