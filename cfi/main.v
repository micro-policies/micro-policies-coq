Require Import ssreflect ssrbool eqtype.

Require Import lib.Coqlib.
Require Import lib.utils.
Require Import lib.partial_maps.
Require Import common.common.
Require Import concrete.concrete.
Require Import concrete.int_32.
Require Import symbolic.symbolic.
Require Import symbolic.int_32.
Require Import symbolic.refinement_common.
Require Import symbolic.backward.
Require Import symbolic.rules.
Require Import cfi.classes.
Require Import cfi.rules.
Require Import cfi.symbolic.
Require Import cfi.abstract.
Require Import cfi.refinementAS.

Section Refinement.

Let t := concrete_int_32_t.
Existing Instance concrete_int_32_ops.
Existing Instance concrete_int_32_ops_spec.

Context {ids : @classes.cfi_id t}
        {enc : @rules.encodable rules.cfi_tag_eqType t}.

Variable cfg : id -> id -> bool.

Instance sp : Symbolic.params := Sym.sym_cfi cfg.

Variable ki : refinement_common.kernel_invariant.
Variable stable : list (Symbolic.syscall t).
Variable atable : list (Abs.syscall t).

Inductive refine_state (ast : Abs.state t) (cst : Concrete.state t) : Prop :=
| rs_intro : forall (sst : Symbolic.state t),
               refinement_common.refine_state ki stable sst cst ->
               RefinementAS.refine_state stable ast sst ->
               refine_state ast cst.
Hint Constructors refine_state.

Hypothesis implementation_correct :
  kernel_code_correctness ki stable.

Hypothesis refine_syscalls_correct : RefinementAS.refine_syscalls stable atable stable.

Hypothesis syscall_sem :
  forall ac ast ast',
    @Abs.sem t ac ast = Some ast' ->
       let '(Abs.State imem _ _ _ b) := ast in
       let '(Abs.State imem' _ _ _ b') := ast' in
         imem = imem' /\ b' = b.

Hypothesis syscall_preserves_instruction_tags :
  forall sc st st',
    Sym.instructions_tagged (cfg := cfg) (Symbolic.mem st) ->
    Symbolic.sem sc st = Some st' ->
    Sym.instructions_tagged (cfg := cfg) (Symbolic.mem st').

Hypothesis syscall_preserves_valid_jmp_tags :
  forall sc st st',
    Sym.valid_jmp_tagged stable (Symbolic.mem st) ->
    Symbolic.sem sc st = Some st' ->
    Sym.valid_jmp_tagged stable (Symbolic.mem st').

Hypothesis syscall_preserves_entry_tags :
  forall sc st st',
    Sym.entry_points_tagged stable (Symbolic.mem st) ->
    Symbolic.sem sc st = Some st' ->
    Sym.entry_points_tagged stable (Symbolic.mem st').

Lemma backwards_refinement_as ast sst sst' :
  RefinementAS.refine_state stable ast sst ->
  exec (Symbolic.step stable) sst sst' ->
  exists ast',
    exec (fun ast ast' => Abs.step atable cfg ast ast') ast ast' /\
    RefinementAS.refine_state stable ast' sst'.
Proof.
  move => REF EXEC.
  elim: EXEC ast REF => {sst sst'} [sst _ |sst sst' sst'' _ STEPS EXEC IH] ast REF; first by eauto 7.
  exploit RefinementAS.backwards_simulation; eauto.
  intros (ast' & STEPA & REF').
  exploit (IH  ast'); eauto.
  intros (ast'' & EXECA & REF'').
  eauto 7.
Qed.

Lemma backwards_refinement (ast : Abs.state t) (cst cst' : Concrete.state t) :
  refine_state ast cst ->
  exec (Concrete.step _ masks) cst cst' ->
  in_user cst' = true ->
  exists ast',
    exec (fun ast ast' => Abs.step atable cfg ast ast') ast ast' /\
    refine_state ast' cst'.
Proof.
  move => [sst SC AS] EXECC INUSER.
  exploit @backward.backwards_refinement; eauto.
  intros (sst' & EXECS & SC').
  exploit backwards_refinement_as; eauto.
  intros (ast' & EXECA & AS'). eauto 7.
Qed.

End Refinement.
