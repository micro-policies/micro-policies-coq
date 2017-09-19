From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat seq eqtype fintype.

From CoqUtils Require Import ord word fset fmap fperm nominal.

Require Import lib.utils lib.fmap_utils common.types symbolic.symbolic symbolic.exec.
Require Import memory_safety.property memory_safety.symbolic memory_safety.abstract.
Require Import memory_safety.refinementAS.
Require Import memory_safety.classes memory_safety.executable memory_safety.propertyA.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section MemorySafety.

Local Open Scope fset_scope.

Import Abstract.

Variable mt : machine_types.
Variable ops : machine_ops mt.
Variable sr : syscall_regs mt.
Variable addrs : memory_syscall_addrs mt.

Local Notation sstate := (@Symbolic.state mt (Sym.sym_memory_safety mt)).
Local Notation sstepf :=
  (@stepf _ ops (Sym.sym_memory_safety mt) (@Sym.memsafe_syscalls _ ops _ addrs)).
Local Notation astate := (Abstract.state mt).
Local Notation astepf := (AbstractE.step ops _ addrs).

Lemma noninterference sst1 sst1' sst2 sst2' mi1 mi2 ast m1 m2 pm n :
  stepn sstepf n sst1 = Some sst1' ->
  stepn sstepf n sst2 = Some sst2' ->
  refine_state mi1 (add_mem m1 ast) sst1 ->
  refine_state mi2 (add_mem m2 (rename pm ast)) sst2 ->
  fdisjoint (names ast) (domm m1) ->
  fdisjoint (names (rename pm ast)) (domm m2) ->
  exists ast' pm' mi1' mi2',
    [/\ refine_state mi1' (add_mem m1 ast') sst1',
        refine_state mi2' (add_mem m2 (rename pm' ast')) sst2',
        fdisjoint (names ast') (domm m1) &
        fdisjoint (names (rename pm' ast')) (domm m2) ].
Proof.
move=> ex1 ex2 ref1 ref2 dis1 dis2.
have [mi1' [ast1' [ex1' ref1']]] := refinement ref1 ex1.
have [mi2' [ast2' [ex2' ref2']]] := refinement ref2 ex2.
have := noninterference ops sr addrs n dis1 dis2.
rewrite ex1' ex2'.
case=> pm' [ast' [e1 dis1' e2 dis2']].
exists ast', pm', mi1', mi2'; split=> //.
  by rewrite -e1.
by rewrite -e2.
Qed.

End MemorySafety.
