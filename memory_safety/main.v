From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype fintype seq ssrint.
From extructures Require Import ord fmap.
From CoqUtils Require Import hseq word nominal.

Require Import lib.utils lib.word_utils.
Require Import common.types.
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

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Refinement.

Let mt := concrete_int_32_mt.
Existing Instance concrete_int_32_ops.
Existing Instance concrete_int_32_ops_spec.

Definition color_size := 13%nat. (*2^13 colors*)
Definition color := [ordType of word color_size].
Definition inc_color (c : color) := (c + 1)%w.

(* Encoding scheme

  type_bits = color_bits + 1 = 14
    TypeData      -> 0
    TypePointer c -> c*2 + 1

  stag_bits = type_bits + color_bits + 3 = 29
    TagFree       -> 0
    TagValue t    -> (enc t)*4+1
    TagMemory c t -> c*2^(type_bits+3) + (enc t)*8 + 2
*)

Import Sym.

Definition encode_type (ty : Sym.type) : word 14 :=
  match ty with
  | TypeData => @wpack [:: 13; 1] [hseq 0%w; 0%w]
  | TypePointer c => @wpack [:: 13;1] [hseq as_word (val c); 1%w]
  end.

Definition decode_type (cty : word 14) : option Sym.type :=
  let: [hseq k; t] := @wunpack [:: 13; 1] cty in
  if t == 0%w then
    if k == 0%w then Some TypeData
    else None
  else if t == 1%w then
    Some (TypePointer (Name (val k)))
  else None.

Definition encode_mtag (tg : Sym.mem_tag) : word 30 :=
  match tg with
  | TagFree => @wpack [:: 13; 14; 3] [hseq 0; 0; 0]%w
  | TagMemory c ty => @wpack [:: 13;14;3] [hseq as_word (val c); encode_type ty; as_word 2]%w
  end.

Import DoNotation.

Definition decode_mtag (ctg : word 30) : option Sym.mem_tag :=
  let: [hseq c;ty; m] := @wunpack [:: 13;14;3] ctg in
  if m == 0%w then
    if c == 0%w then
      if ty == 0%w then Some TagFree
      else None
    else None
  else
    if m == as_word 2 then
      do! cty <- decode_type ty;
      Some (TagMemory (Name (val c)) cty)
    else None.

Instance enc: encodable mt Sym.ms_tags := {
  decode k m := fun (w : mword mt) =>
    let: [hseq ut; w']%w := @wunpack [:: 30; 2] w in
    if w' == 0%w then None
    else
      match k return option (wtag Sym.ms_tags k) with
      | Symbolic.M =>
        if w' == 1%w then
          do! ut <- decode_mtag ut;
          Some (@User Sym.ms_tags ut)
        else if w' == as_word 2 then
          Some (@Entry Sym.ms_tags tt)
        else None
      | Symbolic.P
      | Symbolic.R =>
        let: [hseq ty; _]%w := @wunpack [:: 14; 16] ut in
        if w' == 1%w then
          do! ty <- decode_type ty;
          Some ty
        else None
      end
}.
Proof.
  - move=> * ?. reflexivity.
  - by move=> tk _; rewrite 2!wunpackS.
Qed.

Instance sp : Symbolic.params := Sym.sym_memory_safety mt.

Context {monitor_invariant : @monitor_invariant _ _ enc}
        {syscall_addrs : @memory_syscall_addrs mt}.

Inductive refine_state (ast : Abstract.state mt) (cst : Concrete.state mt) : Prop :=
| rs_intro : forall (sst : Symbolic.state mt) m,
               refinement_common.refine_state monitor_invariant (@Sym.memsafe_syscalls _ _ _ _) sst cst ->
               refinementAS.refine_state m ast sst ->
               refine_state ast cst.
Hint Constructors refine_state.

Hypothesis implementation_correct :
  monitor_code_bwd_correctness monitor_invariant (@Sym.memsafe_syscalls _ _ _ _).

Lemma backwards_refinement_as ast m sst sst' :
  refinementAS.refine_state m ast sst ->
  exec (Symbolic.step (@Sym.memsafe_syscalls _ _ _ _)) sst sst' ->
  exists ast' m',
    exec (fun ast ast' => Abstract.step ast ast') ast ast' /\
    refinementAS.refine_state m' ast' sst'.
Proof.
  move => REF EXEC.
  elim: EXEC m ast REF => {sst sst'} [sst _ |sst sst' sst'' _ STEPS EXEC IH] m ast REF; first by eauto 7.
  have := @backward_simulation _ _ _ _ _ _ _ _ REF STEPS.
  intros (ast' & STEPA & m' & REF').
  have := IH m' ast' REF'; eauto.
  intros (ast'' & m'' & EXECA & REF'').
  eauto 7.
Qed.

Lemma backwards_refinement (ast : Abstract.state mt) (cst cst' : Concrete.state mt) :
  refine_state ast cst ->
  exec (Concrete.step _ masks) cst cst' ->
  in_user cst' ->
  exists ast',
    exec (fun ast ast' => Abstract.step ast ast') ast ast' /\
    refine_state ast' cst'.
Proof.
  move => [sst m SC AS] EXECC INUSER.
  have := backward.backwards_refinement SC EXECC INUSER.
  move/(_ implementation_correct)=> [sst' EXECS SC'].
  have := backwards_refinement_as AS EXECS.
  intros (ast' & EXECA & GOOD' & AS'). by eauto 7.
Qed.

End Refinement.
