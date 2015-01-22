Require Import ssreflect ssrbool eqtype seq ssrint.
Require Import hseq ord word partmap.

Require Import lib.utils lib.word_utils.
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

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Refinement.

Let t := concrete_int_32_t.
Existing Instance concrete_int_32_ops.
Existing Instance concrete_int_32_ops_spec.

Definition color_size := 13%nat. (*2^13 colors*)
Definition color := [ordType of word color_size].
Definition inc_color (c : color) := (c + 1)%w.

Instance col : Sym.color_class := {|
  color := color;
  max_color := monew;
  inc_color := inc_color;
  ltb_inc col := leqw_succ _ col monew
|}.

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
      TypeData => @wpack [:: 13; 1] [hseq 0%w; 0%w]
    | TypePointer c => @wpack [:: 13;1] [hseq c; 1%w]
  end.

Definition decode_type (cty : word 14) : option Sym.type :=
  let: [hseq k; t] := @wunpack [:: 13; 1] cty in
  if t == 0%w then
    if k == 0%w then Some TypeData
    else None
  else if t == 1%w then
         Some (TypePointer k)
  else None.

Lemma encode_typeK ty : decode_type (encode_type ty) = Some ty.
Proof.
case: ty => [|s];
by rewrite /decode_type /encode_type wpackK.
Qed.

Lemma decode_typeK w ty : decode_type w = Some ty ->
                          encode_type ty = w.
Proof.
  rewrite /decode_type /encode_type.
  case E: (wunpack _) => [k [w' []]].
  move: (@wunpackK [:: 13; 1] w). rewrite E.
  have [?|?] := altP (w' =P 0%w); try subst w'.
  { have [?|?] := altP (k =P 0%w); try subst k; last by [].
    by move => H [<-]. }
  have [?|?] := altP (w' =P 1%w); try subst w'; last by [].
  by move => H [<-].
Qed.

Definition encode_mtag (tg : Sym.tag) : word 30 :=
  match tg with
      TagFree => @wpack [:: 13; 14; 3] [hseq 0; 0; 0]%w
    | TagValue ty => @wpack [:: 13;14;3] [hseq 0; encode_type ty; 1]%w
    | TagMemory c ty => @wpack [:: 13;14;3] [hseq c; encode_type ty; as_word 2]%w
  end.

Import DoNotation.

Definition decode_mtag (ctg : word 30) : option Sym.tag :=
  let: [hseq c;ty; m] := @wunpack [:: 13;14;3] ctg in
  if m == 0%w then
    if c == 0%w then
      if ty == 0%w then Some TagFree
      else None
    else None
  else
    if m == 1%w then
      if (c == 0%w) then
        do! cty <- decode_type ty;
        Some (TagValue cty)
      else None
    else
      if m == as_word 2 then
        do! cty <- decode_type ty;
        Some (TagMemory c cty)
      else None.

Lemma encode_mtagK tg : decode_mtag (encode_mtag tg) = Some tg.
Proof.
  destruct tg as  [ty | c ty |];
  rewrite /decode_mtag /encode_mtag ?wpackK;

  try (remember (encode_type ty); rewrite ?wpackK;
       simpl; subst; rewrite encode_typeK);
  try reflexivity.
Qed.

Lemma decode_mtagK w tg : decode_mtag w = Some tg ->
                          encode_mtag tg = w.
Proof.
  rewrite /decode_mtag /encode_mtag.
  case E: (wunpack _) => [c [cty [m []]]].
  move: (@wunpackK [:: 13;14;3] w). rewrite E.
  have [?|?] := altP (m =P 0%w); try subst m.
  { have [?|?] := altP (c =P 0%w); try subst c; last by [].
    have [?|?] := altP (cty =P 0%w); try subst cty; last by [].
    by move => H [<-].
  }
  have [?|?] := altP (m =P 1%w); try subst m.
  { have [?|?] := altP (c =P 0%w); try subst c; last by [].
    case DEC: (decode_type cty) => [ty|] //=.
    apply decode_typeK in DEC; subst.
      by move => H [<-].
  }
  have [?|?] := altP (m =P as_word 2); try subst m; last by [].
  case DEC: (decode_type cty) => [ty|] //=.
  apply decode_typeK in DEC; subst;
    by move => H [<-].
Qed.

Instance enc: encodable t Sym.ms_tags := {|
  decode k m w :=
    let: [hseq ut; w']%w := @wunpack [:: 30; 2] w in
    if w' == 0%w then None
    else if w' == 1%w then
      do! ut <- decode_mtag ut;
      Some (@USER Sym.tag_eqType ut)
    else if w' == as_word 2 then
      do! ut <- decode_mtag ut;
      Some (@ENTRY Sym.tag_eqType ut)
    else None
|}.
Proof.
  - move=> * ?. reflexivity.
  - admit.
Qed.

Instance sp : Symbolic.params := Sym.sym_memory_safety t.

Context {monitor_invariant : @kernel_invariant _ _ enc}
        {syscall_addrs : @memory_syscall_addrs t}
        {alloc : @Abstract.allocator t color}
        {allocspec : Abstract.allocator_spec alloc}.

Inductive refine_state (ast : Abstract.state t color) (cst : Concrete.state t) : Prop :=
| rs_intro : forall (sst : Symbolic.state t) m,
               refinement_common.refine_state monitor_invariant (@Sym.memsafe_syscalls _ _ _ _ _) sst cst ->
               refinementAS.refine_state m ast sst ->
               refine_state ast cst.
Hint Constructors refine_state.

Hypothesis implementation_correct :
  kernel_code_bwd_correctness monitor_invariant (@Sym.memsafe_syscalls _ _ _ _ _).

Lemma backwards_refinement_as ast m sst sst' :
  refinementAS.refine_state m ast sst ->
  exec (Symbolic.step (@Sym.memsafe_syscalls _ _ _ _ _)) sst sst' ->
  exists ast' m',
    exec (fun ast ast' => Abstract.step ast ast') ast ast' /\
    refinementAS.refine_state m' ast' sst'.
Proof.
  move => REF EXEC.
  elim: EXEC m ast REF => {sst sst'} [sst _ |sst sst' sst'' _ STEPS EXEC IH] m ast REF; first by eauto 7.
  have := @backward_simulation _ _ _ _ _ _ allocspec _ _ _ _ _ REF STEPS.
  intros (ast' & m' & STEPA & REF').
  have := IH m' ast' REF'; eauto.
  intros (ast'' & m'' & EXECA & REF'').
  eauto 7.
Qed.

Lemma backwards_refinement (ast : Abstract.state t color) (cst cst' : Concrete.state t) :
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
