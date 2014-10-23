Require Import ssreflect ssrbool eqtype.

Require Import lib.Integers.
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
Require Import memory_safety.classes.
Require Import memory_safety.symbolic.
Require Import memory_safety.abstract.
Require Import memory_safety.refinementAS.

Section Refinement.

Let t := concrete_int_32_t.
Existing Instance concrete_int_32_ops.
Existing Instance concrete_int_32_ops_spec.


Definition color_size := 12%nat. (*2^13 colors*)
Definition color := [eqType of (Word.int color_size)].
Definition inc_color (c : color) := Word.add c (Word.repr 1).

Instance col : Sym.color_class := {|
  color := color;
  max_color := Word.repr (Word.max_unsigned color_size);
  inc_color c := Word.add c Word.one
|}.
Proof.
  rewrite /ordered.ltb /= /ordered.IntOrdered.int_ordered -(lock (ordered.IntOrdered.int_ordered_def _))
          /= /ordered.IntOrdered.int_compare /Word.unsigned /color_size.
  intros col.
  destruct (SetoidDec.equiv_dec col (Word.repr (Word.max_unsigned 12))) as [H7 | H7]; first by [].
  rewrite {1 2 3}/Word.ltu.
  rewrite Word.unsigned_repr //.
  case: (Coqlib.zlt (Word.unsigned col) (Word.max_unsigned 12)) => [H6 _ | H6]; last by [].
  case: (SetoidDec.equiv_dec col (col + 1)%w) => [|NEQ].
  { rewrite /= -{1}(Word.add_zero _ col) => /addwI contra.
    discriminate. }
  move: (Word.unsigned_range col) => [H1' H2'].
  rewrite addwC -{1 3 5}(add0w col) Word.translate_ltu //.
  - rewrite /= /Word.max_unsigned. omega.
  - have {H7} H7 := H7 : col <> Word.repr (Word.max_unsigned 12).
    rewrite [_ 1%w]/=. omega.
Defined.

(* Encoding scheme

  type_bits = color_bits + 1 = 14
    TypeData      -> 0
    TypePointer c -> c*2 + 1

  stag_bits = type_bits + color_bits + 3 = 29
    TagFree       -> 0
    TagValue t    -> (enc t)*4+1
    TagMemory c t -> c*2^(type_bits+3) + (enc t)*8 + 2
*)

Import Word.Notations List.ListNotations Sym.

Close Scope Z.
Open Scope nat.

Definition encode_type (ty : Sym.type) : Word.int 13 :=
  match ty with
      TypeData => Word.zero
    | TypePointer c => Word.pack [12;0] [c;Word.one]%wp
  end.

Definition decode_type (cty : Word.int 13) : option Sym.type :=
  let: [k; t]%wu := Word.unpack [12; 0] cty in
  if t == Word.zero then
    if k == Word.zero then Some TypeData
    else None
  else if t == Word.one then
         Some (TypePointer k)
  else None.

Lemma encode_typeK ty : decode_type (encode_type ty) = Some ty.
Proof.
  case: ty;
  rewrite /decode_type /encode_type;
  [idtac | intros; rewrite Word.packK];
  reflexivity.
Qed.

Lemma decode_typeK w ty : decode_type w = Some ty ->
                          encode_type ty = w.
Proof.
  rewrite /decode_type /encode_type.
  case E: (Word.unpack [12; 0] w) => [k [w' []]].
  move: (Word.unpackK [12; 0] w). rewrite E.
  have [?|?] := altP (w' =P Word.zero); try subst w'.
  { have [?|?] := altP (k =P Word.zero); try subst k; last by [].
    by move => H [<-]. }
  have [?|?] := altP (w' =P Word.one); try subst w'; last by [].
  by move => H [<-].
Qed.

Definition encode_mtag (tg : Sym.tag) : Word.int 29 :=
  match tg with
      TagFree => Word.zero
    | TagValue ty => Word.pack [12;13;2] [Word.zero; encode_type ty; Word.one]%wp
    | TagMemory c ty => Word.pack [12;13;2] [c; encode_type ty; Word.repr 2]%wp
  end.

Import DoNotation.

Definition decode_mtag' (ctg : Word.int 29) : option Sym.tag :=
  let: [hb; m]%wu := Word.unpack [26;2] ctg in
  if m == Word.zero then
    if hb == Word.zero then Some TagFree
    else None
  else
    let: [c; ty]%wu := Word.unpack [12;13] hb in
    if m == Word.one then
      if (c == Word.zero) then
        do! cty <- decode_type ty;
        Some (TagValue cty)
      else None
    else
      if m == Word.repr 2 then
        do! cty <- decode_type ty;
        Some (TagMemory c cty)
      else None.

Definition decode_mtag (ctg : Word.int 29) : option Sym.tag :=
  let: [c;ty; m]%wu := Word.unpack [12;13;2] ctg in
  if m == Word.zero then
    if c == Word.zero then
      if ty == Word.zero then Some TagFree
      else None
    else None
  else
    if m == Word.one then
      if (c == Word.zero) then
        do! cty <- decode_type ty;
        Some (TagValue cty)
      else None
    else
      if m == Word.repr 2 then
        do! cty <- decode_type ty;
        Some (TagMemory c cty)
      else None.

(*decode_mtag' would work too probably*)
Lemma encode_mtagK tg : decode_mtag (encode_mtag tg) = Some tg.
Proof.
  destruct tg as  [ty | c ty |];
  rewrite /decode_mtag /encode_mtag;

  try (remember (encode_type ty); rewrite Word.packK;
       simpl; subst; rewrite encode_typeK);
  reflexivity.
Qed.

Lemma decode_mtagK w tg : decode_mtag w = Some tg ->
                          encode_mtag tg = w.
Proof.
  rewrite /decode_mtag /encode_mtag.
  case E: (Word.unpack [12;13;2] w) => [c [cty [m []]]].
  move: (Word.unpackK [12;13;2] w). rewrite E.
  have [?|?] := altP (m =P Word.zero); try subst m.
  { have [?|?] := altP (c =P Word.zero); try subst c; last by [].
    have [?|?] := altP (cty =P Word.zero); try subst cty; last by [].
    by move => H [<-].
  }
  have [?|?] := altP (m =P Word.one); try subst m.
  { have [?|?] := altP (c =P Word.zero); try subst c; last by [].
    case DEC: (decode_type cty) => [ty|] //=.
    apply decode_typeK in DEC; subst.
      by move => H [<-].
  }
  have [?|?] := altP (m =P Word.repr 2); try subst m; last by [].
  case DEC: (decode_type cty) => [ty|] //=.
  apply decode_typeK in DEC; subst;
    by move => H [<-].
Qed.

Instance enc: encodable t Sym.ms_tags := {|
  decode k m w :=
    let: [ut; w']%wu := Word.unpack [29; 1] w in
    if w' == Word.zero then
      if ut == Word.zero then Some KERNEL
      else None
    else if w' == Word.one then
      do! ut <- decode_mtag ut;
      Some (@USER Sym.tag_eqType ut)
    else if w' == Word.repr 2 then
      do! ut <- decode_mtag ut;
      Some (@ENTRY Sym.tag_eqType ut)
    else None
|}.
Proof.
  - move=> * ?. reflexivity.
  - by [].
Qed.

Instance sp : Symbolic.params := Sym.sym_memory_safety t.

Context {color_map : Type -> Type}
        {color_map_class : PartMaps.partial_map color_map color}
        {color_map_spec : PartMaps.axioms color_map_class}.

Context {monitor_invariant : @kernel_invariant _ _ enc}
        {syscall_addrs : @memory_syscall_addrs t}
        {ap : Abstract.abstract_params [eqType of word t]}
        {apspec : Abstract.params_spec ap}
        {alloc : @Abstract.allocator t _ _}
        {allocspec : Abstract.allocator_spec alloc}.

Inductive refine_state (ast : Abstract.state t) (cst : Concrete.state t) : Prop :=
| rs_intro : forall (sst : Symbolic.state t) m,
               refinement_common.refine_state monitor_invariant (@Sym.memsafe_syscalls _ _ _ _ _) sst cst ->
               refinementAS.refine_state m ast sst ->
               refine_state ast cst.
Hint Constructors refine_state.

Hypothesis implementation_correct :
  kernel_code_correctness monitor_invariant (@Sym.memsafe_syscalls _ _ _ _ _).

Lemma backwards_refinement_as ast m sst sst' :
  refinementAS.refine_state m ast sst ->
  exec (Symbolic.step (@Sym.memsafe_syscalls _ _ _ _ _)) sst sst' ->
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
