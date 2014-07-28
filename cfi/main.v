Require Import ssreflect ssrbool ssrfun eqtype.

Require Import Coq.Lists.List. 
Require Import lib.Coqlib lib.utils.
Require Import lib.partial_maps lib.FiniteMaps lib.ordered.
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
Require Import Integers.

Module NatPMap := FiniteMap NatIndexed.

Instance nat_partial_map : PartMaps.partial_map NatPMap.t nat := {
  get V m n := NatPMap.get n m;
  set V m n v := NatPMap.set n v m;
  map_filter V1 V2 f m := NatPMap.map_filter f m;
  empty V := NatPMap.empty _
}.

Instance nat_partial_map_axioms : PartMaps.axioms nat_partial_map.
Proof.
  constructor.
  - (* get_set_eq *) intros V m n v. by apply NatPMap.gss.
  - (* get_set_neq *) intros V m n1 n2 v. by apply NatPMap.gso.
  - (* map_filter_correctness *) intros V1 V2 f m k. by apply NatPMap.gmap_filter.
  - (* empty_is_empty *) intros V k. by apply NatPMap.gempty.
Qed.

Module CFIInstances.

Section WithClasses.

(* ---------------------------------------------------------------- *)
(* int32 instance *)

Definition t := concrete_int_32_t.
Instance ops : machine_ops t := concrete_int_32_ops.

Definition id_size := Word.int 27.
Definition id := [eqType of id_size].
Definition bound : word t := Word.repr ((Word.max_unsigned 27) + 1)%Z. (*29 bits*)

Definition word_to_id (w : word t) : option id_size :=
  if (Word.ltu w bound) then Some (Word.castu w) else None.

Definition id_to_word (x : id) : word t := 
  Word.castu x.

Lemma id_to_word_bound x : Word.ltu (id_to_word x) bound.
Proof.
  destruct x as [x Hx]. 
  let u := eval compute in (Word.modulus 27) in
  change (Word.modulus 27) with u in Hx.
  unfold id_to_word, Word.castu, Word.ltu, bound.
  simpl. rewrite Word.Z_mod_modulus_eq. rewrite Zmod_small. 
  - destruct (zlt x 268435456); by [trivial | omega].
  -  let u := eval compute in (Word.modulus 31) in
     change (Word.modulus 31) with u.
     by omega.
Qed.
  
Lemma id_to_wordK x : word_to_id (id_to_word x) = Some x.
Proof.
  remember (id_to_word x) as w eqn:Hw.
  unfold word_to_id.
  rewrite Hw. clear Hw.
  rewrite id_to_word_bound.
  unfold id_to_word, Word.castu, bound in *.
  apply f_equal.
  rewrite Word.unsigned_repr_eq.
  let u := eval compute in (Word.modulus (word_size_minus_one t)) in
  change (Word.modulus (word_size_minus_one t)) with u.
  rewrite Zmod_small.
  - by apply Word.repr_unsigned.
  - unfold Word.unsigned. 
    assert (H := Word.intrange 27 x).
    let u := eval compute in (Word.modulus 27) in
                              change (Word.modulus 27) with u in H.
    by omega.
Qed.

Lemma word_to_idK w x :
  word_to_id w = Some x ->
  id_to_word x = w.
Proof.
  intros Hwid.
  unfold word_to_id in Hwid.
  destruct (Word.ltu w bound) eqn:Hl; [idtac | discriminate].
  inv Hwid.
  unfold id_to_word, Word.castu.
  rewrite Word.unsigned_repr_eq.
  let u := eval compute in (Word.modulus 27) in
                            change (Word.modulus 27) with u.
  unfold Word.ltu, bound in Hl.
  simpl in Hl.
  case: (zlt (Word.unsigned w) 268435456) => Hcmp.
  + rewrite Zmod_small; [by apply Word.repr_unsigned | idtac].
    split; auto. 
    destruct (Word.unsigned_range w) as [? ?].
    by assumption.
  + exfalso. 
    apply zlt_false with (A := bool) (a := true) (b := false) in Hcmp.
    rewrite Hl in Hcmp.
    by discriminate.
Qed.
    
Instance ids : cfi_id := {|
 id := id;
 word_to_id := word_to_id;
 id_to_word := id_to_word
|}.
Proof.
  - by apply id_to_wordK.
  - by apply word_to_idK.
Defined.

(* Encoding of tags:
      DATA           --> 0
      INSTR None     --> 1
      INSTR (Some x) --> x*4+2
*)

Import Word.Notations List.ListNotations.

Definition encode_cfi_tag (t : cfi_tag) : Word.int 29 :=
 match t with
   DATA => Word.pack [27; 1] [Word.zero; Word.zero]%wp
 | INSTR None => Word.pack [27; 1] [Word.zero; Word.one]%wp
 | INSTR (Some x) => Word.pack [27; 1] [x; Word.repr 2]%wp
 end.

Definition decode_cfi_tag (t : Word.int 29) : option cfi_tag :=
  let: [k; t]%wu := Word.unpack [27; 1] t in
  if t == Word.zero then
    if k == Word.zero then Some DATA
    else None
  else if t == Word.one then
    if k == Word.zero then Some (INSTR None)
    else None
  else if t == Word.repr 2 then
    Some (INSTR (Some k))
  else None.

Lemma encode_cfi_tagK t : decode_cfi_tag (encode_cfi_tag t) = Some t.
Proof.
  case: t => [[k|]|];
  by rewrite /decode_cfi_tag /encode_cfi_tag Word.packK /=.
Qed.

Lemma decode_cfi_tagK w t : decode_cfi_tag w = Some t ->
                                encode_cfi_tag t = w.
Proof.
  rewrite /decode_cfi_tag /encode_cfi_tag.
  case E: (Word.unpack [27; 1] w) => [k [w' []]].
  move: (Word.unpackK [27; 1] w). rewrite E.
  have [?|?] := altP (w' =P Word.zero); try subst w'.
  { have [?|?] := altP (k =P Word.zero); try subst k; last by [].
    by move => H [<-]. }
  have [?|?] := altP (w' =P Word.one); try subst w'.
  { have [?|?] := altP (k =P Word.zero); try subst k; last by [].
     by move => H [<-]. }
  have [?|?] := altP (w' =P Word.repr 2); try subst w'; last by [].
  by move => H [<-].
Qed.

Import DoNotation.

Instance encodable_tag : @encodable cfi_tag_eqType t := {|
  encode t :=
    match t with
    | USER ut => Word.pack [29; 1] [encode_cfi_tag ut; Word.one]%wp
    | ENTRY ut => Word.pack [29; 1] [encode_cfi_tag ut; Word.repr 2]%wp
    | KERNEL => Word.pack [29; 1] [Word.zero; Word.zero]%wp
    end;

  decode w :=
    let: [ut; w']%wu := Word.unpack [29; 1] w in
    if w' == Word.zero then
      if ut == Word.zero then Some KERNEL
      else None
    else if w' == Word.one then
      do! ut <- decode_cfi_tag ut;
      Some (@USER cfi_tag_eqType ut)
    else if w' == Word.repr 2 then
      do! ut <- decode_cfi_tag ut;
      Some (@ENTRY cfi_tag_eqType ut)
    else None;

  encode_kernel_tag := erefl
|}.
Proof.
  - case => [ut| |ut];
    by rewrite Word.packK /= ?encode_cfi_tagK.
  - intros t w.
    case E: (Word.unpack [29; 1] w) => [ut [w' []]].
    move: (Word.unpackK [29; 1] w). rewrite E.
    have [?|?] := altP (w' =P Word.zero); try subst w'.
    { have [?|?] := altP (ut =P Word.zero); try subst ut; last by [].
      by move => H [<-]. }
    have [?|?] := altP (w' =P Word.one); try subst w'.
    { case DEC: (decode_cfi_tag ut) => [ut'|] //=.
      apply decode_cfi_tagK in DEC. subst ut.
      by move => H [<-]. }
    have [?|?] := altP (w' =P Word.repr 2); try subst w'; last by [].
    case DEC: (decode_cfi_tag ut) => [ut'|] //=.
    apply decode_cfi_tagK in DEC. subst ut.
    by move => H [<-].
Qed.

Section Refinement.

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

End WithClasses.

End CFIInstances.
