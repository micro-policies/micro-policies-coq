From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq fintype ssrint.
From extructures Require Import ord fmap.
From CoqUtils Require Import hseq word.

Require Import lib.utils.
Require Import common.types.
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

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module CFIInstances.

Section WithClasses.

(* ---------------------------------------------------------------- *)
(* int32 instance *)

Definition mt := concrete_int_32_mt.
Instance ops : machine_ops mt := concrete_int_32_ops.

Definition id_size := word 28.
Definition id := [eqType of id_size].
Definition bound := 2 ^ 28.

Definition word_to_id (w : mword mt) : option id_size :=
  if ord_of_word w < bound then Some (as_word (ord_of_word w))
  else None.

Definition id_to_word (x : id) : mword mt :=
  as_word (ord_of_word x).

Lemma id_to_wordK : pcancel id_to_word word_to_id.
Proof.
move=> x; rewrite /word_to_id /id_to_word.
have hx := valP (ord_of_word x) : ord_of_word x < bound.
by rewrite !as_wordK ?[in LHS]hx ?valwK ?(ltn_trans hx) /bound ?ltn_exp2l.
Qed.

Lemma word_to_idK : ocancel word_to_id id_to_word.
Proof.
move=> w; rewrite /word_to_id /id_to_word.
have [hb|] // := boolP (_ < 2 ^ 28).
by rewrite [in X in Some X](lock as_word) /= -lock as_wordK // valwK.
Qed.

Instance ids : cfi_id mt := {
 id := id;
 word_to_id := word_to_id;
 id_to_word := id_to_word
}.
Proof.
  - by apply id_to_wordK.
  - by move=> w x h; move: (word_to_idK w); rewrite h.
Defined.

(* Encoding of tags:
      DATA           --> 0
      INSTR None     --> 1
      INSTR (Some x) --> x*4+2
*)

Definition encode_cfi_tag (t : cfi_tag) : word 30 :=
 match t with
   DATA => @wpack [:: 28; 2] [hseq 0; 0]%w
 | INSTR None => @wpack [:: 28; 2] [hseq 0; 1]%w
 | INSTR (Some x) => @wpack [:: 28; 2] [hseq x; as_word 2]%w
 end.

Definition decode_cfi_tag (t : word 30) : option cfi_tag :=
  let: [hseq k; t] := @wunpack [:: 28; 2] t in
  if t == 0%w then
    if k == 0%w then Some DATA
    else None
  else if t == 1%w then
    if k == 0%w then Some (INSTR None)
    else None
  else if t == as_word 2 then
    Some (INSTR (Some (k : @classes.id _ ids)))
  else None.

Lemma encode_cfi_tagK : pcancel encode_cfi_tag decode_cfi_tag.
Proof.
by case=> [[k|]|] /=; rewrite /decode_cfi_tag wpackK.
Qed.

Lemma decode_cfi_tagK : ocancel decode_cfi_tag encode_cfi_tag.
Proof.
move=> w; rewrite /decode_cfi_tag.
case E: (wunpack _) => [k [t []]]; move: E.
have [{t}->|] := altP (t =P _).
  have [{k}->|hk] //= := altP (k =P _).
  by move=> <-; rewrite wunpackK.
have [{t}-> _|] := altP (t =P 1%w).
  have [{k}->|hk] //= := altP (k =P _).
  by move=> <-; rewrite wunpackK.
have [{t}-> _ _|] //= := altP (t =P as_word 2).
by move=> <-; rewrite wunpackK.
Qed.

Import DoNotation.

Instance encodable_tag : encodable mt cfi_tags := {
  decode k m := fun (w : mword mt) =>
    let: [hseq ut; w'] := @wunpack [:: 30; 2] w in
    if w' == 0%w then None
    else
      match k return option (wtag cfi_tags k) with
      | Symbolic.M =>
        if w' == 1%w then
          do! ut <- decode_cfi_tag ut;
          Some (@User cfi_tags ut)
        else if w' == as_word 2 then
          do! ut <- decode_cfi_tag ut;
          Some (@Entry cfi_tags ut)
        else None
      | Symbolic.P =>
        if w' == 1%w then
          do! ut <- decode_cfi_tag ut;
          Some ut
        else None
      | Symbolic.R =>
        if w' == 1%w then
          do! ut <- decode_cfi_tag ut;
          Some ut
        else None
      end
}.
Proof.
  - by eauto.
  - by move=> tk _; rewrite 2!wunpackS.
Qed.

Section Refinement.

Variable cfg : id -> id -> bool.

(* XXX: Removing the explicit argument here causes Coq to throw a
Not_found when closing the Refinement section below, probably a bug to
be reported. *)

Instance sp : Symbolic.params := Sym.sym_cfi cfg.

Variable mi : refinement_common.monitor_invariant.
Variable stable : Symbolic.syscall_table mt.
Variable atable : Abs.syscall_table mt.

Inductive refine_state (ast : Abs.state mt) (cst : Concrete.state mt) : Prop :=
| rs_intro : forall (sst : Symbolic.state mt),
               refinement_common.refine_state mi stable sst cst ->
               RefinementAS.refine_state stable ast sst ->
               refine_state ast cst.
Hint Constructors refine_state.

Hypothesis implementation_correct :
  monitor_code_bwd_correctness mi stable.

Hypothesis refine_syscalls_correct : RefinementAS.refine_syscalls stable atable stable.

Hypothesis syscall_sem :
  forall ac ast ast',
    @Abs.sem mt ac ast = Some ast' ->
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

Hypothesis syscall_preserves_register_tags :
  forall sc st st',
    Sym.registers_tagged (cfg:=cfg) (Symbolic.regs st) ->
    Symbolic.sem sc st = Some st' ->
    Sym.registers_tagged (Symbolic.regs st').

Hypothesis syscall_preserves_jump_tags :
  forall sc st st',
    Sym.jumps_tagged (cfg:=cfg) (Symbolic.mem st) ->
    Symbolic.sem sc st = Some st' ->
    Sym.jumps_tagged (Symbolic.mem st').

Hypothesis syscall_preserves_jal_tags :
  forall sc st st',
    Sym.jals_tagged (cfg:=cfg) (Symbolic.mem st) ->
    Symbolic.sem sc st = Some st' ->
    Sym.jals_tagged (Symbolic.mem st').

Lemma backwards_refinement_as ast sst sst' :
  RefinementAS.refine_state stable ast sst ->
  exec (Symbolic.step stable) sst sst' ->
  exists ast',
    exec (fun ast ast' => Abs.step atable cfg ast ast') ast ast' /\
    RefinementAS.refine_state stable ast' sst'.
Proof.
move => REF EXEC.
elim: EXEC ast REF=> {sst sst'} [sst _|sst sst' sst'' _ STEPS EXEC IH] ast REF.
  by eauto 7.
have [ast' [STEPA REF']] :=
  RefinementAS.backwards_simulation refine_syscalls_correct syscall_sem
                                    syscall_preserves_instruction_tags
                                    syscall_preserves_valid_jmp_tags
                                    syscall_preserves_entry_tags
                                    syscall_preserves_register_tags
                                    syscall_preserves_jump_tags
                                    syscall_preserves_jal_tags
                                    REF STEPS.
by have [ast'' [EXECA REF'']] := IH ast' REF'; eauto 7.
Qed.

Lemma backwards_refinement (ast : Abs.state mt) (cst cst' : Concrete.state mt) :
  refine_state ast cst ->
  exec (Concrete.step _ masks) cst cst' ->
  in_user cst' ->
  exists ast',
    exec (fun ast ast' => Abs.step atable cfg ast ast') ast ast' /\
    refine_state ast' cst'.
Proof.
move => [sst SC AS] EXECC INUSER.
have [sst' EXECS SC'] := backward.backwards_refinement SC EXECC INUSER.
by have [ast' [EXECA AS']] := backwards_refinement_as AS EXECS; eauto.
Qed.

End Refinement.

End WithClasses.

End CFIInstances.
