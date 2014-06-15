(* Instantiate the machine with 32-bit integers *)

Require Import ZArith.
Require Import Integers.
Require Import List.
Require Import Bool.
Require Import Coq.Classes.SetoidDec.

Import ListNotations.

Require Import Coqlib.
Require Import FiniteMaps.
Require Import common.
Require Import concrete.
Require Import utils.
Require Import lib.ordered.

Import DoNotation.

(* We have to use the same Int module that the maps use. *)
Module Int32Ordered := IntOrdered Wordsize_32.
Module Int32Indexed := Int32Ordered.IntIndexed.
Module Int32        := Int32Indexed.Int.
Import Int32.

(* These types will yield an incorrect (but still executable/useful) encoding *)
(* CH: What's incorrect about it?  Is it the fact that you're
   abusing int instead of using a more precise type? *)
Definition concrete_int_32_t : machine_types := {|
  word := int;
  reg := int; (* 5 bits *)
  imm := int  (* 5 bits; CH: this is extrementy little! *)
|}.

(* CH: x2-x5 are assumed to be all 5 bits,
   and everything more is _silently_ discarded;
   that's very nasty! *)
Definition pack (x1 : opcode) (x2 x3 x4 x5 : int) : int :=
  List.fold_right add (repr 0)
                  [shl (repr (op_to_Z x1)) (repr 20);
                   shl x2 (repr 15);
                   shl x3 (repr 10);
                   shl x4 (repr 5);
                   x5].

Definition mask_31 : int := repr 31.

Definition unpack (x : int) : option (opcode * int * int * int * int) :=
  do opcode <- Z_to_op (unsigned (and (shr x (repr 20)) mask_31));
  Some (opcode,
        and (shr x (repr 15)) mask_31,
        and (shr x (repr 10)) mask_31,
        and (shr x (repr 5)) mask_31,
        and x mask_31).

Program Instance concrete_int_32_ops : machine_ops concrete_int_32_t := {|
  binop_denote b :=
    match b with
    | ADD => add
    | SUB => sub
    | MUL => mul
    | EQ => fun x y => if Z.eqb (unsigned x) (unsigned y) then repr 1
                       else repr 0
    | LEQ => fun x y => if Z.leb (unsigned x) (unsigned y) then repr 1
                        else repr 0
    end;

  encode_instr i :=
    let pack := pack (opcode_of i) in
    match i with
    | Nop => pack zero zero zero zero
    | Const i r => pack i r zero zero
    | Mov r1 r2 => pack r1 r2 zero zero
    | Binop _ r1 r2 r3 => pack r1 r2 r3 zero
    | Load r1 r2 => pack r1 r2 zero zero
    | Store r1 r2 => pack r1 r2 zero zero
    | Jump r => pack r zero zero zero
    | Bnz r i => pack r i zero zero
    | Jal r => pack r zero zero zero
    | JumpEpc => pack zero zero zero zero
    | AddRule => pack zero zero zero zero
    | GetTag r1 r2 => pack r1 r2 zero zero
    | PutTag r1 r2 r3 => pack r1 r2 r3 zero
    end;

  decode_instr i :=
    do t <- unpack i;
    (* Removing the annotation in the match causes this to fail on 8.4pl3 *)
    Some match t : opcode * int * int * int * int with
         | (NOP, _, _, _, _) => Nop _
         | (CONST, i, r, _, _) => Const _ i r
         | (MOV, r1, r2, _, _) => Mov _ r1 r2
         | (BINOP op, r1, r2, r3, _) => Binop _ op r1 r2 r3
         | (LOAD, r1, r2, _, _) => Load _ r1 r2
         | (STORE, r1, r2, _, _) => Store _ r1 r2
         | (JUMP, r, _, _, _) => Jump _ r
         | (BNZ, r, i, _, _) => Bnz _ r i
         | (JAL, r, _, _, _) => Jal _ r
         | (JUMPEPC, _, _, _, _) => JumpEpc _
         | (ADDRULE, _, _, _, _) => AddRule _
         | (GETTAG, r1, r2, _, _) => GetTag _ r1 r2
         | (PUTTAG, r1, r2, r3, _) => PutTag _ r1 r2 r3
         end;

  Z_to_imm := repr;

  imm_to_word i := i;

  min_word := repr min_signed;
  (* ASZ: If this is `max_unsigned`, then `word_to_Z` needs to be `unsigned`,
     but then `opp_word` breaks. *)
  max_word := repr max_signed;

  Z_to_word := repr;

  word_to_Z := signed;

  add_word := add;

  opp_word := neg;

  eq_word := _; (* In-scope type class instance *)
  ord_word := _; (* In-scope type class instance *)

  eq_reg := _; (* In-scope type class instance *)

  ra := repr 0
|}.
(* Removing Program causes Coq not to find concrete_int_32_t *)

Lemma unpack_pack : forall x1 x2 x3 x4 x5,
  unpack (pack x1 x2 x3 x4 x5) = Some (x1,x2,x3,x4,x5).
Proof.
  (* TODO Prove our packing function correct. *)
Admitted.

(* This belongs in CompCert's integers, but alas. *)
Lemma add_repr : forall x y, (add (repr x) (repr y)) = repr (x + y)%Z.
Proof.
  intros. rewrite add_signed. unfold repr,signed; simpl.
  apply mkint_eq. repeat rewrite Z_mod_modulus_eq.
  destruct (zlt (x mod modulus) half_modulus),
           (zlt (y mod modulus) half_modulus).
  - rewrite <- Zplus_mod; reflexivity.
  - replace (x mod modulus + (y mod modulus - modulus))%Z
       with (x mod modulus + y mod modulus - modulus)%Z
         by omega.
    rewrite Zminus_mod, <- Zplus_mod.
    rewrite Z_mod_same_full, Zminus_0_r.
    rewrite Zmod_mod; reflexivity.
  - replace (x mod modulus - modulus + y mod modulus)%Z
       with (x mod modulus + y mod modulus - modulus)%Z
         by omega.
    rewrite Zminus_mod, <- Zplus_mod.
    rewrite Z_mod_same_full, Zminus_0_r.
    rewrite Zmod_mod; reflexivity.
  - replace (x mod modulus - modulus + (y mod modulus - modulus))%Z
       with (x mod modulus + y mod modulus - (2*modulus))%Z
         by omega.
    rewrite Zminus_mod, <- Zplus_mod.
    rewrite Zmult_mod, Z_mod_same_full, Zmult_0_r, Zminus_0_r.
    rewrite Zmod_mod; reflexivity.
Qed.

Lemma compare_signed : forall x y, (x <=> y) = (signed x ?= signed y)%Z.
Proof.
  simpl; intros; unfold Int32Ordered.int_compare,lt.
  destruct (x == y) as [EQ | NE]; [ssubst; auto using Zcompare_refl|].
  destruct (zlt (signed x) (signed y)) as [LT | GE]; [auto with zarith|].
  unfold Zge in GE; destruct (_ ?= _)%Z eqn:CMP.
  + apply Z.compare_eq in CMP.
    destruct x as [x px], y as [y py].
    unfold signed,unsigned in CMP; simpl in CMP.
    destruct (zlt x half_modulus),(zlt y half_modulus); ssubst;
    solve [omega
          | contradict NE; apply mkint_eq; solve [reflexivity | omega]].
  + congruence.
  + reflexivity.
Qed.

Instance concrete_int_32_ops_spec : machine_ops_spec concrete_int_32_ops.
Proof.
  constructor.
  - unfold encode_instr,decode_instr,concrete_int_32_ops;
      intros; destruct i; rewrite unpack_pack; reflexivity.
  - vm_compute; inversion 1.
  - reflexivity.
  - simpl. apply repr_signed.
  - simpl; intros. apply signed_repr. compute -[Zle] in *; omega.
  - exact add_repr.
  - exact neg_repr.
  - exact compare_signed.
  - intros w.
    assert (min_signed <= word_to_Z w) by apply signed_range.
    unfold min_word,word_to_Z,concrete_int_32_ops,le in *.
    rewrite compare_signed,signed_repr by
      (generalize (signed_range (repr 0)); omega).
    assumption.
  - intros w.
    assert (word_to_Z w <= max_signed) by apply signed_range.
    unfold max_word,word_to_Z,concrete_int_32_ops,le in *.
    rewrite compare_signed,signed_repr by
      (generalize (signed_range (repr 0)); omega).
    assumption.
Defined.

Import Concrete.

Module Int32PMap := FiniteMap      Int32Indexed.
Module Int32TMap := FiniteTotalMap Int32Indexed.

Let atom := atom (word concrete_int_32_t) (word (concrete_int_32_t)).

Instance concrete_int_32_params : concrete_params concrete_int_32_t := {|
  memory    := Int32PMap.t atom;
  registers := Int32TMap.t atom;

  mem_class := {|
    PartMaps.get mem i := Int32PMap.get i mem;
    PartMaps.upd mem i x := match Int32PMap.get i mem with
                              | Some _ => Some (Int32PMap.set i x mem)
                              | None   => None
                            end
  |};

  reg_class := {|
    TotalMaps.get regs r := Int32TMap.get r regs;
    TotalMaps.upd regs r x := Int32TMap.set r x regs
  |};

  fault_handler_start := repr 2000;

  TKernel := repr 1;
  TNone := repr 0;

  cache_line_addr := repr 0
|}.

Program Instance concrete_int_32_params_spec :
  params_spec (concrete_int_32_params).
Next Obligation.
  constructor.
  - (* upd_defined *)
    intros mem i x x' Hget. simpl in *.
    rewrite Hget; eauto.
  - (* upd_inv *)
    intros mem i x' mem' Hset. simpl in *.
    destruct (Int32PMap.get i mem); [eauto | discriminate].
  - (* get_upd_eq *)
    intros mem mem' i x Hset. simpl in *.
    destruct (Int32PMap.get i mem); [|discriminate].
    inversion_clear Hset. apply Int32PMap.gss.
  - (* get_upd_neq *)
    intros mem mem' i i' x Hneq Hset. simpl in *.
    destruct (Int32PMap.get i mem); [|discriminate].
    inversion_clear Hset. apply Int32PMap.gso; assumption.
Qed.
Next Obligation.
  constructor.
  - (* get_upd_eq *)
    intros mem i x. simpl in *.
    apply Int32TMap.gss.
  - intros mem i i' x Hneq. simpl in *.
    apply Int32TMap.gso; assumption.
Qed.
