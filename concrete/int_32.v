(* Instantiate the machine with 32-bit integers *)

Require Import ZArith.
Require Import Integers.
Require Import List.
Require Import Bool.
Require Import Coq.Classes.SetoidDec.

Import ListNotations.

Require Import FiniteMaps.
Require Import common.
Require Import concrete.
Require Import utils.
Require Import ordered.

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

  Z_to_imm z := repr z;

  imm_to_word i := i;

  zero_word := repr 0;

  max_word := repr max_unsigned;

  Z_to_word i := repr i;

  word_to_Z i := signed i;

  add_word := add;

  opp_word := neg;

  eq_word := _; (* In-scope type class instance *)
  ord_word := _; (* In-scope type class instance *)

  eq_reg := _; (* In-scope type class instance *)

  ra := repr 0

|}.
(* Removing Program causes Coq not to find concrete_int_32_t *)

Import Concrete.

Module Int32PMap := FiniteMap      Int32Indexed.
Module Int32TMap := FiniteTotalMap Int32Indexed.

Let atom := atom (word concrete_int_32_t) (word (concrete_int_32_t)).

Instance concrete_int_32_params : concrete_params concrete_int_32_t := {|
  memory    := Int32PMap.t atom;
  registers := Int32TMap.t atom;

  get_mem mem i   := Int32PMap.get i mem;
  upd_mem mem i x := match Int32PMap.get i mem with
                       | Some _ => Some (Int32PMap.set i x mem)
                       | None   => None
                     end;

  get_reg regs r   := Int32TMap.get r   regs;
  upd_reg regs r x := Int32TMap.set r x regs;

  fault_handler_start := repr 2000;

  TKernel := repr 1;
  TNone := repr 0;

  cache_line_addr := repr 0
|}.

Program Instance concrete_int_32_params_spec :
  params_spec (concrete_int_32_params).
Next Obligation.
  refine ({| PartMaps.eq_key := fun (x y : word concrete_int_32_t) => x == y |}).
  - (* upd_defined *)
    intros mem i x x' Hget.
    rewrite Hget; eauto.
  - (* upd_inv *)
    intros mem i x' mem' Hset.
    destruct (Int32PMap.get i mem); [eauto | discriminate].
  - (* get_upd_eq *)
    intros mem mem' i x Hset.
    destruct (Int32PMap.get i mem); [|discriminate].
    inversion_clear Hset. apply Int32PMap.gss.
  - (* get_upd_neq *)
    intros mem mem' i i' x Hneq Hset.
    destruct (Int32PMap.get i mem); [|discriminate].
    inversion_clear Hset. apply Int32PMap.gso; assumption.
Qed.
Next Obligation.
  constructor.
  - (* get_upd_eq *)
    intros mem i x.
    apply Int32TMap.gss.
  - intros mem i i' x Hneq.
    apply Int32TMap.gso; assumption.
Qed.
