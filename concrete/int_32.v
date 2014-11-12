(* Instantiate the concrete machine with 32-bit integers *)

Require Import ZArith.
Require Import lib.Integers.
Require Import Bool.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Require Import lib.Coqlib.
Require Import lib.FiniteMaps.
Require Import lib.utils.
Require Import lib.partial_maps.
Require Import lib.ordered.
Require Import common.common common.printing.
Require Import concrete.concrete.

Import DoNotation.

Import Word.

Program Definition concrete_int_32_t : machine_types := {|
  word_size_minus_one := 31;
  reg_field_size_minus_one := 4;
  imm_size_minus_one := 14
|}.
Solve Obligations using omega.

Definition encode_opcode (o : opcode) : int 4 :=
  repr (op_to_Z o).

Definition decode_opcode (o : int 4) : option opcode :=
  Z_to_op (unsigned o).

Lemma encode_opcodeK o : decode_opcode (encode_opcode o) = Some o.
Proof.
  case o; try case; reflexivity.
Qed.

Instance concrete_int_32_ops : machine_ops concrete_int_32_t := {|
  encode_instr i :=
    let op := encode_opcode (opcode_of i) in
    match i with
    | Nop => pack [:: 4; 26] [wp op; zero]%w
    | Const i r => pack [:: 4; 14; 4; 6] [wp op; i; r; zero]%w
    | Mov r1 r2 => pack [:: 4; 4; 4; 16] [wp op; r1; r2; zero]%w
    | Binop _ r1 r2 r3 => pack [:: 4; 4; 4; 4; 11] [wp op; r1; r2; r3; zero]%w
    | Load r1 r2 => pack [:: 4; 4; 4; 16] [wp op; r1; r2; zero]%w
    | Store r1 r2 => pack [:: 4; 4; 4; 16] [wp op; r1; r2; zero]%w
    | Jump r => pack [:: 4; 4; 21] [wp op; r; zero]%w
    | Bnz r i => pack [:: 4; 4; 14; 6] [wp op; r; i; zero]%w
    | Jal r => pack [:: 4; 4; 21] [wp op; r; zero]%w
    | JumpEpc => pack [:: 4; 26] [wp op; zero]%w
    | AddRule => pack [:: 4; 26] [wp op; zero]%w
    | GetTag r1 r2 => pack [:: 4; 4; 4; 16] [wp op; r1; r2; zero]%w
    | PutTag r1 r2 r3 => pack [:: 4; 4; 4; 4; 11] [wp op; r1; r2; r3; zero]%w
    | Halt => pack [:: 4; 26] [wp op; zero]%w
    end;

  decode_instr i :=
    let: (op, rest) := @unpack2 4 26 i in
    let t := concrete_int_32_t in
    do! op <- decode_opcode op;
    match op : let int := reg concrete_int_32_t in opcode with
    | NOP => Some (Nop t)
    | CONST => let: [wu i; r; _]%w := unpack [:: 14; 4; 6] rest in
               Some (@Const t i r)
    | MOV => let: [wu r1; r2; _]%w := unpack [:: 4; 4; 16] rest in
             Some (@Mov t r1 r2)
    | BINOP op => let: [wu r1; r2; r3; _]%w := unpack [:: 4; 4; 4; 11] rest in
                  Some (@Binop t op r1 r2 r3)
    | LOAD => let: [wu r1; r2; _]%w := unpack [:: 4; 4; 16] rest in
              Some (@Load t r1 r2)
    | STORE => let: [wu r1; r2; _]%w := unpack [:: 4; 4; 16] rest in
               Some (@Store t r1 r2)
    | JUMP => let : [wu r; _]%w := unpack [:: 4; 21] rest in
              Some (@Jump t r)
    | BNZ => let: [wu r; i; _]%w := unpack [:: 4; 14; 6] rest in
             Some (@Bnz t r i)
    | JAL => let: [wu r; _]%w := unpack [:: 4; 21] rest in
             Some (@Jal t r)
    | JUMPEPC => Some (JumpEpc t)
    | ADDRULE => Some (AddRule t)
    | GETTAG => let: [wu r1; r2; _]%w := unpack [:: 4; 4; 16] rest in
                Some (@GetTag t r1 r2)
    | PUTTAG => let: [wu r1; r2; r3; _]%w := unpack [:: 4; 4; 4; 11] rest in
                Some (@PutTag t r1 r2 r3)
    | HALT => Some (Halt t)
    end;

  ra := repr 0

|}.

Open Scope Z_scope.

Instance concrete_int_32_ops_spec : machine_ops_spec concrete_int_32_ops.
Proof.
  constructor.
  Opaque pack.
  Opaque unpack.
  Opaque unpack2.
  unfold encode_instr,decode_instr,concrete_int_32_ops.
  intros; destruct i; simpl;
  rewrite packU /= pack2K encode_opcodeK /= ?packK //.
  Transparent pack.
  Transparent unpack.
  Transparent unpack2.
Defined.

Import Concrete.

Let atom := atom (word concrete_int_32_t) (word (concrete_int_32_t)).

Open Scope string_scope.
Import printing.

Instance p : printing concrete_int_32_t := {|
  format_word := fun i => format_Z (unsigned i);
  format_reg := fun i => format_Z (unsigned i);
  format_imm := fun i => format_Z (unsigned i)
|}.

Definition format_instr := printing.format_instr.

Open Scope Z_scope.

Require Import String.

(* BCP: all this needs some fixing to live here...

Definition format_atom atom :=
  let: w1@w2 := atom in
    match decode_instr w1 with
      Some i => ss "(" +++ format_instr i +++ ss ")@" +++ format_word w2
    | None => format_word w1 +++ ss "@" +++ format_word w2
    end.

Definition print_instr atom :=
  let: w1@w2 := atom in (Int32.intval w1, decode_instr w1, Int32.intval w2).

Definition print_atom atom :=
  let: w1@w2 := atom in (Int32.intval w1, Int32.intval w2).

Definition format_mvec l :=
  let os := match (Z_to_op (word_to_Z (@Concrete.cop (word concrete_int_32_t) l))) with
              Some o => format_opcode o
            | None => ss "<BAD OPCODE>"
            end in
   os
   +++ sspace +++
   format_word (@Concrete.ctpc (word concrete_int_32_t) l)
   +++ sspace +++
   format_word (@Concrete.cti (word concrete_int_32_t) l)
   +++ sspace +++
   format_word (@Concrete.ct1 (word concrete_int_32_t) l)
   +++ sspace +++
   format_word (@Concrete.ct2 (word concrete_int_32_t) l)
   +++ sspace +++
   format_word (@Concrete.ct3 (word concrete_int_32_t) l).

Definition format_rvec l :=
   format_word (@Concrete.ctrpc (word concrete_int_32_t) l)
   +++ sspace +++
   format_word (@Concrete.ctr (word concrete_int_32_t) l).

Definition format_whole_cache (c : Concrete.rules (word concrete_int_32_t)) :=
  map (fun l => let: (m,r) := l in (format_mvec m +++ ss " => " +++ format_rvec r)) c.

Definition format_cache (c : Concrete.rules (word concrete_int_32_t)) :=
  format_whole_cache (take 3 c).

Require Import Coqlib.

Fixpoint enum (M R S : Type) (map : M) (get : M -> Int32.int -> R) (f : R -> S) (n : nat) (i : Int32.int) :=
  match n with
  | O => []
  | S p => (Int32.intval i, f (get map i)) :: enum map get f p (Int32.add i (Int32.repr 1))
  end.

Definition summarize_concrete_state mem_count cache_count st :=
  let mem' := just_somes
               (@enum _ _ _
                 (@Concrete.mem concrete_int_32_t cp st)
                 (@PartMaps.get _ Int32.int _ _)
                 (@omap atom sstring format_atom)
                 mem_count
                 (Int32.repr 0)) in
  let mem := ssconcat sspace (map (fun x => let: (addr,con) := x in format_Z addr +++ ss ":" +++ con) mem') in
  let regs' := @enum _ _ _
                 (@Concrete.regs concrete_int_32_t cp st)
                 (@TotalMaps.get _ Int32.int _ _)
                 (fun a => format_atom a)
                 (word_to_nat user_reg_max)
                 (Int32.repr (word_to_Z (nat_to_word 0))) in
  let regs := map (fun r =>
                     let: (x,a) := r in
                     ss "r" +++ format_nat (nat_of_Z x) +++ ss "=" +++ a)
               regs' in
  let current_instr :=
    let: addr@_ := Concrete.pc st in
    match @PartMaps.get _ Int32.int _ _
                    (@Concrete.mem t cp st)
                    addr with
      None => ss "(UNDEF ADDR)"
    | Some i => format_atom i
    end in
  (to_string
     (ss "PC=" +++ format_atom (Concrete.pc st) +++ ss "  "
               +++ current_instr +++
      ss " | " +++
      ssconcat sspace regs +++
      ss " | " +++
      mem +++
      ss " | " +++
      ssconcat sspace (format_whole_cache
                         (take cache_count (Concrete.cache st))))).
*)
