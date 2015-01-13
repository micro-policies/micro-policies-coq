(* Instantiate the concrete machine with 32-bit integers *)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype ssrint.
Require Import tuple.
Require Import hseq ord word partmap.

Require Import lib.utils.
Require Import common.common common.printing.
Require Import concrete.concrete.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import DoNotation.

Program Definition concrete_int_32_t : machine_types := {|
  word_size := 32;
  reg_field_size := 5;
  imm_size := 15
|}.

Local Notation t := concrete_int_32_t.

Definition encode_opcode (o : opcode) : word 5 :=
  as_word (nat_of_op o).

Definition decode_opcode (o : word 5) : option opcode :=
  op_of_nat (ord_of_word o).

Lemma encode_opcodeK o : decode_opcode (encode_opcode o) = Some o.
Proof. case o; try case; reflexivity. Qed.

Definition fields_of_op op : seq nat :=
  match op with
  | NOP => [:: 27]
  | CONST => [:: 15; 5; 7]
  | MOV => [:: 5; 5; 17]
  | BINOP _ => [:: 5; 5; 5; 12]
  | LOAD => [:: 5; 5; 17]
  | STORE => [:: 5; 5; 17]
  | JUMP => [:: 5; 22]
  | BNZ => [:: 5; 15; 7]
  | JAL => [:: 5; 22]
  | JUMPEPC => [:: 27]
  | ADDRULE => [:: 27]
  | GETTAG => [:: 5; 5; 17]
  | PUTTAG => [:: 5; 5; 5; 12]
  | HALT => [:: 27]
  end.

Lemma fields_of_opP op : sumn (fields_of_op op) = 27.
Proof. by case: op. Qed.

Definition args_of_instr (i : instr t) : hseq word (fields_of_op (opcode_of i)) :=
  match i with
  | Nop => [hseq 0%w]
  | Const i r => [hseq i : word _; r : word _; 0%w]
  | Mov r1 r2 => [hseq r1 : word _; r2 : word _; 0%w]
  | Binop _ r1 r2 r3 => [hseq r1 : word _; r2 : word _; r3 : word _; zerow]
  | Load r1 r2 => [hseq r1 : word _; r2 : word _; 0%w]
  | Store r1 r2 => [hseq r1 : word _; r2 : word _; 0%w]
  | Jump r => [hseq r : word _; 0%w]
  | Bnz r i => [hseq r : word _; i : word _; 0%w]
  | Jal r => [hseq r : word _; 0%w]
  | JumpEpc => [hseq 0%w]
  | AddRule => [hseq 0%w]
  | GetTag r1 r2 => [hseq r1 : word _; r2 : word _; 0%w]
  | PutTag r1 r2 r3 => [hseq r1 : word _; r2 : word _; r3 : word _; 0%w]
  | Halt => [hseq 0%w]
  end.

Definition instr_of_args op : hseq word (fields_of_op op) -> instr t :=
  match op with
  | NOP => fun args => Nop t
  | CONST => fun args => @Const t [hnth args 0] [hnth args 1]
  | MOV => fun args => @Mov t [hnth args 0] [hnth args 1]
  | BINOP b => fun args => @Binop t b [hnth args 0] [hnth args 1] [hnth args 2]
  | LOAD => fun args => @Load t [hnth args 0] [hnth args 1]
  | STORE => fun args => @Store t [hnth args 0] [hnth args 1]
  | JUMP => fun args => @Jump t [hnth args 0]
  | BNZ => fun args => @Bnz t [hnth args 0] [hnth args 1]
  | JAL => fun args => @Jal t [hnth args 0]
  | JUMPEPC => fun args => JumpEpc t
  | ADDRULE => fun args => AddRule t
  | GETTAG => fun args => @GetTag t [hnth args 0] [hnth args 1]
  | PUTTAG => fun args => @PutTag t [hnth args 0] [hnth args 1] [hnth args 2]
  | HALT => fun args => Halt t
  end.

Lemma args_of_instrK i : instr_of_args (args_of_instr i) = i.
Proof.
by case: i => * //=; rewrite /hnth /tnth /=;
do !rewrite ![in X in eq_rect _ _ _ _ X]eq_axiomK /=.
Qed.

Instance concrete_int_32_ops : machine_ops t := {|
  encode_instr i :=
    let op := encode_opcode (opcode_of i) in
    let args : word 27 := wcast (fields_of_opP _) (wpack (args_of_instr i)) in
    @wpack [:: 5; 27] [hseq op; args];

  decode_instr i :=
    let i' := @wunpack [:: 5; 27] i in
    let op := [hnth i' 0] in
    do! op <- decode_opcode op;
    let args := wcast (esym (fields_of_opP op)) [hnth i' 1] in
    Some (instr_of_args (wunpack args));

  ra := zerow

|}.

Instance concrete_int_32_ops_spec : machine_ops_spec concrete_int_32_ops.
Proof.
constructor=> i.
rewrite /decode_instr /encode_instr /= wpackK /hnth /=.
by rewrite encode_opcodeK /= wcastK wpackK args_of_instrK.
Qed.
