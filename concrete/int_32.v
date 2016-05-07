(* Instantiate the concrete machine with 32-bit integers *)

From mathcomp Require Import
  ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype ssrint tuple.
From CoqUtils Require Import hseq ord word partmap.

Require Import lib.utils.
Require Import common.types common.printing.
Require Import concrete.concrete.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import DoNotation.

Program Definition concrete_int_32_mt : machine_types := {|
  word_size := 32;
  reg_field_size := 5;
  imm_size := 15
|}.

Local Notation mt := concrete_int_32_mt.

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

Definition args_of_instr (i : instr mt) : hseq word (fields_of_op (opcode_of i)) :=
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

Definition instr_of_args op : hseq word (fields_of_op op) -> instr mt :=
  match op with
  | NOP => fun args => Nop mt
  | CONST => fun args => @Const mt [hnth args 0] [hnth args 1]
  | MOV => fun args => @Mov mt [hnth args 0] [hnth args 1]
  | BINOP b => fun args => @Binop mt b [hnth args 0] [hnth args 1] [hnth args 2]
  | LOAD => fun args => @Load mt [hnth args 0] [hnth args 1]
  | STORE => fun args => @Store mt [hnth args 0] [hnth args 1]
  | JUMP => fun args => @Jump mt [hnth args 0]
  | BNZ => fun args => @Bnz mt [hnth args 0] [hnth args 1]
  | JAL => fun args => @Jal mt [hnth args 0]
  | JUMPEPC => fun args => JumpEpc mt
  | ADDRULE => fun args => AddRule mt
  | GETTAG => fun args => @GetTag mt [hnth args 0] [hnth args 1]
  | PUTTAG => fun args => @PutTag mt [hnth args 0] [hnth args 1] [hnth args 2]
  | HALT => fun args => Halt mt
  end.

Lemma args_of_instrK i : instr_of_args (args_of_instr i) = i.
Proof.
by case: i => * //=; rewrite /hnth /tnth /=;
do !rewrite ![in X in eq_rect _ _ _ _ X]eq_axiomK /=.
Qed.

Instance concrete_int_32_ops : machine_ops mt := {|
  encode_instr i :=
    let op := word_of_op (opcode_of i) in
    let args : word 27 := wcast (fields_of_opP _) (wpack (args_of_instr i)) in
    @wpack [:: 5; 27] [hseq op; args];

  decode_instr i :=
    let i' := @wunpack [:: 5; 27] i in
    let op := [hnth i' 0] in
    do! op <- op_of_word op;
    let args := wcast (esym (fields_of_opP op)) [hnth i' 1] in
    Some (instr_of_args (wunpack args));

  ra := zerow

|}.

Instance concrete_int_32_ops_spec : machine_ops_spec concrete_int_32_ops.
Proof.
constructor=> i.
rewrite /decode_instr /encode_instr /= wpackK /hnth /=.
by rewrite word_of_opK //= wcastK wpackK args_of_instrK.
Qed.
