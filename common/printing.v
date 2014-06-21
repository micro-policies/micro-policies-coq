Require Import common.common.
Require Import String.
Require Import Ascii.
Require Import NPeano.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Import common.
Import String.

Set Implicit Arguments.

Open Scope char_scope.
Definition natToDigit (n : nat) : ascii :=
  match n with
    | 0 => "0"
    | 1 => "1"
    | 2 => "2"
    | 3 => "3"
    | 4 => "4"
    | 5 => "5"
    | 6 => "6"
    | 7 => "7"
    | 8 => "8"
    | _ => "9"
  end.

Fixpoint writeNatAux (time n : nat) (acc : string) : string :=
  let acc' := String (natToDigit (n mod 10)) acc in
  match time with
    | 0 => acc'
    | S time' =>
      match n / 10 with
        | 0 => acc'
        | n' => writeNatAux time' n' acc'
      end
  end.

Definition format_nat (n : nat) : string :=
  writeNatAux n n "".

Open Scope string_scope.

Definition format_binop (b : binop) :=
  match b with
   | ADD => "ADD"
   | SUB => "SUB"
   | MUL => "MUL"
   | EQ => "EQ"
   | LEQ => "LEQ"
   | AND => "AND"
   | OR => "OR"
   | SHRU => "SHRU"
   | SHL => "SHL"
  end.

Definition format_opcode (o : opcode) :=
  match o with
   | NOP => "NOP"
   | CONST => "CONST"
   | MOV => "MOV"
   | BINOP b => format_binop b
   | LOAD => "LOAD"
   | STORE => "STORE"
   | JUMP => "JUMP"
   | BNZ => "BNZ"
   | JAL => "JAL"
   | JUMPEPC => "JUMPEPC"
   | ADDRULE => "ADDRULE"
   | GETTAG => "GETTAG"
   | PUTTAG => "PUTTAG"
   | HALT => "HALT"
   | SERVICE => "SERVICE"
  end.

Class printing (t : machine_types) := {
  format_word : word t -> string;
  format_reg : reg t -> string;
  format_imm : imm t -> string
}.

Section Printing.

Context {t : machine_types}
        {p : printing t}.

Definition format_reg_r (r : reg t) := "r" ++ format_reg r.

Definition format_instr (i : instr t) :=
  match i with
  | Nop => "Nop" 
  | Const im r => "Const " ++ format_imm im ++ " " ++ format_reg_r r
  | Mov r1 r2 => "Mov " ++ format_reg_r r1 ++ " " ++ format_reg_r r2
  | Binop b r1 r2 r3 => format_binop b ++ format_reg_r r1 ++ " " ++ format_reg_r r2 ++ " " ++ format_reg_r r3
  | Load r1 r2 => "Load " ++ format_reg_r r1 ++ " " ++ format_reg_r r2
  | Store r1 r2 => "Store " ++ format_reg_r r1 ++ " " ++ format_reg_r r2
  | Jump r1 => "Jump " ++ format_reg_r r1
  | Bnz r im => "Bnz " ++ format_reg_r r ++ " " ++ format_imm im 
  | Jal r1 => "Jal " ++ format_reg_r r1
  | JumpEpc => "JumpEpc" 
  | AddRule => "AddRule" 
  | GetTag r1 r2 => "GetTag " ++ format_reg_r r1 ++ " " ++ format_reg_r r2
  | PutTag r1 r2 r3 => "PutTag  " ++ format_reg_r r1 ++ " " ++ format_reg_r r2 ++ " " ++ format_reg_r r3
  | Halt => "Halt"  
  end.

End Printing.
