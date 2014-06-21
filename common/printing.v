Require Import common.common.
Require Import String.
Require Import Ascii.
Require Import NPeano.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Import common.
Import String.

Set Implicit Arguments.

(* ------------------------------------------------------------------- *)
(* Append-list strings *)

Open Scope string_scope.

Definition sstring := string -> string.

Definition sempty : sstring := fun s => s.

Definition ss (s : string) : sstring := 
  fun s' => s ++ s'.

Definition schar (c : ascii) : sstring := 
  fun s => String c s.

Definition sappend (s1 s2 : sstring) : sstring := 
  fun s => s1 (s2 s).

Notation "x +++ y" := (sappend x y) (right associativity, at level 60).

Definition to_string (s : sstring) : string := s "".

(* ------------------------------------------------------------------- *)

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

Fixpoint writeNatAux (time n : nat) (acc : sstring) : sstring :=
  let acc' := schar (natToDigit (n mod 10)) +++ acc in
  match time with
    | 0 => acc'
    | S time' =>
      match n / 10 with
        | 0 => acc'
        | n' => writeNatAux time' n' acc'
      end
  end.

Definition format_nat (n : nat) : sstring :=
  writeNatAux n n sempty.

Open Scope string_scope.

Definition format_binop (b : binop) :=
  match b with
   | ADD => ss "ADD"
   | SUB => ss "SUB"
   | MUL => ss "MUL"
   | EQ => ss "EQ"
   | LEQ => ss "LEQ"
   | AND => ss "AND"
   | OR => ss "OR"
   | SHRU => ss "SHRU"
   | SHL => ss "SHL"
  end.

Definition format_opcode (o : opcode) :=
  match o with
   | NOP => ss "NOP"
   | CONST => ss "CONST"
   | MOV => ss "MOV"
   | BINOP b => format_binop b
   | LOAD => ss "LOAD"
   | STORE => ss "STORE"
   | JUMP => ss "JUMP"
   | BNZ => ss "BNZ"
   | JAL => ss "JAL"
   | JUMPEPC => ss "JUMPEPC"
   | ADDRULE => ss "ADDRULE"
   | GETTAG => ss "GETTAG"
   | PUTTAG => ss "PUTTAG"
   | HALT => ss "HALT"
   | SERVICE => ss "SERVICE"
  end.

Class printing (t : machine_types) := {
  format_word : word t -> sstring;
  format_reg : reg t -> sstring;
  format_imm : imm t -> sstring
}.

Section Printing.

Context {t : machine_types}
        {p : printing t}.

Definition format_reg_r (r : reg t) := ss "r" +++ format_reg r.

Definition format_instr (i : instr t) :=
  match i with
  | Nop => ss "Nop" 
  | Const im r => ss "Const " +++ format_imm im +++ ss " " +++ format_reg_r r
  | Mov r1 r2 => ss "Mov " +++ format_reg_r r1 +++ ss " " +++ format_reg_r r2
  | Binop b r1 r2 r3 => format_binop b +++ ss " " +++ format_reg_r r1 +++ ss " " 
                        +++ format_reg_r r2 +++ ss " " +++ format_reg_r r3
  | Load r1 r2 => ss "Load " +++ format_reg_r r1 +++ ss " " +++ format_reg_r r2
  | Store r1 r2 => ss "Store " +++ format_reg_r r1 +++ ss " " +++ format_reg_r r2
  | Jump r1 => ss "Jump " +++ format_reg_r r1
  | Bnz r im => ss "Bnz " +++ format_reg_r r +++ ss " " +++ format_imm im 
  | Jal r1 => ss "Jal " +++ format_reg_r r1
  | JumpEpc => ss "JumpEpc" 
  | AddRule => ss "AddRule" 
  | GetTag r1 r2 => ss "GetTag " +++ format_reg_r r1 +++ ss " " +++ format_reg_r r2
  | PutTag r1 r2 r3 => ss "PutTag  " +++ format_reg_r r1 +++ ss " " +++ format_reg_r r2 +++ ss " " +++ format_reg_r r3
  | Halt => ss "Halt"  
  end.

End Printing.
