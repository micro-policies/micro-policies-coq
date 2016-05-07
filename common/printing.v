Require Import common.types.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import ZArith.
Require Import NPeano.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Import String.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope char_scope.
Open Scope Z_scope.

Definition ascii_of_Z (z : Z) : Ascii.ascii :=
  match z with
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

Open Scope string_scope.

Fixpoint format_Z_aux (fuel : nat) (z : Z) (acc : String.string) : String.string :=
  match fuel with
  | O => acc
  | S fuel' =>
    match Z.div_eucl z 10 with
    | (q, r) =>
      match q with
      | Z0 => String.String (ascii_of_Z r) acc
      | _ => format_Z_aux fuel' q (String.String (ascii_of_Z r) acc)
      end
    end
  end.

Definition format_Z z rest :=
  match z with
  | Z0 => String.append "0" rest
  | Zpos _ => format_Z_aux (S (Z.to_nat (Z.log2 z))) z rest
  | Zneg _ => String.append "-" (format_Z_aux (S (Z.to_nat (Z.log2 z))) (Z.abs z) rest)
  end.

(* ------------------------------------------------------------------- *)
(* Append-list strings *)

Open Scope string_scope.

Definition sstring := string -> string.

Definition ssempty : sstring := fun s => s.

Definition ss (s : string) : sstring :=
  fun s' => s ++ s'.

Definition schar (c : ascii) : sstring :=
  fun s => String c s.

Definition ssappend (s1 s2 : sstring) : sstring :=
  fun s => s1 (s2 s).

Notation "x +++ y" := (ssappend x y) (right associativity, at level 60).

Definition to_string (s : sstring) : string := s "".

Definition ssconcat (sep : sstring) (s : seq sstring) : sstring :=
  foldr (fun rest x => rest +++ sep +++ x) ssempty s.

Definition sspace := ss " ".

(* ------------------------------------------------------------------- *)

Open Scope char_scope.
Open Scope nat_scope.
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
  writeNatAux n n ssempty.

Open Scope string_scope.

Definition format_binop (b : binop) :=
  match b with
   | ADD => ss "ADD"
   | SUB => ss "SUB"
   | MUL => ss "MUL"
   | EQ => ss "EQ"
   | LEQ => ss "LEQ"
   | LEQU => ss "LEQU"
   | AND => ss "AND"
   | OR => ss "OR"
   | XOR => ss "XOR"
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
  end.

Class printing (mt : machine_types) := {
  format_word : mword mt -> sstring;
  format_reg : reg mt -> sstring;
  format_imm : imm mt -> sstring
}.

Section Printing.

Context {mt : machine_types}
        {p : printing mt}.

Definition format_reg_r (r : reg mt) := ss "r" +++ format_reg r.

Definition format_instr (i : instr mt) :=
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
