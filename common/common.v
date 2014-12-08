Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
Require Import div.
Require Import word partmap ord.

Require Import lib.utils.

Set Implicit Arguments.

(* Warning: extending binop here requires to add corresponding ground rules *)
Inductive binop :=
| ADD
| SUB
| MUL
| EQ
| LEQ
| LEQU
| AND
| OR
| XOR
| SHRU
| SHL.

Definition binops := [::
  ADD;
  SUB;
  MUL;
  EQ;
  LEQ;
  LEQU;
  AND;
  OR;
  XOR;
  SHRU;
  SHL
  ].

Scheme Equality for binop.

Lemma binop_eqP : Equality.axiom binop_beq.
Proof. by do !case; constructor. Qed.

Definition binop_eqMixin := EqMixin binop_eqP.
Canonical binop_eqType := Eval hnf in EqType binop binop_eqMixin.

Lemma binopsP : forall b : binop, b \in binops.
Proof. by case. Qed.

Inductive opcode : Set :=
| NOP
| CONST
| MOV
| BINOP : binop -> opcode
| LOAD
| STORE
| JUMP
| BNZ
| JAL
| JUMPEPC
| ADDRULE
| GETTAG
| PUTTAG
| HALT.

Inductive vopcode : Set :=
| OP : opcode -> vopcode
(* "Virtual" opcode used for describing handlers for system services *)
| SERVICE.

Coercion OP : opcode >-> vopcode.

Scheme Equality for opcode.

Lemma opcode_eqP : Equality.axiom opcode_beq.
Proof. by do !case; constructor. Qed.

Definition opcode_eqMixin := EqMixin opcode_eqP.
Canonical opcode_eqType := Eval hnf in EqType opcode opcode_eqMixin.

Definition opcodes :=
  [::
   NOP;
   CONST;
   MOV;
   BINOP ADD;
   BINOP SUB;
   BINOP MUL;
   BINOP EQ;
   BINOP LEQ;
   BINOP LEQU;
   BINOP AND;
   BINOP OR;
   BINOP XOR;
   BINOP SHRU;
   BINOP SHL;
   LOAD;
   STORE;
   JUMP;
   BNZ;
   JAL;
   JUMPEPC;
   ADDRULE;
   GETTAG;
   PUTTAG;
   HALT].

Lemma opcodesP : forall op, op \in opcodes.
Proof. by do !case. Qed.

Definition vopcode_eq (x1 x2 : vopcode) : bool :=
  match x1, x2 with
  | OP x1, OP x2 => x1 == x2
  | SERVICE, SERVICE => true
  | _, _ => false
  end.

Lemma vopcode_eqP : Equality.axiom vopcode_eq.
Proof.
  move=> [x1|] [x2|] /=; try by constructor.
  by apply/(iffP idP); [move /eqP ->| move=> [->]].
Qed.

Definition vopcode_eqMixin := EqMixin vopcode_eqP.
Canonical vopcode_eqType := Eval hnf in EqType vopcode vopcode_eqMixin.

Definition vopcodes := SERVICE :: [seq OP x | x <- opcodes].

Lemma vopcodesP x : x \in vopcodes.
Proof.
  case: x => [x|] //=.
  by rewrite inE orFb map_f // opcodesP.
Qed.

Record machine_types := {
  word_size : nat;
  word_size_lb : 7 <= word_size;
  reg_field_size : nat;
  imm_size : nat
}.

Definition mword (mt : machine_types) : Type :=
  word (word_size mt).
Arguments mword mt : simpl never.

Definition reg (mt : machine_types) : Type :=
  word (reg_field_size mt).
Arguments reg mt : simpl never.

Definition imm (mt : machine_types) : Type :=
  word (imm_size mt).
Arguments imm mt : simpl never.

Section instr.

Variable t : machine_types.

Inductive instr : Type :=
| Nop : instr
| Const : imm t -> reg t -> instr
| Mov : reg t -> reg t -> instr
| Binop : binop -> reg t -> reg t -> reg t -> instr
| Load : reg t -> reg t -> instr
| Store : reg t -> reg t -> instr
| Jump : reg t -> instr
| Bnz : reg t -> imm t -> instr
| Jal : reg t -> instr
(* only for the concrete machine: *)
| JumpEpc : instr
| AddRule : instr
| GetTag : reg t -> reg t -> instr
| PutTag : reg t -> reg t -> reg t -> instr
| Halt : instr.

Definition instr_eq (i1 i2 : instr) : bool :=
  match i1, i2 with
  | Nop, Nop => true
  | Const x1 y1, Const x2 y2 => eq_op x1 x2 && eq_op y1 y2
  | Mov x1 y1, Mov x2 y2 => eq_op x1 x2 && eq_op y1 y2
  | Binop o1 x1 y1 z1, Binop o2 x2 y2 z2 =>
    eq_op o1 o2 && eq_op x1 x2 && eq_op y1 y2 && eq_op z1 z2
  | Load x1 y1, Load x2 y2 => eq_op x1 x2 && eq_op y1 y2
  | Store x1 y1, Store x2 y2 => eq_op x1 x2 && eq_op y1 y2
  | Jump x1, Jump x2 => eq_op x1 x2
  | Bnz x1 y1, Bnz x2 y2 => eq_op x1 x2 && eq_op y1 y2
  | Jal x1, Jal x2 => eq_op x1 x2
  | JumpEpc, JumpEpc => true
  | AddRule, AddRule => true
  | GetTag x1 y1, GetTag x2 y2 => eq_op x1 x2 && eq_op y1 y2
  | PutTag x1 y1 z1, PutTag x2 y2 z2 =>
    eq_op x1 x2 && eq_op y1 y2 && eq_op z1 z2
  | Halt, Halt => true
  | _, _ => false
  end.

Lemma instr_eqP : Equality.axiom instr_eq.
Proof.
  move => i1 i2.
  case: i1; case: i2 => /= *; try (by constructor);
  repeat match goal with
  | |- context[?x == ?y] =>
    have [->|/eqP ?] := altP (x =P y); simpl; try constructor; try congruence
  end.
Qed.

Definition instr_eqMixin := EqMixin instr_eqP.
Canonical instr_eqType := Eval hnf in EqType instr instr_eqMixin.

Definition opcode_of (i : instr) : opcode :=
  match i with
  | Nop => NOP
  | Const _ _ => CONST
  | Mov _ _ => MOV
  | Binop op _ _ _ => BINOP op
  | Load _ _ => LOAD
  | Store _ _ => STORE
  | Jump _ => JUMP
  | Bnz _ _ => BNZ
  | Jal _ => JAL
  | JumpEpc => JUMPEPC
  | AddRule => ADDRULE
  | GetTag _ _ => GETTAG
  | PutTag _ _ _ => PUTTAG
  | Halt => HALT
  end.

End instr.

Class machine_ops (t : machine_types) := {
  encode_instr : instr t -> mword t;
  decode_instr : mword t -> option (instr t);

  ra : reg t
}.

Class machine_ops_spec t (ops : machine_ops t) := {

  encodeK : forall i, decode_instr (encode_instr i) = Some i

}.

Lemma max_word_bound t : (31 < val (monew : mword t)).
Proof.
have lb : 1 < 2 ^ word_size t.
  rewrite -{1}(expn0 2) ltn_exp2l //.
  by have := ltn_trans _ (word_size_lb t); apply.
rewrite -[31]/(2 ^ 5 - 1) /= ?modn_small //;
  try by rewrite subn1 prednK ?expn_gt0 // leqnn.
apply: ltn_sub2r=> //; rewrite ltn_exp2l //.
by have := ltn_trans _ (word_size_lb t); apply.
Qed.

Section Ops.

Local Open Scope word_scope.

Context {t : machine_types}
        {op : machine_ops t}
        {ops : machine_ops_spec op}.

Definition bool_to_word (b : bool) : mword t := as_word b.

Definition binop_denote (f : binop) : mword t -> mword t -> mword t :=
  match f with
  | ADD => addw
  | SUB => subw
  | MUL => mulw
  | EQ  => fun w1 w2 => bool_to_word (w1 == w2)
  | LEQ => fun w1 w2 => bool_to_word (w1 <= w2)%ord (* FIXME: we don't have signed comparison right now *)
  | LEQU => fun w1 w2 => bool_to_word (w1 <= w2)%ord
  | AND => andw
  | OR => orw
  | XOR => xorw
  | SHRU => addw (* FIXME: we don't have shifts right now *)
  | SHL => addw
  end.

End Ops.

Section Coding.

Context {t : machine_types}
        {op : machine_ops t}
        {ops : machine_ops_spec op}.

(* this is similar to (but simpler than) decode *)
Definition op_of_nat (n : nat) : option opcode :=
  match n with
  |  1 => Some NOP
  |  2 => Some CONST
  |  3 => Some MOV
  |  4 => Some LOAD
  |  5 => Some STORE
  |  6 => Some JUMP
  |  7 => Some BNZ
  |  8 => Some JAL
  |  9 => Some JUMPEPC
  | 10 => Some ADDRULE
  | 11 => Some GETTAG
  | 12 => Some PUTTAG
  | 13 => Some (BINOP ADD)
  | 14 => Some (BINOP SUB)
  | 15 => Some (BINOP MUL)
  | 16 => Some (BINOP EQ)
  | 17 => Some (BINOP LEQ)
  | 18 => Some (BINOP LEQU)
  | 19 => Some (BINOP AND)
  | 20 => Some (BINOP OR)
  | 21 => Some (BINOP XOR)
  | 22 => Some (BINOP SHRU)
  | 23 => Some (BINOP SHL)
  | 24 => Some HALT
  | _  => None
  end.

Definition nat_of_op (o : opcode) : nat :=
  match o with
  | NOP        =>  1
  | CONST      =>  2
  | MOV        =>  3
  | LOAD       =>  4
  | STORE      =>  5
  | JUMP       =>  6
  | BNZ        =>  7
  | JAL        =>  8
  | JUMPEPC    =>  9
  | ADDRULE    => 10
  | GETTAG     => 11
  | PUTTAG     => 12
  | BINOP ADD  => 13
  | BINOP SUB  => 14
  | BINOP MUL  => 15
  | BINOP EQ   => 16
  | BINOP LEQ  => 17
  | BINOP LEQU => 18
  | BINOP AND  => 19
  | BINOP OR   => 20
  | BINOP XOR  => 21
  | BINOP SHRU => 22
  | BINOP SHL  => 23
  | HALT       => 24
  end.

Definition max_opcode := 24.

Lemma max_opcodeP o : nat_of_op o <= max_opcode.
Proof. by move: o; do! case. Qed.

Lemma nat_of_opK : pcancel nat_of_op op_of_nat.
Proof. by do! case. Qed.

Lemma op_of_natK : ocancel op_of_nat nat_of_op.
Proof. by do !(case=> //). Qed.

Definition nat_of_vop (vo : vopcode) : nat :=
  match vo with
  | OP op => nat_of_op op
  | SERVICE => max_opcode + 1
  end.

Definition op_of_mword (w : mword t) : option opcode :=
  op_of_nat (val w).

Definition mword_of_op (o : opcode) : mword t :=
  as_word (nat_of_op o).

Lemma mword_of_opK : pcancel mword_of_op op_of_mword.
Proof.
have lb : 2 ^ 7 <= 2 ^ word_size t.
  by rewrite leq_exp2l // (word_size_lb t).
do !case=> //=;
by rewrite /mword_of_op /op_of_mword as_wordK ?nat_of_opK //;
apply: leq_ltn_trans lb.
Qed.

Lemma mword_of_op_inj : injective mword_of_op.
Proof. by apply (pcan_inj mword_of_opK). Qed.

End Coding.

Record atom V T := Atom { val : V; tag : T }.

Definition atom_eqb (V T : eqType) : rel (atom V T) :=
  [rel a1 a2 | [&& val a1 == val a2 & tag a1 == tag a2] ].

Lemma atom_eqbP V T : Equality.axiom (atom_eqb V T).
Proof.
  move => [v1 t1] [v2 t2] /=.
  apply (iffP andP); simpl.
  - by move => [/eqP -> /eqP ->].
  - move => [-> ->]. by rewrite !eqxx.
Qed.

Definition atom_eqMixin V T := EqMixin (atom_eqbP V T).
Canonical atom_eqType V T := Eval hnf in EqType _ (atom_eqMixin V T).

Notation "x @ t" := (Atom x t) (at level 5, format "x '@' t").

Section SyscallRegs.

Context {t : machine_types}.

Class syscall_regs := {
  syscall_ret  : reg t;
  syscall_arg1 : reg t;
  syscall_arg2 : reg t;
  syscall_arg3 : reg t
}.

End SyscallRegs.

Section Relocation.

Context {t : machine_types}
        {ops : machine_ops t}.

(* The type of relocatable memory segments.  The first nat specifies
   the segment's size.  The argument type specifies what kind of
   relocation information is needed (e.g., nothing for constant
   segments; just one word for relocatable code; a pair of words for
   relocatable code that also needs access to a shared data area).

   TODO: One issue is that we need the resulting list to always be of
   the specified size, but the type does not demand this at the
   moment.  One way to deal with this is to add a proof component that
   certifies that the resulting list always has the specified length.
   Is there a better way?  (This seems not too bad: our structured
   code combinators can build these certificates pretty easily.) *)

Definition relocatable_segment :=
  fun Args => fun Cell => (nat * (mword t -> Args -> list Cell))%type.

Definition empty_relocatable_segment (Args Cell : Type) : relocatable_segment Args Cell :=
  (0, fun (base : mword t) (rest : Args) => [::]).

(*
Definition concat_relocatable_segments
             (Args Cell : Type)
             (seg1 seg2 : relocatable_segment Args Cell)
           : relocatable_segment Args Cell :=
  let (l1,gen1) := seg1 in
  let (l2,gen2) := seg2 in
  let gen := fun (base : word t) (rest : Args) =>
                  (gen1 base rest)
               ++ (gen2 (add_word base (nat_to_word l1)) rest) in
  (l1+l2, gen).
*)

(* Concatenates list of relocatable segments into one, returning a
   list of offsets (relative to the base address). *)
Definition concat_and_measure_relocatable_segments
             (Args Cell : Type)
             (segs : list (relocatable_segment Args Cell))
           : relocatable_segment Args Cell * list nat :=
  foldl
    (fun (p : relocatable_segment Args Cell * list nat)
         (seg : relocatable_segment Args Cell) =>
       let: (acc,addrs) := p in
       let (l1,gen1) := acc in
       let (l2,gen2) := seg in
       let gen := fun (base : mword t) (rest : Args) =>
                       gen1 base rest
                    ++ gen2 (addw base (as_word l1)) rest in
       let newseg := (l1+l2, gen) in
       (newseg, addrs ++ [:: l1]))
    (empty_relocatable_segment _ _, [::])
    segs.

Definition concat_relocatable_segments
             (Args Cell : Type)
             (segs : list (relocatable_segment Args Cell))
           : relocatable_segment Args Cell :=
  fst (concat_and_measure_relocatable_segments segs).

Definition map_relocatable_segment
             (Args Cell Cell' : Type)
             (f : Cell -> Cell')
             (seg : relocatable_segment Args Cell)
           : relocatable_segment Args Cell' :=
  let (l,gen) := seg in
  let gen' := fun (base : mword t) (rest : Args) => map f (gen base rest) in
  (l, gen').

Definition relocate_ignore_args
             (Args Cell : Type)
             (seg : relocatable_segment unit Cell)
           : relocatable_segment Args Cell :=
  let (l,gen) := seg in
  let gen' := fun (base : mword t) (rest : Args) => gen base tt in
  (l, gen').

End Relocation.

Ltac current_instr_opcode :=
  match goal with
  | H : decode_instr _ = Some ?instr |- _ =>
    let op := (eval compute in (opcode_of instr)) in
    op
  end.
