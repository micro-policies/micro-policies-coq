From mathcomp Require Import
  ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype div ssrint ssralg intdiv.
From CoqUtils Require Import ord word.

Require Import lib.utils.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Warning: extending binop here requires to add corresponding ground rules *)
Inductive binop : predArgType :=
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

Scheme Equality for binop.

Lemma binop_eqP : Equality.axiom binop_beq.
Proof. by do !case; constructor. Qed.

Definition binop_eqMixin := EqMixin binop_eqP.
Canonical binop_eqType := Eval hnf in EqType binop binop_eqMixin.

Definition pickle_binop b :=
  match b with
  | ADD  => 0
  | SUB  => 1
  | MUL  => 2
  | EQ   => 3
  | LEQ  => 4
  | LEQU => 5
  | AND  => 6
  | OR   => 7
  | XOR  => 8
  | SHRU => 9
  | SHL  => 10
  end.

Definition unpickle_binop n :=
  match n with
  | 0  => Some ADD
  | 1  => Some SUB
  | 2  => Some MUL
  | 3  => Some EQ
  | 4  => Some LEQ
  | 5  => Some LEQU
  | 6  => Some AND
  | 7  => Some OR
  | 8  => Some XOR
  | 9  => Some SHRU
  | 10 => Some SHL
  | _  => None
  end.

Lemma pickle_binopK : pcancel pickle_binop unpickle_binop.
Proof. by case. Qed.

Definition binop_choiceMixin := PcanChoiceMixin pickle_binopK.
Canonical binop_choiceType := Eval hnf in ChoiceType binop binop_choiceMixin.
Definition binop_countMixin := CountMixin pickle_binopK.
Canonical binop_countType := Eval hnf in CountType binop binop_countMixin.

Definition binop_enum := [::
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

Lemma binop_enumP : Finite.axiom binop_enum.
Proof. by case. Qed.

Definition binop_finMixin := FinMixin binop_enumP.
Canonical binop_finType := Eval hnf in FinType binop binop_finMixin.

Inductive opcode : predArgType :=
| NOP
| CONST
| MOV
| BINOP of binop
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

Scheme Equality for opcode.

Lemma opcode_eqP : Equality.axiom opcode_beq.
Proof. by do !case; constructor. Qed.

Definition opcode_eqMixin := EqMixin opcode_eqP.
Canonical opcode_eqType := Eval hnf in EqType opcode opcode_eqMixin.

Definition pickle_opcode (o : opcode) : nat :=
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

Definition unpickle_opcode (n : nat) : option opcode :=
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

Lemma pickle_opcodeK : pcancel pickle_opcode unpickle_opcode.
Proof. by do !case. Qed.

Definition opcode_choiceMixin := PcanChoiceMixin pickle_opcodeK.
Canonical opcode_choiceType :=
  Eval hnf in ChoiceType opcode opcode_choiceMixin.
Definition opcode_countMixin := CountMixin pickle_opcodeK.
Canonical opcode_countType := Eval hnf in CountType opcode opcode_countMixin.
Definition opcode_ordMixin := PcanOrdMixin pickle_opcodeK.
Canonical opcode_ordType := Eval hnf in OrdType opcode opcode_ordMixin.

Definition max_opcode := 24.

Lemma max_opcodeP (o : opcode) : pickle o <= max_opcode.
Proof. by move: o; do! case. Qed.

Definition opcode_enum :=
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

Lemma opcode_enumP : Finite.axiom opcode_enum.
Proof. by do !case. Qed.

Definition opcode_finMixin := FinMixin opcode_enumP.
Canonical opcode_finType := Eval hnf in FinType opcode opcode_finMixin.

Inductive vopcode : predArgType :=
| OP : opcode -> vopcode
(* "Virtual" opcode used for describing handlers for system services *)
| SERVICE.

Coercion OP : opcode >-> vopcode.

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

Definition pickle_vopcode (vo : vopcode) : nat :=
  match vo with
  | OP op => pickle op
  | SERVICE => max_opcode + 1
  end.

Definition unpickle_vopcode n :=
  if n == max_opcode + 1 then Some SERVICE
  else omap OP (unpickle n).

Lemma pickle_vopcodeK : pcancel pickle_vopcode unpickle_vopcode.
Proof. by do !case. Qed.

Definition vopcode_choiceMixin := PcanChoiceMixin pickle_vopcodeK.
Canonical vopcode_choiceType :=
  Eval hnf in ChoiceType vopcode vopcode_choiceMixin.
Definition vopcode_countMixin := CountMixin pickle_vopcodeK.
Canonical vopcode_countType :=
  Eval hnf in CountType vopcode vopcode_countMixin.

Definition vopcode_enum := SERVICE :: [seq OP x | x <- enum opcode].

Lemma vopcode_enumP : Finite.axiom vopcode_enum.
Proof.
case => [x|] //=; rewrite count_map /=.
  by rewrite -(@eq_count _ (pred1 x)) // enumT enumP.
by rewrite -(@eq_count _ pred0) // count_pred0.
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
Canonical mword_eqType mt :=
  Eval hnf in EqType (mword mt) [eqMixin of word (word_size mt)].

Definition reg (mt : machine_types) : Type :=
  word (reg_field_size mt).
Arguments reg mt : simpl never.

Definition imm (mt : machine_types) : Type :=
  word (imm_size mt).
Arguments imm mt : simpl never.

Section instr.

Variable mt : machine_types.

Inductive instr : Type :=
| Nop : instr
| Const : imm mt -> reg mt -> instr
| Mov : reg mt -> reg mt -> instr
| Binop : binop -> reg mt -> reg mt -> reg mt -> instr
| Load : reg mt -> reg mt -> instr
| Store : reg mt -> reg mt -> instr
| Jump : reg mt -> instr
| Bnz : reg mt -> imm mt -> instr
| Jal : reg mt -> instr
(* only for the concrete machine: *)
| JumpEpc : instr
| AddRule : instr
| GetTag : reg mt -> reg mt -> instr
| PutTag : reg mt -> reg mt -> reg mt -> instr
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

Class machine_ops (mt : machine_types) := {
  encode_instr : instr mt -> mword mt;
  decode_instr : mword mt -> option (instr mt);

  ra : reg mt
}.

Class machine_ops_spec mt (ops : machine_ops mt) := {

  encodeK : forall i, decode_instr (encode_instr i) = Some i

}.

Lemma max_word_bound mt : (31 < val (monew : mword mt)).
Proof.
have lb : 1 < 2 ^ word_size mt.
  rewrite -{1}(expn0 2) ltn_exp2l //.
  by have := ltn_trans _ (word_size_lb mt); apply.
rewrite -[31]/(2 ^ 5 - 1) /= !modz_nat !absz_nat !modn_mod ?modn_small //;
  try by rewrite subn1 prednK ?expn_gt0 // leqnn.
apply: ltn_sub2r=> //; rewrite ltn_exp2l //.
by have := ltn_trans _ (word_size_lb mt); apply.
Qed.

Section Ops.

Local Open Scope word_scope.

Context {mt : machine_types}
        {op : machine_ops mt}
        {ops : machine_ops_spec op}.

Definition binop_denote (f : binop) : mword mt -> mword mt -> mword mt :=
  match f with
  | ADD => addw
  | SUB => subw
  | MUL => mulw
  | EQ  => fun w1 w2 => as_word (w1 == w2)
  | LEQ => fun w1 w2 => as_word (w1 <= w2)%ord (* FIXME: we don't have signed comparison right now *)
  | LEQU => fun w1 w2 => as_word (w1 <= w2)%ord
  | AND => andw
  | OR => orw
  | XOR => xorw
  | SHRU => addw (* FIXME: we don't have shifts right now *)
  | SHL => shlw
  end.

End Ops.

Section Coding.

Section FixK.

Variable k : nat.
Hypothesis k_ge_5 : 5 <= k.

Definition op_of_word (w : word k) : option opcode :=
  unpickle (val w).

Definition word_of_op (o : opcode) : word k :=
  as_word (pickle o).

Lemma word_of_opK : pcancel word_of_op op_of_word.
Proof.
have lb : 2 ^ 5 <= 2 ^ k by rewrite leq_exp2l //.
do !case=> //=;
by rewrite /word_of_op /op_of_word as_wordK //;
apply: leq_ltn_trans lb.
Qed.

Lemma word_of_op_inj : injective word_of_op.
Proof. by apply (pcan_inj word_of_opK). Qed.

End FixK.

Lemma mword_of_opK mt :
  pcancel (@word_of_op (word_size mt)) (@op_of_word (word_size mt)).
Proof.
by apply: word_of_opK; rewrite (leq_trans _ (word_size_lb mt)).
Qed.

Definition mword_of_op_inj mt := pcan_inj (mword_of_opK mt).

End Coding.

Arguments word_of_op {k} _.
Arguments op_of_word {k} _.

Record atom V T := Atom { vala : V; taga : T }.

Arguments vala {V T} _.
Arguments taga {V T} _.

Definition atom_eqb (V T : eqType) : rel (atom V T) :=
  [rel a1 a2 | [&& vala a1 == vala a2 & taga a1 == taga a2] ].

Lemma atom_eqbP V T : Equality.axiom (@atom_eqb V T).
Proof.
  move => [v1 t1] [v2 t2] /=.
  apply (iffP andP); simpl.
  - by move => [/eqP -> /eqP ->].
  - move => [-> ->]. by rewrite !eqxx.
Qed.

Definition atom_eqMixin V T := EqMixin (@atom_eqbP V T).
Canonical atom_eqType V T := Eval hnf in EqType _ (atom_eqMixin V T).

Notation "x @ t" := (Atom x t) (at level 5, format "x '@' t").

Section SyscallRegs.

Context (mt : machine_types).

Class syscall_regs := {
  syscall_ret  : reg mt;
  syscall_arg1 : reg mt;
  syscall_arg2 : reg mt;
  syscall_arg3 : reg mt
}.

End SyscallRegs.

Arguments syscall_ret  {_ _}.
Arguments syscall_arg1 {_ _}.
Arguments syscall_arg2 {_ _}.
Arguments syscall_arg3 {_ _}.

Ltac current_instr_opcode :=
  match goal with
  | H : decode_instr _ = Some ?instr |- _ =>
    let op := (eval compute in (opcode_of instr)) in
    op
  end.

Ltac failwith m :=
  let op := current_instr_opcode in
  fail 1000 m op.
