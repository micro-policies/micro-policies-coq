Require Import List Arith ZArith Bool.
Require Import Coq.Classes.SetoidDec.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import lib.ordered.

Require Import lib.utils.
Require Import lib.Integers.
Require Import lib.Maps.
Require Import lib.FiniteMaps.
Require Import lib.partial_maps.

Import ListNotations.

Set Implicit Arguments.

(* Warning: extending binop here requires to add corresponding ground rules *)
Inductive binop :=
| ADD
| SUB
| MUL
| EQ
| LEQ
| AND
| OR
| XOR
| SHRU
| SHL.

Definition binops := [
  ADD;
  SUB;
  MUL;
  EQ;
  LEQ;
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
| HALT
(* "Virtual" opcode used for describing handlers for system services *)
| SERVICE.

Scheme Equality for opcode.

Lemma opcode_eqP : Equality.axiom opcode_beq.
Proof. by do !case; constructor. Qed.

Definition opcode_eqMixin := EqMixin opcode_eqP.
Canonical opcode_eqType := Eval hnf in EqType opcode opcode_eqMixin.

Definition opcodes :=
  [NOP;
   CONST;
   MOV;
   BINOP ADD;
   BINOP SUB;
   BINOP MUL;
   BINOP EQ;
   BINOP LEQ;
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
   HALT;
   SERVICE].

Lemma opcodesP : forall op, op \in opcodes.
Proof. by do !case. Qed.

Record machine_types := {
  word_size_minus_one : nat;
  word_size_lb : (6 <= word_size_minus_one)%coq_nat;
  reg_field_size_minus_one : nat;
  imm_size_minus_one : nat
}.

Definition word (mt : machine_types) : Type :=
  Word.int (word_size_minus_one mt).
Arguments word mt : simpl never.

Definition reg (mt : machine_types) : Type :=
  Word.int (reg_field_size_minus_one mt).
Arguments reg mt : simpl never.

Definition imm (mt : machine_types) : Type :=
  Word.int (imm_size_minus_one mt).
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
  encode_instr : instr t -> word t;
  decode_instr : word t -> option (instr t);

  ra : reg t
}.

Notation "+%w" := Word.add.
Notation "-%w" := Word.neg.
Notation "x + y" := (Word.add x y) : word_scope.
Notation "- x" := (Word.neg x) : word_scope.
Notation "x - y" := (Word.sub x y) : word_scope.
Notation "0" := (Word.zero) : word_scope.
Notation "1" := (Word.one) : word_scope.
Notation "2" := (Word.repr 2) : word_scope.

Delimit Scope word_scope with w.

Class machine_ops_spec t (ops : machine_ops t) := {

  encodeK : forall i, decode_instr (encode_instr i) = Some i

}.

Definition min_word t : word t := Word.repr (Word.min_signed (word_size_minus_one t)).

Definition max_word t : word t := Word.repr (Word.max_signed (word_size_minus_one t)).

Lemma signed_min_word t :
  Word.signed (min_word t) = Word.min_signed (word_size_minus_one t).
Proof.
  rewrite /min_word Word.signed_repr; first by [].
  split; first by omega.
  move: (Word.min_signed_neg (word_size_minus_one t)).
  move: (Word.max_signed_pos (word_size_minus_one t)).
  move => *. omega.
Qed.

Lemma signed_max_word t :
  Word.signed (max_word t) = Word.max_signed (word_size_minus_one t).
Proof.
  rewrite /max_word Word.signed_repr; first by [].
  split; last by omega.
  move: (Word.min_signed_neg (word_size_minus_one t)).
  move: (Word.max_signed_pos (word_size_minus_one t)).
  move => *. omega.
Qed.

Lemma min_word_bound t : (Word.signed (min_word t) <= 0)%Z.
Proof.
rewrite signed_min_word -(Word.signed_zero (word_size_minus_one t)).
apply (proj1 (Word.signed_range _ _)).
Qed.

Lemma max_word_bound t : (31 < Word.signed (max_word t))%Z.
Proof.
rewrite signed_max_word /Word.max_signed Word.half_modulus_power
        /Word.zwordsize /Word.wordsize.
zify. clear H.
case: t => [s Hs ? ?]. simpl.
have ->: (31 = two_p 5 - 1)%Z by [].
suffices: (two_p 5 < two_p (Z.succ (Z.of_nat s) - 1))%Z by (move => ?; omega).
apply Coqlib.two_p_monotone_strict.
omega.
Qed.

Lemma lew_min t (w : word t) : min_word t <= w.
Proof.
rewrite /le IntOrdered.compare_signed signed_min_word.
move: (Word.signed_range _ w) => H1 /Z.compare_gt_iff => H2.
omega.
Qed.

Lemma lew_max t (w : word t) : w <= max_word t.
Proof.
rewrite /le IntOrdered.compare_signed signed_max_word.
move: (Word.signed_range _ w) => H1 /Z.compare_gt_iff => H2.
omega.
Qed.

Section Ops.

Local Open Scope word_scope.

Context {t : machine_types}
        {op : machine_ops t}
        {ops : machine_ops_spec op}.

Definition bool_to_word (b : bool) : word t := if b then 1 else 0.

Definition binop_denote (f : binop) : word t -> word t -> word t :=
  match f with
  | ADD => Word.add
  | SUB => Word.sub
  | MUL => Word.mul
  | EQ  => fun w1 w2 => bool_to_word (w1 == w2)
  | LEQ => fun w1 w2 => bool_to_word (leb w1 w2)
  | AND => Word.and
  | OR => Word.or
  | XOR => Word.xor
  | SHRU => Word.shru
  | SHL => Word.shl
  end.

Lemma addwP : forall x y, (Word.repr x + Word.repr y)%w = (Word.repr (x + y)%Z) :> word t.
Proof. exact: Word.add_repr. Qed.

Lemma oppwP : forall x, (- Word.repr x)%w = Word.repr (- x)%Z :> word t.
Proof. exact: Word.neg_repr. Qed.

Lemma addwA n : associative (@Word.add n).
Proof.
intros x y z.
by rewrite Word.add_assoc.
Qed.

Lemma addwC n : commutative (@Word.add n).
Proof.
intros x y.
apply Word.add_commut.
Qed.

Lemma add0w n : left_id 0 (@Word.add n).
Proof.
exact: Word.add_zero_l.
Qed.

Lemma addNw n : left_inverse 0 (@Word.neg n) +%w.
Proof.
intros x.
by rewrite addwC Word.add_neg_zero.
Qed.

Lemma addw0 n : right_id 0 (@Word.add n).
Proof.
move => x. by rewrite Word.add_zero.
Qed.

Lemma addwN n : right_inverse 0 (@Word.neg n) +%w.
Proof. move => x. now rewrite Word.add_neg_zero. Qed.
Definition subww := addwN.

Lemma addKw n : left_loop (@Word.neg n) +%w.
Proof.
now intros x y; rewrite addwA addNw add0w.
Qed.

Lemma addNKw n : rev_left_loop (@Word.neg n) +%w.
Proof.
now intros x y; rewrite addwA addwN add0w.
Qed.

Lemma addwK n : right_loop (@Word.neg n) +%w.
Proof.
now intros x y; rewrite <-addwA, addwN, addw0.
Qed.

Lemma addwNK n : rev_right_loop (@Word.neg n) +%w.
Proof.
now intros x y; rewrite <-addwA, addNw, addw0.
Qed.

Definition subwK := addwNK.

Lemma addwI n : right_injective (@Word.add n).
Proof. intros x; exact (can_inj (addKw x)). Qed.

Lemma addIw n : left_injective (@Word.add n).
Proof. intros y; exact (can_inj (addwK y)). Qed.

(* If more lemmas are needed, please copy the statements and proofs
from ssralg.v in ssreflect to keep the nice structure. *)

End Ops.

Section WordCompare.

Context {t : machine_types}
        {op : machine_ops t}
        {ops : machine_ops_spec op}.

Local Open Scope Z.
Local Open Scope word_scope.
Local Open Scope ordered.

Local Ltac reflect thm :=
  intros until 0;
  repeat first [ rewrite ltb_lt | rewrite gtb_gt
               | rewrite leb_le | rewrite geb_ge ];
  apply thm.

Local Ltac comparison :=
  intros until 0; unfold lt,gt,le,ge,Zlt,Zgt,Zle,Zge;
  rewrite IntOrdered.compare_signed; split; auto.

Ltac comparison_b :=
  intros; unfold ltb,gtb,leb,geb,Z.ltb,Z.gtb,Z.leb,Z.geb;
  rewrite IntOrdered.compare_signed; destruct (Word.signed _ ?= Word.signed _); reflexivity.

Theorem word_signed_lt : forall n (x y : Word.int n), x <  y <-> (Word.signed x <  Word.signed y)%Z.
Proof. comparison. Qed.

Theorem word_signed_gt : forall n (x y : Word.int n), x >  y <-> (Word.signed x >  Word.signed y)%Z.
Proof. comparison. Qed.

Theorem word_signed_le : forall n (x y : Word.int n), x <= y <-> (Word.signed x <= Word.signed y)%Z.
Proof. comparison. Qed.

Theorem word_signed_ge : forall n (x y : Word.int n), x >= y <-> (Word.signed x >= Word.signed y)%Z.
Proof. comparison. Qed.

Theorem word_signed_ltb : forall n (x y : Word.int n), x <?  y = (Word.signed x <?  Word.signed y)%Z.
Proof. comparison_b. Qed.

Theorem word_signed_gtb : forall n (x y : Word.int n), x >?  y = (Word.signed x >?  Word.signed y)%Z.
Proof. comparison_b. Qed.

Theorem word_signed_leb : forall n (x y : Word.int n), x <=? y = (Word.signed x <=? Word.signed y)%Z.
Proof. comparison_b. Qed.

Theorem word_signed_geb : forall n (x y : Word.int n), x >=? y = (Word.signed x >=? Word.signed y)%Z.
Proof. comparison_b. Qed.

(*
Corollary lew_minmax' : @min_word t <= max_word.
Proof.
  generalize min_word_bound,max_word_bound; rewrite word_signed_le; omega.
Qed.

Corollary lew_minmax : forall w, min_word <= w <= max_word.
Proof. split; [apply lew_min | apply lew_max]. Qed.
*)

(*
Lemma lew_add2l x y z :
  x + y <= x + z <-> y <= z.
Proof.
rewrite !word_signed_le.
rewrite -[x]Word.signedK -{1}[y]Word.signedK -{1}[z]Word.signedK.
rewrite !addwP.
rewrite !Z_to_wordK.
omega.

Qed.
*)

Lemma addwE (x y : word t) :
  (Word.signed (min_word t) <= Word.signed x + Word.signed y <= Word.signed (max_word t))%Z ->
  Word.signed (x + y) = (Word.signed x + Word.signed y)%Z.
Proof.
rewrite signed_min_word signed_max_word.
move => ?.
rewrite -{1}[x]Word.repr_signed -{1}[y]Word.repr_signed.
rewrite addwP.
by rewrite Word.signed_repr.
Qed.

Lemma oppwE (x : word t) :
  (Word.signed (min_word t) <= - Word.signed x <= Word.signed (max_word t))%Z ->
  Word.signed (- x) = (- Word.signed x)%Z.
Proof.
rewrite signed_min_word signed_max_word.
move=> ?.
rewrite -{1}[x]Word.repr_signed.
rewrite oppwP.
by rewrite Word.signed_repr.
Qed.

Lemma subwE (x y : word t) :
(Word.signed (min_word t) <= Word.signed x - Word.signed y <= Word.signed (max_word t))%Z ->
  Word.signed (x - y) = (Word.signed x - Word.signed y)%Z.
Proof.
rewrite signed_min_word signed_max_word.
move=> ?.
rewrite -{1}[x]Word.repr_signed -{1}[y]Word.repr_signed Word.sub_add_opp.
rewrite oppwP addwP.
by rewrite Word.signed_repr.
Qed.

End WordCompare.

Section Coding.

Context {t : machine_types}
        {op : machine_ops t}
        {ops : machine_ops_spec op}.

Local Open Scope Z.

(* this is similar to (but simpler than) decode *)
Definition Z_to_op (z : Z) : option opcode :=
  match z with
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
  | 18 => Some (BINOP AND)
  | 19 => Some (BINOP OR)
  | 20 => Some (BINOP XOR)
  | 21 => Some (BINOP SHRU)
  | 22 => Some (BINOP SHL)
  | 23 => Some HALT
  | 24 => Some SERVICE
  | _  => None
  end.

Definition op_to_Z (o : opcode) : Z :=
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
  | BINOP AND  => 18
  | BINOP OR   => 19
  | BINOP XOR  => 20
  | BINOP SHRU => 21
  | BINOP SHL  => 22
  | HALT       => 23
  | SERVICE    => 24
  end.

Definition max_opcode := 24.

Lemma max_opcodeP o : 0 <= op_to_Z o <= max_opcode.
Proof. by move: o; do! case; split; apply/Z.leb_le. Qed.

Lemma op_to_ZK : pcancel op_to_Z Z_to_op.
Proof. by do! case. Qed.

Lemma Z_to_opK : ocancel Z_to_op op_to_Z.
Proof.
  move => x. rewrite /Z_to_op.
  repeat match goal with
  | |- context[match ?x with _ => _ end] =>
    destruct x; simpl; try reflexivity
  end.
Qed.

Definition word_to_op (w : word t) : option opcode :=
  Z_to_op (Word.unsigned w).

Definition op_to_word (o : opcode) : word t :=
  Word.repr (op_to_Z o).

Lemma op_to_wordK : pcancel op_to_word word_to_op.
Proof.
  unfold pcancel, word_to_op, op_to_word; intros o.
  rewrite Word.unsigned_repr ?op_to_ZK //=.
  move: t (max_opcodeP o) => [s Hs ? ?] /= H.
  rewrite /max_opcode in H.
  have: Word.max_unsigned 5 <= Word.max_unsigned s.
  { rewrite /Word.max_unsigned !Word.modulus_power.
    suffices: two_p (Word.zwordsize 5) <= two_p (Word.zwordsize s) by move => *; omega.
    apply Coqlib.two_p_monotone.
    rewrite /Word.zwordsize /Word.wordsize. zify. omega. }
  have ->: Word.max_unsigned 5 = 63 by [].
  move => ?. omega.
Qed.

Lemma op_to_word_inj : injective op_to_word.
Proof. now apply (pcan_inj op_to_wordK). Qed.

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
  fun Args => fun Cell => (nat * (word t -> Args -> list Cell))%type.

Definition empty_relocatable_segment (Args Cell : Type) : relocatable_segment Args Cell :=
  (0, fun (base : word t) (rest : Args) => []).

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
  fold_left
    (fun (p : relocatable_segment Args Cell * list nat)
         (seg : relocatable_segment Args Cell) =>
       let: (acc,addrs) := p in
       let (l1,gen1) := acc in
       let (l2,gen2) := seg in
       let gen := fun (base : word t) (rest : Args) =>
                       gen1 base rest
                    ++ gen2 (Word.add base (Word.reprn l1)) rest in
       let newseg := (l1+l2, gen) in
       (newseg, addrs ++ [l1]))
    segs
    (empty_relocatable_segment _ _, []).

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
  let gen' := fun (base : word t) (rest : Args) => map f (gen base rest) in
  (l, gen').

Definition relocate_ignore_args
             (Args Cell : Type)
             (seg : relocatable_segment unit Cell)
           : relocatable_segment Args Cell :=
  let (l,gen) := seg in
  let gen' := fun (base : word t) (rest : Args) => gen base tt in
  (l, gen').

End Relocation.

Ltac current_instr_opcode :=
  match goal with
  | H : decode_instr _ = Some ?instr |- _ =>
    let op := (eval compute in (opcode_of instr)) in
    op
  end.

Module ZMap := FiniteMap(ZIndexed).

Instance int_partial_map n : PartMaps.partial_map ZMap.t (Word.int n) := {
  get V m k := ZMap.get (Word.unsigned k) m;
  set V m k v := ZMap.set (Word.unsigned k) v m;
  map_filter V1 V2 f m := ZMap.map_filter f m;
  remove V m k := ZMap.remove (Word.unsigned k) m;
  combine V1 V2 V3 f m1 m2 := ZMap.combine f m1 m2;
  empty V := @ZMap.empty V;
  is_empty V m := m == @ZMap.empty V
}.

Instance int_partial_map_axioms n : PartMaps.axioms (int_partial_map n).
Proof.
  constructor.
  + (* get_set_eq *)
    intros V mem i x. by apply ZMap.gss.
  + (* get_set_neq *)
    intros V mem i i' x H. apply ZMap.gso.
    rewrite <- (Word.repr_unsigned _ i'),
            <- (Word.repr_unsigned _ i) in H.
    congruence.
  + (* map_filter_correctness *)
    intros V1 V2 f m k. by apply ZMap.gmap_filter.
  + (* get_remove_eq *)
    intros V m k. by apply ZMap.grs.
  + (* get_remove_neq *)
    intros V m k k' H. apply ZMap.gro.
    contradict H.
    by apply Word.unsigned_inj.
  + (* get_combine *)
    intros. by apply ZMap.gcombine.
  + (* get_empty *)
    intros V k. by apply ZMap.gempty.
  + (* is_emptyP *)
    intros. exact: eqP.
Qed.

(* XXX: AAA: Weird. for some reason, declaring a global partial map
instance for words causes it to be unfolded when applying simpl, even
when declaring it as "simpl never", which is probably a bug.

We did not encounter the same problem before (I think) because it
occurred at places where the map type class appeared as a parameter,
and not as a concretely defined thing. For now, we just leave this as
opaque. *)

Global Opaque int_partial_map.

Inductive word_map (mt : machine_types) T :=
  WordMap of ZMap.t T.

Let wm mt T (m : word_map mt T) := let (m) := m in m.

Definition word_map_eqb mt (T : eqType) (m1 m2 : word_map mt T) := wm m1 == wm m2.

Lemma word_map_eqbP mt (T : eqType) : Equality.axiom (@word_map_eqb mt T).
Proof.
  move => [m1] [m2] /=.
  apply: (iffP eqP); simpl; try congruence.
Qed.

Definition word_map_eqMixin mt T := EqMixin (@word_map_eqbP mt T).
Canonical word_map_eqType mt T := Eval hnf in EqType _ (@word_map_eqMixin mt T).

Inductive reg_map (mt : machine_types) T :=
  RegMap of ZMap.t T.

Let rm mt T (m : reg_map mt T) := let (m) := m in m.

Definition reg_map_eqb mt (T : eqType) (m1 m2 : reg_map mt T) := rm m1 == rm m2.

Lemma reg_map_eqbP mt (T : eqType) : Equality.axiom (@reg_map_eqb mt T).
Proof.
  move => [m1] [m2] /=.
  apply: (iffP eqP); simpl; try congruence.
Qed.

Definition reg_map_eqMixin mt T := EqMixin (@reg_map_eqbP mt T).
Canonical reg_map_eqType mt T := Eval hnf in EqType _ (@reg_map_eqMixin mt T).

Instance word_map_class (mt : machine_types) : PartMaps.partial_map (word_map mt) (word mt) := {
  get V m k := ZMap.get (Word.unsigned k) (wm m);
  set V m k v := WordMap mt (ZMap.set (Word.unsigned k) v (wm m));
  map_filter V1 V2 f m := WordMap mt (ZMap.map_filter f (wm m));
  remove V m k := WordMap mt (ZMap.remove (Word.unsigned k) (wm m));
  combine V1 V2 V3 f m1 m2 := WordMap mt (ZMap.combine f (wm m1) (wm m2));
  empty V := WordMap mt (@ZMap.empty V);
  is_empty V m := wm m == ZMap.empty V
}.

Instance word_map_axioms (mt : machine_types) : PartMaps.axioms (word_map_class mt).
Proof.
  constructor.
  + (* get_set_eq *)
    intros V mem i x. by apply ZMap.gss.
  + (* get_set_neq *)
    intros V mem i i' x H. apply ZMap.gso.
    rewrite <- (Word.repr_unsigned _ i'),
            <- (Word.repr_unsigned _ i) in H.
    congruence.
  + (* map_filter_correctness *)
    intros V1 V2 f m k. by apply ZMap.gmap_filter.
  + (* get_remove_eq *)
    intros V m k. by apply ZMap.grs.
  + (* get_remove_neq *)
    intros V m k k' H. apply ZMap.gro.
    contradict H.
    by apply Word.unsigned_inj.
  + (* get_combine *)
    intros. by apply ZMap.gcombine.
  + (* get_empty *)
    intros V k. by apply ZMap.gempty.
  + (* is_emptyP *)
    intros. exact: eqP.
Qed.

Instance reg_map_class (mt : machine_types) : PartMaps.partial_map (reg_map mt) (reg mt) := {
  get V m k := ZMap.get (Word.unsigned k) (rm m);
  set V m k v := RegMap mt (ZMap.set (Word.unsigned k) v (rm m));
  map_filter V1 V2 f m := RegMap mt (ZMap.map_filter f (rm m));
  remove V m k := RegMap mt (ZMap.remove (Word.unsigned k) (rm m));
  combine V1 V2 V3 f m1 m2 := RegMap mt (ZMap.combine f (rm m1) (rm m2));
  empty V := RegMap mt (@ZMap.empty V);
  is_empty V m := rm m == ZMap.empty V
}.

Instance reg_map_axioms (mt : machine_types) : PartMaps.axioms (reg_map_class mt).
Proof.
  constructor.
  + (* get_set_eq *)
    intros V mem i x. by apply ZMap.gss.
  + (* get_set_neq *)
    intros V mem i i' x H. apply ZMap.gso.
    rewrite <- (Word.repr_unsigned _ i'),
            <- (Word.repr_unsigned _ i) in H.
    congruence.
  + (* map_filter_correctness *)
    intros V1 V2 f m k. by apply ZMap.gmap_filter.
  + (* get_remove_eq *)
    intros V m k. by apply ZMap.grs.
  + (* get_remove_neq *)
    intros V m k k' H. apply ZMap.gro.
    contradict H.
    by apply Word.unsigned_inj.
  + (* get_combine *)
    intros. by apply ZMap.gcombine.
  + (* get_empty *)
    intros V k. by apply ZMap.gempty.
  + (* is_emptyP *)
    intros. exact: eqP.
Qed.

Global Opaque word_map_class.
Global Opaque reg_map_class.

Module NatPMap := FiniteMap NatIndexed.

Instance nat_partial_map : PartMaps.partial_map NatPMap.t nat := {
  get V m n := NatPMap.get n m;
  set V m n v := NatPMap.set n v m;
  map_filter V1 V2 f m := NatPMap.map_filter f m;
  remove V m k := NatPMap.remove k m;
  combine V1 V2 V3 f m1 m2 := NatPMap.combine f m1 m2;
  empty V := NatPMap.empty _;
  is_empty V m := m == @NatPMap.empty V
}.

Instance nat_partial_map_axioms : PartMaps.axioms nat_partial_map.
Proof.
  constructor.
  - (* get_set_eq *) intros V m n v. by apply NatPMap.gss.
  - (* get_set_neq *) intros V m n1 n2 v. by apply NatPMap.gso.
  - (* map_filter_correctness *) intros V1 V2 f m k. by apply NatPMap.gmap_filter.
  - (* get_remove_eq *)
    intros V m k. by apply NatPMap.grs.
  - (* get_remove_neq *)
    intros V m k k' H. by apply NatPMap.gro.
  - (* get_combine *)
    intros. by apply NatPMap.gcombine.
  - (* get_empty *) intros V k. by apply NatPMap.gempty.
  - (* is_emptyP *) intros. exact: eqP.
Qed.
