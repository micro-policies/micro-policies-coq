Require Import List.

Require Import Arith.
Require Import ZArith.
Require Import Bool.
Require Import Coq.Classes.SetoidDec.
Require Import lib.ordered.

Require Import utils.

Import ListNotations.

Set Implicit Arguments.

Inductive binop :=
| ADD
| SUB
| MUL
| EQ.

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
| PUTTAG.

Scheme Equality for opcode.

Definition opcodes :=
  [NOP;
   CONST;
   MOV;
   BINOP ADD;
   BINOP SUB;
   BINOP MUL;
   BINOP EQ;
   LOAD;
   STORE;
   JUMP;
   BNZ;
   JAL;
   JUMPEPC;
   ADDRULE;
   GETTAG;
   PUTTAG].

(* This should be a proof by reflexion... *)
Lemma opcodesP : forall op, In op opcodes.
Proof. intros []; try intros []; vm_compute; auto 17. Qed.

Record machine_types := {
  word : Type;
  reg : Type;
  imm : Type
}.

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
| PutTag : reg t -> reg t -> reg t -> instr.

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
  end.

End instr.

Class machine_ops (t : machine_types) := {
  binop_denote : binop -> word t -> word t -> word t;
  encode_instr : instr t -> word t;
  decode_instr : word t -> option (instr t);

  (* CH: I think it would be nicer to have Z_to_imm be partial *)
  Z_to_imm : Z -> imm t;
  imm_to_word : imm t -> word t;

  (* ASZ: Why is this in the class, rather than a free function defined as
     `Z_to_word 0`? *)
  zero_word : word t;

  (* ASZ: I think we need this to be able to talk about overflow *)
  min_word : word t;
  (* ASZ: Are words signed or unsigned?  Given `opp_word`, I think signed.  (See
     `int_32.v` for why this comes up here.) *)
  max_word : word t;
  (* CH: I think it would be nicer to have Z_to_imm be partial *)
  Z_to_word : Z -> word t;
  word_to_Z : word t -> Z;

  add_word : word t -> word t -> word t;
  opp_word : word t -> word t;
  eq_word  :> EqDec (eq_setoid (word t));
  ord_word :> Ordered (word t);

  eq_reg :> EqDec (eq_setoid (reg t));

  ra : reg t

}.

Notation "x + y" := (add_word x y) : word_scope.
Notation "- x" := (opp_word x) : word_scope.
Notation "x - y" := (add_word x (opp_word y)) : word_scope.
Notation "0" := zero_word : word_scope.
Notation "+%w" := add_word.
Notation "-%w" := opp_word.

Delimit Scope word_scope with w.

(* CH: At some point should prove or at least test that the concrete
   instantiation satisfies these *)
(* ASZ: We now (June 9, 2014) have proofs of everything except decodeK (aka "the
   hard one") for the 32-bit machine in int_32.v.  (There are some sticky
   details with the preconditions for addwP and oppwP; the code in int_32.v
   asserts the commented-out conditions locally, so we know the suggested
   preconditions work.) *)
Class machine_ops_spec t (ops : machine_ops t) := {

  decodeK : forall i, decode_instr (encode_instr i) = Some i;

  (* ASZ: Not sure if this is the right bound to use. *)
  min_word_bound : (word_to_Z min_word <= 0)%Z;
  
  max_word_bound : (15 < word_to_Z max_word)%Z;

  word_to_ZK : forall w, Z_to_word (word_to_Z w) = w;

  Z_to_wordK : forall z,
                 (0 <= z <= word_to_Z max_word)%Z ->
                 word_to_Z (Z_to_word z) = z;

  zerowP : word_to_Z 0%w = 0%Z;

  addwP : forall x y, (Z_to_word x + Z_to_word y)%w = Z_to_word (x + y)%Z;

  oppwP : forall x, (- Z_to_word x)%w = Z_to_word (- x)%Z;

  word_to_Z_compare : forall x y,
    x <=> y = (word_to_Z x ?= word_to_Z y)%Z;
  
  word_to_Z_succ : forall w1 w2,
    w1 < w2 -> word_to_Z (w1 + Z_to_word 1)%w = (word_to_Z w1 + 1)%Z

}.

Section WordArith.

Local Open Scope word_scope.

Context {t : machine_types}
        {op : machine_ops t}
        {ops : machine_ops_spec op}.

Lemma word_to_Z_inj : injective word_to_Z.
Proof. exact (can_inj word_to_ZK). Qed.

Lemma addwA : associative +%w.
Proof.
intros x y z.
rewrite <-(word_to_ZK x), <-(word_to_ZK y), <-(word_to_ZK z), !addwP.
now rewrite Z.add_assoc.
Qed.

Lemma addwC : commutative +%w.
Proof. 
intros x y.
now rewrite <-(word_to_ZK x), <-(word_to_ZK y), !addwP, Z.add_comm.
Qed.

Lemma add0w : left_id 0 +%w.
Proof.
intros x.
now rewrite <-(word_to_ZK x), <-(word_to_ZK 0), zerowP, addwP, Z.add_0_l.
Qed.

Lemma addNw : left_inverse 0 -%w +%w.
Proof.
intros x.
rewrite <-(word_to_ZK x), <-(word_to_ZK 0), zerowP, oppwP, addwP.
now rewrite Z.add_opp_diag_l. (* What a name! *)
Qed.

Lemma addw0 : right_id 0 +%w.
Proof.
intros x.
now rewrite <-(word_to_ZK x), <-(word_to_ZK 0), zerowP, addwP, Z.add_0_r.
Qed.

Lemma addwN : right_inverse 0 -%w +%w.
Proof. now intros x; rewrite addwC, addNw. Qed.
Definition subww := addwN.

Lemma addKw : left_loop -%w +%w.
Proof.
now intros x y; rewrite addwA, addNw, add0w.
Qed.

Lemma addNKw : rev_left_loop -%w +%w.
Proof. 
now intros x y; rewrite addwA, addwN, add0w.
Qed.

Lemma addwK : right_loop -%w +%w.
Proof. 
now intros x y; rewrite <-addwA, addwN, addw0.
Qed.

Lemma addwNK : rev_right_loop -%w +%w.
Proof.
now intros x y; rewrite <-addwA, addNw, addw0.
Qed.

Definition subwK := addwNK.

Lemma addwI : right_injective +%w.
Proof. intros x; exact (can_inj (addKw x)). Qed.

Lemma addIw : left_injective +%w.
Proof. intros y; exact (can_inj (addwK y)). Qed.

(* If more lemmas are needed, please copy the statements and proofs
from ssralg.v in ssreflect to keep the nice structure. *)

End WordArith.

Section Coding.

Context {t : machine_types}
        {op : machine_ops t}
        {ops : machine_ops_spec op}.

Local Open Scope Z.

(* this is similar to (but simpler than) decode *)
Definition Z_to_op (z : Z) : option opcode :=
  match z with
  |  0 => Some NOP
  |  1 => Some CONST
  |  2 => Some MOV
  |  3 => Some LOAD
  |  4 => Some STORE
  |  5 => Some JUMP
  |  6 => Some BNZ
  |  7 => Some JAL
  |  8 => Some JUMPEPC
  |  9 => Some ADDRULE
  | 10 => Some GETTAG
  | 11 => Some PUTTAG
  | 12 => Some (BINOP ADD)
  | 13 => Some (BINOP SUB)
  | 14 => Some (BINOP MUL)
  | 15 => Some (BINOP EQ)
  | _  => None
  end.

Definition op_to_Z (o : opcode) : Z :=
  match o with
  | NOP         =>  0
  | CONST       =>  1
  | MOV         =>  2
  | LOAD     =>  3
  | STORE    =>  4
  | JUMP     =>  5
  | BNZ      =>  6
  | JAL      =>  7
  | JUMPEPC  =>  8
  | ADDRULE  =>  9
  | GETTAG   => 10
  | PUTTAG   => 11
  | BINOP ADD=> 12
  | BINOP SUB=> 13
  | BINOP MUL=> 14
  | BINOP EQ => 15
  end.

Definition word_to_op (w : word t) : option opcode :=
  Z_to_op (word_to_Z w).

Definition op_to_word (o : opcode) : word t :=
  Z_to_word (op_to_Z o).

Lemma op_to_wordK : pcancel op_to_word word_to_op.
Proof.
  unfold pcancel, word_to_op, op_to_word; intros o.
  assert (H := max_word_bound).
  rewrite Z_to_wordK; destruct o; try reflexivity; simpl; try omega;   destruct b; try reflexivity; omega.
Qed.

Lemma word_to_opK : ocancel word_to_op op_to_word.
Proof.
  unfold ocancel, oapp, word_to_op, op_to_word.
  intros o; destruct (Z_to_op (word_to_Z o)) as [o'|] eqn:H; try reflexivity.
  remember (word_to_Z o) as w.
  unfold Z_to_op in H.
  repeat match goal with
  | H : match ?w with _ => _ end = Some _ |- _ =>
    destruct w; try solve [inversion H]
  end;
  match goal with
  | H : Some _ = Some _ |- _ => inversion H; subst; clear H
  end;
  simpl;
  rewrite Heqw;
  apply word_to_ZK.
Qed.

Lemma op_to_word_inj : injective op_to_word.
Proof. now apply (pcan_inj op_to_wordK). Qed.

Definition op_to_imm (o : opcode) : imm t :=
  Z_to_imm (op_to_Z o).

End Coding.

Record atom V T := Atom { val : V; tag : T }.

Notation "x @ t" := (Atom x t) (at level 5, format "x '@' t").

Section WordCompare.

Context {t : machine_types}
        {op : machine_ops t}
        {ops : machine_ops_spec op}.

Local Open Scope Z.
Local Open Scope word_scope.
Local Open Scope ordered.
Local Notation W1 := (Z_to_word 1).

Local Ltac reflect thm :=
  intros until 0;
  repeat first [ rewrite ltb_lt | rewrite gtb_gt
               | rewrite leb_le | rewrite geb_ge ];
  apply thm.

Local Ltac comparison :=
  intros until 0; unfold lt,gt,le,ge,Zlt,Zgt,Zle,Zge;
  rewrite word_to_Z_compare; split; auto.

Ltac comparison_b :=
  intros; unfold ltb,gtb,leb,geb,Z.ltb,Z.gtb,Z.leb,Z.geb;
  rewrite word_to_Z_compare; destruct (word_to_Z _ ?= word_to_Z _); reflexivity.

Theorem word_to_Z_lt : forall x y, x <  y <-> (word_to_Z x <  word_to_Z y)%Z.
Proof. comparison. Qed.

Theorem word_to_Z_gt : forall x y, x >  y <-> (word_to_Z x >  word_to_Z y)%Z.
Proof. comparison. Qed.

Theorem word_to_Z_le : forall x y, x <= y <-> (word_to_Z x <= word_to_Z y)%Z.
Proof. comparison. Qed.

Theorem word_to_Z_ge : forall x y, x >= y <-> (word_to_Z x >= word_to_Z y)%Z.
Proof. comparison. Qed.

Theorem word_to_Z_ltb : forall x y, x <?  y = (word_to_Z x <?  word_to_Z y)%Z.
Proof. comparison_b. Qed.

Theorem word_to_Z_gtb : forall x y, x >?  y = (word_to_Z x >?  word_to_Z y)%Z.
Proof. comparison_b. Qed.

Theorem word_to_Z_leb : forall x y, x <=? y = (word_to_Z x <=? word_to_Z y)%Z.
Proof. comparison_b. Qed.

Theorem word_to_Z_geb : forall x y, x >=? y = (word_to_Z x >=? word_to_Z y)%Z.
Proof. comparison_b. Qed.

(* The x < y constraint in theormes guarantees that x is not INT_MAX. *)

Theorem word_succ_le_lt : forall x y, x < y -> x + W1 <= y.
Proof.
 intros; erewrite word_to_Z_le, word_to_Z_succ by eassumption.
 rewrite word_to_Z_lt in *; omega.
Qed.

Theorem word_succ_leb_ltb : forall x y, x <? y = true -> x + W1 <=? y = true.
Proof. reflect word_succ_le_lt. Qed.

Theorem word_succ_lt_bounded : forall x y,
  x < y -> x < x + W1.
Proof.
  intros; erewrite word_to_Z_lt, word_to_Z_succ by eassumption; omega.
Qed.

Theorem word_succ_ltb_bounded : forall x y,
  x <? y = true -> x <? x + W1 = true.
Proof. reflect word_succ_lt_bounded. Qed.

End WordCompare.
