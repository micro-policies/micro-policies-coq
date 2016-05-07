From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From CoqUtils Require Import hseq.

Require Import lib.utils common.types symbolic.symbolic.
Require Import cfi.classes.

Import Symbolic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section uhandler.

Context {mt : machine_types}.
Context {ops : machine_ops mt}.

Context {ids : cfi_id mt}.

Inductive cfi_tag : Type :=
| INSTR : option id -> cfi_tag
| DATA  : cfi_tag.

Definition get_id tg :=
  match tg with
    | DATA
    | INSTR None => None
    | INSTR x => x
  end.

Definition cfi_tag_eq t1 t2 :=
  match t1, t2 with
    | INSTR id1, INSTR id2 => id1 == id2
    | DATA, DATA => true
    | _, _ => false
  end.

Lemma cfi_tag_eqP : Equality.axiom cfi_tag_eq.
Proof.
by move=> [w1|] [w2|] /=; apply: (iffP idP) => // [/eqP->|[->]].
Qed.

Definition cfi_tag_eqMixin := EqMixin cfi_tag_eqP.
Canonical cfi_tag_eqType := Eval hnf in EqType cfi_tag cfi_tag_eqMixin.

(* XXX: Refine this later to use different types *)
Definition cfi_tags := {|
  Symbolic.pc_tag_type := [eqType of cfi_tag];
  Symbolic.reg_tag_type := [eqType of cfi_tag];
  Symbolic.mem_tag_type := [eqType of cfi_tag];
  Symbolic.entry_tag_type := [eqType of cfi_tag]
|}.

Variable cfg : id -> id -> bool.

Definition default_rtag (op : opcode) : type_of_result cfi_tags (outputs op) :=
  match outputs op as o return type_of_result cfi_tags o with
  | Some P => DATA
  | Some R => DATA
  | Some M => DATA
  | None   => tt
  end.

(* This allows loading of instructions as DATA *)
Definition cfi_handler (ivec : Symbolic.ivec cfi_tags) : option (Symbolic.vovec cfi_tags (Symbolic.op ivec)) :=
  match ivec return option (Symbolic.vovec cfi_tags (Symbolic.op ivec)) with
  | IVec   (JUMP as op) (INSTR (Some n))  (INSTR (Some m))  _
  | IVec   (JAL  as op) (INSTR (Some n))  (INSTR (Some m))  _  =>
    if cfg n m then Some (@OVec cfi_tags op (INSTR (Some m)) (default_rtag op))
    else None
  | IVec   (JUMP as op)  DATA  (INSTR (Some n))  _
  | IVec   (JAL  as op)  DATA  (INSTR (Some n))  _   =>
    Some (@OVec cfi_tags op (INSTR (Some n)) (default_rtag op))
  | IVec   JUMP   DATA  (INSTR None)  _
  | IVec   JAL    DATA  (INSTR None)  _  =>
    None
  | IVec   STORE  (INSTR (Some n))  (INSTR (Some m))  [hseq _ ; _ ; DATA]  =>
    if cfg n m then Some (@OVec cfi_tags STORE DATA DATA) else None
  | IVec   STORE  DATA  (INSTR _)  [hseq _ ; _ ; DATA]  =>
    Some (@OVec cfi_tags STORE DATA DATA)
  | IVec   STORE  _  _  _  => None
  | IVec   (OP op) (INSTR (Some n))  (INSTR (Some m))  _  =>
    (* this includes op = SERVICE *)
    if cfg n m then Some (@OVec cfi_tags op DATA (default_rtag op)) else None
  | IVec   (OP op) DATA  (INSTR _)  _  =>
    (* this includes op = SERVICE, fall-throughs checked statically *)
    Some (@OVec cfi_tags op DATA (default_rtag op))
  | IVec   SERVICE (INSTR (Some n)) (INSTR (Some m)) _ =>
    if cfg n m then Some tt else None
  | IVec   SERVICE DATA (INSTR _) _ =>
    Some tt
  | IVec _ _ _ _ => None
  end.

Ltac handler_equiv_tac :=
  match goal with
    | [|- match ?Expr with _ => _ end = _] =>
      destruct Expr
    | [|- _ = match ?Expr with _ => _ end] =>
      destruct Expr
    | [|- ?E = ?E] => reflexivity
  end.

End uhandler.
