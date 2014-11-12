Require Import Coq.Lists.List Coq.Arith.Arith Bool.
Require Coq.Vectors.Vector.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Require Import lib.utils common.common symbolic.symbolic.
Require Import lib.hlist.
Require Import cfi.classes.

Set Implicit Arguments.
Import HListNotations.
Import Symbolic.

Section uhandler.

Context {t : machine_types}.
Context {ops : machine_ops t}.

Context {ids : @cfi_id t}.

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
Definition cfi_tags : Symbolic.tag_kind -> eqType := fun _ => [eqType of cfi_tag].

Variable cfg : id -> id -> bool.

Definition default_rtag (op : opcode) : type_of_result cfi_tags (outputs op) :=
  match outputs op as o return type_of_result cfi_tags o with
  | Some P => DATA
  | Some R => DATA
  | Some M => DATA
  | None   => tt
  end.

(* This allows loading of instructions as DATA *)
Definition cfi_handler (ivec : Symbolic.IVec cfi_tags) : option (Symbolic.VOVec cfi_tags (Symbolic.op ivec)) :=
  match ivec return option (Symbolic.VOVec cfi_tags (Symbolic.op ivec)) with
  | mkIVec   (JUMP as op) (INSTR (Some n))  (INSTR (Some m))  _
  | mkIVec   (JAL  as op) (INSTR (Some n))  (INSTR (Some m))  _  =>
    if cfg n m then Some (@mkOVec cfi_tags op (INSTR (Some m)) (default_rtag op))
    else None
  | mkIVec   (JUMP as op)  DATA  (INSTR (Some n))  _
  | mkIVec   (JAL  as op)  DATA  (INSTR (Some n))  _   =>
    Some (@mkOVec cfi_tags op (INSTR (Some n)) (default_rtag op))
  | mkIVec   JUMP   DATA  (INSTR None)  _
  | mkIVec   JAL    DATA  (INSTR None)  _  =>
    None
  | mkIVec   STORE  (INSTR (Some n))  (INSTR (Some m))  [hl _ ; _ ; DATA]  =>
    if cfg n m then Some (@mkOVec cfi_tags STORE DATA DATA) else None
  | mkIVec   STORE  DATA  (INSTR _)  [hl _ ; _ ; DATA]  =>
    Some (@mkOVec cfi_tags STORE DATA DATA)
  | mkIVec   STORE  _  _  _  => None
  | mkIVec   (OP op) (INSTR (Some n))  (INSTR (Some m))  _  =>
    (* this includes op = SERVICE *)
    if cfg n m then Some (@mkOVec cfi_tags op DATA (default_rtag op)) else None
  | mkIVec   (OP op) DATA  (INSTR _)  _  =>
    (* this includes op = SERVICE, fall-throughs checked statically *)
    Some (@mkOVec cfi_tags op DATA (default_rtag op))
  | mkIVec   SERVICE (INSTR (Some n)) (INSTR (Some m)) _ =>
    if cfg n m then Some tt else None
  | mkIVec   SERVICE DATA (INSTR _) _ =>
    Some tt
  | mkIVec _ _ _ _ => None
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
