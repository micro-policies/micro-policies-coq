Require Import Coq.Lists.List Coq.Arith.Arith Bool.
Require Coq.Vectors.Vector.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Require Import lib.utils common.common symbolic.symbolic.
Require Import cfi.classes.

Set Implicit Arguments.
Import Coq.Vectors.Vector.VectorNotations.
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


Variable cfg : id -> id -> bool.

(* This allows loading of instructions as DATA *)
Definition cfi_handler (umvec : Symbolic.MVec cfi_tag) : option (Symbolic.RVec cfi_tag) :=
  match umvec with
  | mkMVec   JUMP   (INSTR (Some n))  (INSTR (Some m))  _
  | mkMVec   JAL    (INSTR (Some n))  (INSTR (Some m))  _  =>
    if cfg n m then Some (mkRVec (INSTR (Some m)) DATA)
    else None
  | mkMVec   JUMP   DATA  (INSTR (Some n))  _
  | mkMVec   JAL    DATA  (INSTR (Some n))  _   => 
    Some (mkRVec (INSTR (Some n)) DATA)
  | mkMVec   JUMP   DATA  (INSTR None)  _
  | mkMVec   JAL    DATA  (INSTR None)  _  =>
    None
  | mkMVec   STORE  (INSTR (Some n))  (INSTR (Some m))  [_ ; _ ; DATA]  =>
    if cfg n m then Some (mkRVec DATA DATA) else None
  | mkMVec   STORE  DATA  (INSTR _)  [_ ; _ ; DATA]  => 
    Some (mkRVec DATA DATA)
  | mkMVec   STORE  _  _  _  => None
  | mkMVec    _    (INSTR (Some n))  (INSTR (Some m))  _  => 
    (* this includes op = SERVICE *)
    if cfg n m then Some (mkRVec DATA DATA) else None
  | mkMVec    _    DATA  (INSTR _)  _  => 
    (* this includes op = SERVICE, fall-throughs checked statically *)
    Some (mkRVec DATA DATA)
  | mkMVec _ _ _ _ => None
  end.

(* Here is a more readable variant (unused at the moment) *)
(* NG: Found bug in store case*)
(* NG: Found second bug*)
Definition cfi_handler_aux (umvec : MVec cfi_tag) : option (RVec cfi_tag) :=
  match umvec with
  | mkMVec   JUMP   _  (INSTR (Some m))  _
  | mkMVec   JAL    _  (INSTR (Some m))  _  =>
    Some (mkRVec (INSTR (Some m)) DATA)
  | mkMVec JUMP _ _ _
  | mkMVec JAL _ _ _ => None (*jump/jal untagged should get stuck?*)
  | mkMVec   STORE  _  (INSTR _)  [_ ; _ ; t]  =>
    match t with
    | DATA => Some (mkRVec DATA DATA)
    | _    => None
    end
  | mkMVec STORE _ _ _ => None (*This is needed*)
  | mkMVec    _     _  (INSTR _)  _  => 
    Some (mkRVec DATA DATA)
  | mkMVec    _     _  DATA       _ => None
  end.

Definition cfi_handler' (umvec : MVec cfi_tag) : option (RVec cfi_tag) :=
  match tpc umvec, ti umvec with
  | (INSTR (Some n)), INSTR (Some m) =>
    if cfg n m then cfi_handler_aux umvec else None
  | DATA,             INSTR _ =>
    cfi_handler_aux umvec
  | _, _ => None
  end.

Ltac handler_equiv_tac := 
  match goal with
    | [|- match ?Expr with _ => _ end = _] => 
      destruct Expr
    | [|- _ = match ?Expr with _ => _ end] =>
      destruct Expr
    | [|- ?E = ?E] => reflexivity
  end. 

Lemma handlers_equiv umvec :
  cfi_handler umvec = cfi_handler' umvec.
Proof.
  destruct umvec as [op tpc ti ts].
  unfold cfi_handler'.
  destruct tpc as [[n|]|], ti as [[m|]|]; try (destruct op; reflexivity).
  {  destruct op; simpl; destruct (cfg n m); auto;
     repeat handler_equiv_tac.
  }
  { destruct op; simpl; auto; 
    repeat handler_equiv_tac.
  }
  { destruct op; simpl; auto.
    destruct ts. reflexivity.
    destruct ts0. reflexivity.
    destruct ts0. reflexivity.
    destruct h1. destruct ts0; reflexivity.
    destruct ts0; reflexivity.
  }
Qed.
    
End uhandler.
