Require Import Coq.Lists.List Coq.Arith.Arith Bool.
Require Coq.Vectors.Vector.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Require Import concrete.common lib.utils symbolic.rules.

Set Implicit Arguments.
Import Coq.Vectors.Vector.VectorNotations.

Section uhandler.

Context {t : machine_types}.
Context {ops : machine_ops t}.

Inductive cfi_tag : Type :=
| INSTR : option (word t) -> cfi_tag
| DATA  : cfi_tag.


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

Variable valid_jmp : word t -> word t -> bool.

(* Uncertain how we handle syscalls *)
(* This allows loading of instructions as DATA *)
Definition cfi_handler (umvec : MVec cfi_tag) : option (RVec cfi_tag) :=
  match umvec with
  | mkMVec   JUMP   (INSTR (Some n))  (INSTR (Some m))  _
  | mkMVec   JAL    (INSTR (Some n))  (INSTR (Some m))  _  =>
    if valid_jmp n m then Some (mkRVec (INSTR (Some m)) DATA)
    else None
  | mkMVec   JUMP   DATA  (INSTR (Some n))  _
  | mkMVec   JAL    DATA  (INSTR (Some n))  _  => 
    Some (mkRVec (INSTR (Some n)) DATA)
  | mkMVec   JUMP   DATA  (INSTR None)  _
  | mkMVec   JAL    DATA  (INSTR None)  _  =>
    None
  | mkMVec   STORE  (INSTR (Some n))  (INSTR (Some m))  [_ ; _ ; DATA]  =>
    if valid_jmp n m then Some (mkRVec DATA DATA) else None
  | mkMVec   STORE  DATA  (INSTR None)  [_ ; _ ; DATA]  => 
    Some (mkRVec DATA DATA)
  | mkMVec   STORE  _  _  _  => None
  | mkMVec    _    (INSTR (Some n))  (INSTR (Some m))  _  => 
    if valid_jmp n m then Some (mkRVec DATA DATA) else None
  | mkMVec    _    DATA  (INSTR None)  _  => 
    Some (mkRVec DATA DATA)
  | mkMVec _ _ _ _ => None
  end.

(* Here is a more readable variant *)
Definition cfi_handler' (umvec : MVec cfi_tag) : option (RVec cfi_tag) :=
  match umvec with
  | mkMVec   JUMP   _  (INSTR (Some m))  _
  | mkMVec   JAL    _  (INSTR (Some m))  _  =>
    Some (mkRVec (INSTR (Some m)) DATA)
  | mkMVec   STORE  _  (INSTR _)  [_ ; _ ; t]  =>
    match t with
    | DATA => Some (mkRVec DATA DATA)
    | _    => None
    end
  | mkMVec    _     _  (INSTR _)  _  => 
    Some (mkRVec DATA DATA)
  | mkMVec    _     _  DATA       _ => None
  end.

Definition cfi_handler'' (umvec : MVec cfi_tag) : option (RVec cfi_tag) :=
  match tpc umvec, ti umvec with
  | (INSTR (Some n)), INSTR (Some m) =>
    if valid_jmp n m then cfi_handler' umvec else None
  | DATA,             INSTR _ =>
    cfi_handler' umvec
  | _, _ => None
  end.

End uhandler.
