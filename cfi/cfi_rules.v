Require Import Coq.Lists.List Coq.Arith.Arith Bool.
Require Import Coq.Classes.SetoidDec.
Require Import concrete.common.
Require Import lib.utils.
Require Import symbolic.rules.
Require Coq.Vectors.Vector.

Set Implicit Arguments.
Import Coq.Vectors.Vector.VectorNotations.

Section uhandler.

Context {t : machine_types}.
Context {ops : machine_ops t}.

Inductive cfi_tag : Type :=
| INSTR : option (word t) -> cfi_tag
| DATA  : cfi_tag. 

Program Instance id_eq_eqdec : EqDec (eq_setoid (option (word t))).
Next Obligation.
Proof.
  destruct x,y.
  - assert (DEC:{ w = w0} + {w <> w0}) by (apply eq_word).
    destruct DEC; subst; auto.
    right. unfold complement. intro H; inversion H; auto.
  - right; intros CONTRA. inversion CONTRA.
  - right; unfold complement; intro H; inversion H.
  -  left; reflexivity.
Defined.

Global Instance equ : EqDec (eq_setoid cfi_tag).
  intros t1 t2.
  refine (
      match t1, t2 with
      | INSTR id1, INSTR id2 =>
        match id1 == id2 with
        | left H1 => _
        | _ => _
        end
      | DATA, DATA => left eq_refl
      | _, _ => _
      end
    ); simpl in *; subst; unfold complement in *; auto; right; congruence. 
Defined.

Variable valid_jmp : word t -> word t -> bool.

(* Uncertain how we handle syscalls*)
Definition cfi_handler (umvec : MVec cfi_tag) : option (RVec cfi_tag) :=
  match umvec with
  | mkMVec JUMP (INSTR (Some n)) (INSTR (Some m)) _
  | mkMVec JAL (INSTR (Some n)) (INSTR (Some m)) _  =>
    if valid_jmp n m then Some (mkRVec (INSTR (Some m)) DATA)
    else None
  | mkMVec JUMP DATA (INSTR (Some n)) _
  | mkMVec JAL DATA (INSTR (Some n)) _  => 
    Some (mkRVec (INSTR (Some n)) DATA)
  | mkMVec JUMP DATA (INSTR NONE) _
  | mkMVec JAL DATA (INSTR NONE) _ =>
    None
  | mkMVec STORE (INSTR (Some n)) (INSTR (Some m)) [_ ; _ ; DATA] =>
    if valid_jmp n m then Some (mkRVec DATA DATA) else None
  | mkMVec STORE DATA (INSTR None) [_ ; _ ; DATA] => Some (mkRVec DATA DATA)
  | mkMVec STORE _ _ _ => None
  | mkMVec _ (INSTR (Some n)) (INSTR (Some m)) _ => 
    if valid_jmp n m then Some (mkRVec DATA DATA) else None
  | mkMVec _ DATA (INSTR None) _ => Some (mkRVec DATA DATA)
  | mkMVec _ _ _ _ => None
  end.

End uhandler.


