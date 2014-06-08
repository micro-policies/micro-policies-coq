(* Definition of symbolic rules and tags used for kernel protection,
   along with conversion functions towards concrete integer tags.

   Here are the various kinds of tags we use:

     For the PC:

     - KERNEL          : for kernel mode

     - USER ut is_call : for user mode. [ut] gives the user-level tag,
       while flag [is_call] signals whether we've just executed a JAL,
       for keeping track of system calls.

     For registers:

     - KERNEL : for data only used in the kernel

     - USER ut false : for data only used in user mode, with
       corresponding user-level tag [ut]

     For memory:
     - KERNEL : for kernel space
     - USER [ut] false : similar to above
     - ENTRY : for system call entry points

*)

Require Import Coq.Lists.List Arith Bool.
Require Import Coq.Classes.SetoidDec.

Require Import concrete.common.
Require Import utils Coqlib.
Require Import symbolic.rules.
Require Coq.Vectors.Vector.

Set Implicit Arguments.
Import Coq.Vectors.Vector.VectorNotations.

Section uhandler.

Context {t : machine_types}.
Context {ops : machine_ops t}.

Inductive user_tag : Type :=
| INSTR : option (word t) -> user_tag
| DATA  : user_tag. 

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

Global Instance equ : EqDec (eq_setoid user_tag).
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

Definition tnone := DATA.

Variable valid_jmp : word t -> word t -> bool.

(* Uncertain how we handle syscalls*)
Definition uhandler (umvec : MVec user_tag) : option (RVec user_tag) :=
  match umvec with
  | mkMVec JUMP (INSTR (Some n)) (INSTR (Some m)) _
  | mkMVec JAL (INSTR (Some n)) (INSTR (Some m)) _  =>
    if valid_jmp n m then Some (mkRVec (INSTR (Some m)) DATA)
    else None
  | mkMVec JUMP _ (INSTR (Some n)) _
  | mkMVec JAL _ (INSTR (Some n)) _  => 
    Some (mkRVec (INSTR (Some n)) DATA)
  | mkMVec STORE (INSTR (Some n)) (INSTR (Some m)) [_ ; _ ; DATA] =>
    if valid_jmp n m then Some (mkRVec DATA DATA) else None
  | mkMVec STORE _ (INSTR None) [_ ; _ ; DATA] => Some (mkRVec DATA DATA)
  | mkMVec STORE _ _ _ => None
  | mkMVec _ DATA (INSTR None) _ => Some (mkRVec DATA DATA)
  | mkMVec _ _ _ _ => None
  end.

Definition handler := rules.handler uhandler.

End uhandler.


