(* Here we need to define...

- The concrete transfer function  (use last year's combinators)

- The concrete generation, sealing, and unsealing services

- The encoding function for symbolic tags

- The data needed to instantiate the symbolic machine correctly (entry
  points of the monitor services)
*)

Require Import List. Import ListNotations.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.SetoidDec.
Require Import ssreflect eqtype.
Require Import lib.utils common.common.
Require Import concrete.concrete.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import DoNotation.

Module ConcreteSealing.

Section WithClasses.

Context (t : machine_types)
        {ops : machine_ops t}
        {scr : @syscall_regs t}.

Definition admit {T: Type} : T.  Admitted.

(* We need a constant here that tells application code where to put
   its entry point. *)

(* Most of this belongs in symbolic.v
Definition concrete_sealing_machine : Concrete.state _ := 
  Concrete.mkState
    admit (* memory *)
    admit (* registers *)
    admit (* cache (should get it from symbolic machine!) *)
    admit (* pc *)
    admit (* epc *)
.

(* And then I want to instantiate the symbolic refinement proof
   appropriately so that I get a proof of refinement for this instance of
   the concrete and symbolic machines. *)

*)

End WithClasses.
End ConcreteSealing.
