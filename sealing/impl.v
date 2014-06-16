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
Require Import lib.utils.
Require Import utils common.
(* Require Import concrete.concrete. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import DoNotation.

Module Con.

Section WithClasses.

Context (t : machine_types)
        {ops : machine_ops t}
        {scr : @syscall_regs t}.

Definition admit {T: Type} : T.  Admitted.
Definition concrete_sealing_machine : bool := admit.

End WithClasses.
End Con.
