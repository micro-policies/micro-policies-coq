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
Require Import ssreflect eqtype ssrnat.
Require Import lib.utils common.common.
Require Import concrete.concrete.
Require Import concrete.int_32.
Require Import sealing.abstract.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import DoNotation.

Module ConcreteSealing.

Section WithClasses.

Definition t := concrete_int_32_t.
Definition ops := concrete_int_32_ops.

Context {scr : @syscall_regs t}.

Definition admit {T: Type} : T.  Admitted.

Instance sk : Abs.sealing_key := {|
  key := [eqType of nat];
  mkkey_f := admit;
  mkkey_fresh := admit
|}.

Instance ap : Abs.abstract_params t := {|
  memory    := Int32PMap.t (Abs.value t);
  registers := Int32PMap.t (Abs.value t);

  am := {|
    PartMaps.get mem i := Int32PMap.get i mem;
    PartMaps.upd mem i x := match Int32PMap.get i mem with
                              | Some _ => Some (Int32PMap.set i x mem)
                              | None   => None
                            end
  |};

  ar := {|
    PartMaps.get regs r := Int32PMap.get r regs;
    PartMaps.upd regs r x := match Int32PMap.get r regs with
                              | Some _ => Some (Int32PMap.set r x regs)
                              | None   => None
                            end
  |}
|}.

Definition build_abstract_sealing_machine :=
  fun user_memory : (word t -> list (word t)) -> 


Definition build_concrete_sealing_machine :=
  fun user_memory : word t -> 

































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
