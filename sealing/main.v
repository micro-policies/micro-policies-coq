Require Import List. Import ListNotations.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.SetoidDec.
Require Import ssreflect eqtype ssrnat.
Require Import lib.utils lib.partial_maps common.common.
Require Import concrete.concrete.
Require Import concrete.int_32.
Require Import symbolic.int_32.
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

(* BCP: The definition of sk really belongs in abstract.v, I think... *)

Definition keytype := [eqType of nat].

Definition max_element : list keytype -> keytype := admit.

Lemma max_element_plus_one_is_distinct : 
  forall (l : list keytype), 
    ~(In (1 + max_element l) l).
Admitted.

Instance sk : Abs.sealing_key := {|
  key := keytype;
  mkkey_f := fun l => 1 + max_element l;
  mkkey_fresh := max_element_plus_one_is_distinct
|}.

(* Minor: Why do PartMaps.get and PartMaps.set take their arguments in
   a different order from Int32PMap.get and Int32PMap.set?? *)

Instance ap : Abs.params t := {|
  memory    := Int32PMap.t (Abs.value t);
  registers := Int32PMap.t (Abs.value t);

  am := {|
    PartMaps.get mem i := Int32PMap.get i mem;
    PartMaps.set mem i x := Int32PMap.set i x mem;
    PartMaps.upd mem i x := match Int32PMap.get i mem with
                              | Some _ => Some (Int32PMap.set i x mem)
                              | None   => None
                            end
  |};

  ar := {|
    PartMaps.get regs r := Int32PMap.get r regs;
    PartMaps.set mem i x := Int32PMap.set i x mem;
    PartMaps.upd regs r x := match Int32PMap.get r regs with
                              | Some _ => Some (Int32PMap.set r x regs)
                              | None   => None
                            end
  |}
|}.

(* We forgot (in the initial_state function):

   - An initial value for the extra state
   - Relocatable stuff needs to be parameterized on location of extra state

   Need to build...

   - encoding of tags

       DATA      --> 0
       KEY(k)    --> k*2+1 
       SEALED(k) --> k*2+2

   - concrete transfer function (with combinators)

       basically we just check that things are tagged DATA (unless
       they are only being copied around)

   - three system call routines

       MKKEY: increment the extra state and return the old value (as a KEY)

       SEAL: move a tag KEY(k) from one atom to another (currently
       marked DATA, afterwards marked SEAL(k))

       UNSEAL: check that the tag of one arg is KEY(k) and the other
       is SEAL(k) and then change the latter to DATA.

   - fixpoint implementation of concrete step function 
     (with proof of correctness)

*)

Definition build_concrete_sealing_machine :=
  fun user_memory : @relocatable_segment t unit atom =>
  initial_state (* TODO: ... applied to some stuff... ! *).

(*
Definition build_abstract_sealing_machine :=
  fun user_memory : relocatable_mem atom =>
  ... 

BCP: Hmmm -- I see one nontrivial problem looming here.  How do we
     find out the system call addresses to use when instantiating the
     sealing machine?
*)

End WithClasses.
End ConcreteSealing.
