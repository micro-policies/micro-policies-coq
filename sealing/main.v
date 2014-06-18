Require Import List. Import ListNotations.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.SetoidDec.
Require Import ssreflect eqtype ssrnat ssrbool.
Require Import lib.utils lib.partial_maps common.common.
Require Import concrete.concrete.
Require Import concrete.int_32.
Require Import symbolic.int_32.
Require Import sealing.abstract.
Require Import Omega.

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

Definition max_element (l : list keytype) : keytype :=
  fold_right maxn O l.

Lemma max_element_plus_one_is_distinct :
  forall (l : list keytype),
    ~(In (1 + max_element l) l).
Proof.
  move => l.
  have MAX: forall x, In x l -> x <= max_element l.
  { elim: l => [|x' l IH] // x [-> | THERE] //=.
    - by rewrite leq_max leqnn.
    - by rewrite leq_max IH //= orb_true_r. }
  move => CONTRA.
  move: (MAX _ CONTRA).
  rewrite /addn /addn_rec.
  move/leP => LE.
  omega.
Qed.

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

(* Need to build...

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

Axiom fault_handler : @relocatable_segment t w atom.

Axiom extra_state : @relocatable_segment t w atom.
(* Should be just a single location initially containing 0@TKernel *)

Axiom mkkey_segment : @relocatable_segment t w atom.
Axiom seal_segment : @relocatable_segment t w atom.
Axiom unseal_segment : @relocatable_segment t w atom.

Definition build_concrete_sealing_machine
     (user_mem : @relocatable_segment t unit atom)
     (initial_pc_tag : w)
   : Concrete.state concrete_int_32_t :=
  let syscalls :=
    concat_relocatable_segments
      mkkey_segment
      (concat_relocatable_segments seal_segment unseal_segment) in
  let handler_and_syscalls :=
    concat_relocatable_segments fault_handler syscalls in
  initial_state
    extra_state
    handler_and_syscalls
    (@relocate_ignore_args t w atom user_mem)
    initial_pc_tag.

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
