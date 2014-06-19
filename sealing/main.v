Require Import List. Import ListNotations.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.SetoidDec.
Require Import ssreflect eqtype ssrnat ssrbool.
Require Import lib.utils lib.partial_maps common.common.
Require Import concrete.concrete.
Require Import concrete.int_32.
Require Import symbolic.int_32.
Require Import sealing.symbolic.
Require Import symbolic.fault_handler.
Require Import sealing.abstract.
Require Import concrete.exec.
Require Import Integers.
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
Context {fhp : fault_handler.fault_handler_params t}.

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

(*
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
*)

Instance cp : Concrete.concrete_params t := {|
  memory    := Int32PMap.t atom;
  registers := Int32TMap.t atom;

  mem_class := {|
    PartMaps.get mem i := Int32PMap.get i mem;
    PartMaps.set mem i x := Int32PMap.set i x mem;
    PartMaps.upd mem i x := match Int32PMap.get i mem with
                              | Some _ => Some (Int32PMap.set i x mem)
                              | None   => None
                            end
  |};

  reg_class := {|
    TotalMaps.get regs r := Int32TMap.get r regs;
    (* BCP/MD: Why isn't this called 'set'? *)
    TotalMaps.upd regs r x := Int32TMap.set r x regs
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

(* ---------------------------------------------------------------- *)
(* Code combinators... *)

Definition constant_data l : @relocatable_segment t w atom := 
  (length l, fun _ _ => map (fun x => Atom x Concrete.TKernel) l).

Definition make_code l :=
  map (fun x => Atom (encode_instr x) Concrete.TKernel) l.

Definition constant_code {X} l : @relocatable_segment t X atom := 
  (length l, fun _ _ => make_code l).

(* ---------------------------------------------------------------- *)
(* Main definitions *)

(* Axiom fault_handler : @relocatable_segment t w atom.  *)

Definition transfer_function : list (instr t) :=
  [].
(* TODO *)

Definition fault_handler : @relocatable_segment t w atom :=
  constant_code (handler t ops fhp transfer_function).

Definition extra_state : @relocatable_segment t w atom := 
  constant_data [nat_to_word 0].

Instance sk_defs : Sym.sealing_key := {|
  key := int_eqType;
  max_key := Int32.repr 100;
  inc_key := fun x => Int32.add x (Int32.repr 1);
  ord_key := int_ordered
|}.
Admitted.

Definition encode_sealing_tag (t : Sym.stag) : w := 
  match t with
    Sym.DATA => Z_to_word 0
  | Sym.KEY k => Z_to_word 1     (* TODO FIX *)
  | Sym.SEALED k => Z_to_word 2
  end.

Definition mkkey_segment : @relocatable_segment t w atom :=
  (2, fun _ (extra : w) => make_code [
          (* TODO: too many numeric types! *)
          Const _ (Z_to_imm (word_to_Z extra)) (ri1 t);
          Load _ (ri1 t) (ri2 t);
          (* TODO: More here! *)
          Jump _ (rra t)
          ]).

Definition seal_segment : @relocatable_segment t w atom :=
  (2, fun _ (extra : w) => make_code [
          (* TODO: More here! *)
          Jump _ (rra t)
          ]).

Definition unseal_segment : @relocatable_segment t w atom :=
  (2, fun _ (extra : w) => make_code [
          (* TODO: More here! *)
          Jump _ (rra t)
          ]).

Definition build_concrete_sealing_machine 
     (user_mem : @relocatable_segment t unit atom) 
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
    (encode_sealing_tag Sym.DATA).

Definition hello_world : @relocatable_segment t unit atom :=
  constant_code [
    Const _ (Z_to_imm 2) (ri1 t);
    Binop _ ADD (ri2 t) (ri2 t) (ri3 t)
  ].

Definition trivial_masks : Concrete.Masks :=
  fun _ _ => {|
    Concrete.dc := fun _ => false;
    Concrete.ct := {| Concrete.ct_trpc := None; 
                      Concrete.ct_tr := None |}
  |}.

End WithClasses.

Instance scr : @syscall_regs t := {|
  syscall_ret  := Int32.repr 20;
  syscall_arg1 := Int32.repr 21;
  syscall_arg2 := Int32.repr 22
|}.

(* BCP/MD: There should be some proof obligations about -- at least --
   these being pairwise distinct.  Some axioms must be false
   somewhere! *)
Instance fhp : fault_handler.fault_handler_params t := {|
  rop := Int32.repr 1; 
  rtpc := Int32.repr 2; 
  rti := Int32.repr 3; rt1 := Int32.repr 4; rt2 := Int32.repr 5; 
  rt3 := Int32.repr 6; 
  rb := Int32.repr 7; 
  ri1 := Int32.repr 8; ri2 := Int32.repr 9; ri3 := Int32.repr 10; 
  ri4 := Int32.repr 11; ri5 := Int32.repr 12; 
  rtrpc := Int32.repr 13; rtr := Int32.repr 14; 
  raddr := Int32.repr 15; 
  rra := Int32.repr 16;

  load_const := fun (x : word t) (r : reg t) =>
    [Const _ (Z_to_imm (word_to_Z x)) r]
|}.

(*
Goal exec.step trivial_masks t (build_concrete_sealing_machine hello_world) = None.
*)

(* BCP: One nontrivial issue here.  How do we find out the system call
addresses to use when instantiating the sealing machine?
Answer (roughly)...

Definition build_abstract_sealing_machine :=
  fun user_memory : ...
  let ... := build_concrete_sealing_machine ...
  Instance ...
  ... 
*)

(* TODO: Refinement proof from concrete to abstract instances *)

End ConcreteSealing.
