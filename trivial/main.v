(*
TODO: write better testing support -- e.g. comparing final states
*)

Require Import List. Import ListNotations.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.SetoidDec.
Require Import ssreflect ssrfun eqtype ssrnat ssrbool seq.
Require Import lib.utils lib.partial_maps common.common.
Require Import lib.FiniteMaps lib.ordered.
Require Import concrete.concrete.
Require Import concrete.int_32.
Require Import concrete.exec.
Require Import symbolic.int_32.
Require Import symbolic.symbolic.
Require Import symbolic.exec.
Require Import symbolic.refinement_common.
Require Import symbolic.backward.
Require Import symbolic.rules.
Require Import symbolic.fault_handler.
Require Import trivial.symbolic.
Require Import Integers.
Require Import Omega.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import DoNotation.

Module TrivialInstances.

Section WithClasses.

(* ---------------------------------------------------------------- *)
(* int32 instance *)

Definition t := concrete_int_32_t.
Instance ops : machine_ops t := concrete_int_32_ops.
Instance fhp : fault_handler_params t := concrete_int_32_fh.

(* ---------------------------------------------------------------- *)
(* Generic definitions for building concrete machine instances *)

Definition ruser1 : reg t := Word.repr 20.
Definition ruser2 : reg t := Word.repr 21.
Definition ruser3 : reg t := Word.repr 22.
Definition ruser4 : reg t := Word.repr 23.
Definition user_registers :=
  [:: ra; syscall_ret; syscall_arg1; syscall_arg2; syscall_arg3; ruser1;
      ruser2; ruser3; ruser4].
Definition user_reg_max := last (Word.repr 0) user_registers.

Definition kernel_data {X} l : @relocatable_segment t X w :=
 (length l, fun _ _ => l).

Definition kernel_code {X} l : @relocatable_segment t X w :=
 (length l,
  fun _ _ => map encode_instr l).

(* ---------------------------------------------------------------- *)
(* ---------------------------------------------------------------- *)
(* ---------------------------------------------------------------- *)
(* Main definitions for concrete trivial machine *)

Import Word.Notations.

Ltac inv H := (inversion H; subst; clear H).

Definition encode_trivial_tag (t : Sym.ttag) : Word.int 29 :=
  Word.zero.

Definition decode_trivial_tag (t : Word.int 29) : option Sym.ttag :=
  if t == Word.zero then
    Some (Sym.DUMMY)
  else 
    None.

Lemma encode_trivial_tagK t : decode_trivial_tag (encode_trivial_tag t) = Some t.
Proof.
  unfold decode_trivial_tag, encode_trivial_tag. destruct t;auto.
Qed.

Lemma decode_trivial_tagK w t : decode_trivial_tag w = Some t ->
                                encode_trivial_tag t = w.
Proof.
  unfold decode_trivial_tag, encode_trivial_tag. 
  have [?|?] := altP (w =P Word.zero); try subst w'. auto.
  intro X; inv X. 
Qed.

Instance encodable_tag : @encodable t Sym.ttag_eqType := {|
  encode t :=
    match t with
    | USER ut => Word.pack [29; 1] [encode_trivial_tag ut; Word.one]%wp
    | ENTRY ut => Word.pack [29; 1] [encode_trivial_tag ut; Word.repr 2]%wp
    | KERNEL => Word.pack [29; 1] [Word.zero; Word.zero]%wp
    end;

  decode w :=
    let: [ut; w']%wu := Word.unpack [29; 1] w in
    if w' == Word.zero then
      if ut == Word.zero then Some KERNEL
      else None
    else if w' == Word.one then
      do! ut <- decode_trivial_tag ut;
      Some (@USER Sym.ttag_eqType ut)
    else if w' == Word.repr 2 then
      do! ut <- decode_trivial_tag ut;
      Some (@ENTRY Sym.ttag_eqType ut)
    else None;

  encode_kernel_tag := erefl
|}.
Proof.
  - case => [ut| |ut].
    rewrite Word.packK;  simpl; destruct ut; auto. 
    rewrite Word.packK;  simpl;  auto. 
    rewrite Word.packK;  simpl; destruct ut; auto. 
  - intros t w.
    case E: (Word.unpack [29; 1] w) => [ut [w' []]].
    move: (Word.unpackK [29; 1] w). rewrite E.
    have [?|?] := altP (w' =P Word.zero); try subst w'.
    { have [?|?] := altP (ut =P Word.zero); try subst ut; last by [].
      by move => H [<-]. }
    have [?|?] := altP (w' =P Word.one); try subst w'.
    { case DEC: (decode_trivial_tag ut) => [ut'|] //=.
      apply decode_trivial_tagK in DEC. subst ut.
      by move => H [<-]. }
    have [?|?] := altP (w' =P Word.repr 2); try subst w'; last by [].
    case DEC: (decode_trivial_tag ut) => [ut'|] //=.
    apply decode_trivial_tagK in DEC. subst ut.
    by move => H [<-].
Qed.

Definition DUMMY : word t := Word.repr 0.

Definition transfer_function : list (instr t) :=
 [Const (Word.casts DUMMY) rtrpc;
  Const (Word.casts DUMMY) rtr].

Definition fault_handler : @relocatable_segment t w w :=
 kernel_code (fault_handler.handler t fhp transfer_function).

Definition extra_state : @relocatable_segment t w w :=
 kernel_data [].

Definition gen_syscall_code gen : @relocatable_segment t w w :=
 (length (gen (Word.repr 0) (Word.repr 0)),
  fun b w => map encode_instr (gen b w)).

Definition concrete_trivial_monitor :
  Concrete.memory t * w :=
  let syscalls := [] in
  let res := build_monitor_memory extra_state fault_handler syscalls in
  let monitor_memory := fst (fst res) in
  let user_memory_addr := snd (fst res) in
  (monitor_memory, user_memory_addr).

Definition concrete_trivial_monitor_memory :=
  fst concrete_trivial_monitor.

Definition user_memory_addr :=
  snd concrete_trivial_monitor.

Definition build_concrete_trivial_machine
    (user_program : @relocatable_segment t unit (instr t))
  : Concrete.state concrete_int_32_t
     :=
 (* This list should be defined at the same place as the decoding
    function that splits out the addresses for use when generating
    user code *)
 let user_mem :=
       map_relocatable_segment
         (fun x => Atom (encode_instr x) DUMMY)
         user_program in
 concrete_initial_state
   concrete_trivial_monitor_memory
   user_memory_addr
   tt
   user_mem
   DUMMY
   user_registers
   DUMMY.

(* We need to set up a similar parametric state, but:
   - with concrete handler code in place
   - starting at known handler entry point
   - with epc at parametrized address, but known user tag
   - no user memory: argue that this is strongest (since any reference will die)
   - parameterized user registers (a bit arbitrary)
   - 
  




End WithClasses.

End TrivialInstances.
