(* Specializing protected kernel to 32-bit machine *)

Require Import ZArith.
Require Import Integers.
Require Import List.
Require Import Bool.

Import ListNotations.

Require Import lib.FiniteMaps.
Require Import lib.utils.
Require Import concrete.common.
Require Import concrete.concrete.
Require Import concrete.int_32.

Require Import kernel.rules.
Require Import kernel.fault_handler.

Import DoNotation.
Import Int32.
Import Concrete.

Instance concrete_int_32_fh : fault_handler_params concrete_int_32_t := {
  rop := repr 1;
  rtpc := repr 2;
  rti := repr 3;
  rt1 := repr 4;
  rt2 := repr 5;
  rt3 := repr 6;
  rb := repr 7;
  ri := repr 8;
  rtrpc := repr 9;
  rtr := repr 10;
  raddr := repr 11;
  eq_code r1 r2 r3 := [Binop concrete_int_32_t BEq r1 r2 r3];

  (* WARNING: This doesn't quite work in the general case, because imm
     should be strictly smaller than word. However, it should work
     fine when used on small immediates *)
  load_const c r := [Const concrete_int_32_t c r]
}.


Definition hello_world :=
  map (@encode_instr _ concrete_int_32_ops)
      [Const concrete_int_32_t (repr 1) (repr 12);
       Const concrete_int_32_t (repr 2) (repr 13);
       Binop concrete_int_32_t BAdd (repr 12) (repr 13) (repr 13)].

Definition faulthandler_bin := map (@encode_instr _ concrete_int_32_ops)
                                   (kernel_protection_fh concrete_int_32_t _
                                                         concrete_int_32_params
                                                         concrete_int_32_fh).

Open Scope bool_scope.
Open Scope Z_scope.

Fixpoint insert_from_as {A B : Type} (i : int) (l : list A) (f : A -> B)
                        (mem : Int32PMap.t B) : Int32PMap.t B :=
  match l with
    | []      => mem
    | h :: l' => insert_from_as (add i one) l' f (Int32PMap.set i (f h) mem)
  end.

Fixpoint constants_from {A : Type} (i : int) (n : nat) (x : A)
                        (mem : Int32PMap.t A) : Int32PMap.t A :=
  match n with
    | O    => mem
    | S n' => constants_from (add i one) n' x (Int32PMap.set i x mem)
  end.

Definition initial_memory : Concrete.memory concrete_int_32_t :=
  let kernelZero := Atom zero Concrete.TKernel in
  let withNone w := w @ Concrete.TNone
  in ( constants_from zero        1000 kernelZero
     ∘ insert_from_as (repr 1000) hello_world      withNone
     ∘ insert_from_as (repr 2000) faulthandler_bin withNone )
     (Int32PMap.empty _).

Program Definition initial_regs : Concrete.registers concrete_int_32_t :=
  Int32TMap.init zero@zero.

Program Definition initial_state : Concrete.state concrete_int_32_t := {|
  Concrete.mem := initial_memory;
  Concrete.regs := initial_regs;
  Concrete.cache := concrete_ground_rules;
  Concrete.pc := (repr 1000)@TNone;
  Concrete.epc := zero@zero
|}.
