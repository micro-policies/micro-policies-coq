Require Import QuickChick.

Require Import common.
Require Import concrete.
Require Import concrete_exec.
Require Import concrete_int_32.
Require Import concrete_monitor.
Require Import fault_handler.
Require Import testing.

Require Import ZArith.
Require Import Integers.
Require Import List.
Require Import Coq.Strings.String.
Import ListNotations.

Import Concrete.

Definition state       := state       concrete_int_32_t.
Definition word        := word        concrete_int_32_t.
Definition monitor_regs := monitor_regs concrete_int_32_t concrete_int_32_fh.
Definition reg         := reg         concrete_int_32_t.
Definition atom        := atom        concrete_int_32_t.
Definition mkatom      := mkatom      concrete_int_32_t.
Definition registers   := registers   concrete_int_32_t.
Definition memory      := memory      concrete_int_32_t.

Definition word_eq_dec : forall (x y : word), {x = y} + {~ (x = y)} :=
  word_mt_eq_dec reflect_eq_word.

Definition gen_word : Gen word := liftGen Z_to_word arbitrary.

(* Generates a valid register :
   - The value of the register is an arbitrary integer (TODO: Fix? Does it matter?)
   - The tag of the register depends on the register ID (monitor/non-monitor) *)
Definition gen_register (r : reg) : Gen atom :=
  liftGen2 mkatom gen_word
           (if in_dec word_eq_dec r monitor_regs then
              returnGen TMonitor
            else returnGen TNone).

Definition nat_to_reg (n : nat) : reg :=
  Z_to_word (Z_of_nat n).

Definition gen_register_nat (n : nat) : Gen atom :=
  gen_register (nat_to_reg n).

(* TODO: How many should I generate??? *)
Definition gen_registers (n : nat) : Gen registers :=
  foldGen (fun a b => liftGen (upd_reg a (nat_to_reg b)) (gen_register_nat b))
          (seq 0 n) initial_regs.

(* TODO: Maybe we want to generate random cache configurations? *)
Definition gen_cache : Gen (rules word) := returnGen concrete_ground_rules.

(* First thousand  -> Monitor constants
   Second thousand -> User Program
   Third thousand  -> Faulthandler *)
Definition gen_memory : Gen memory := returnGen initial_memory.

(*
Fixpoint constants_from {A : Type} (i : int) (n : nat) (x : A)
                        (mem : Int32PMap.t A) : Int32PMap.t A :=
  match n with
    | O    => mem
    | S n' => constants_from (add i one) n' x (Int32PMap.set i x mem)
  end.


Definition initial_memory : Concrete.memory concrete_int_32_t :=
  let monitorZero := Concrete.mkatom concrete_int_32_t zero Concrete.TMonitor in
  let withNone w := w @ Concrete.TNone
  in ( constants_from zero        1000 monitorZero
     ∘ insert_from_as (repr 1000) hello_world      withNone
     ∘ insert_from_as (repr 2000) faulthandler_bin withNone )
     (Int32PMap.empty _).
*)

Definition gen_pc : Gen atom := returnGen (pc initial_state).

Definition gen_state : Gen state :=
  bindGen gen_memory         (fun m  =>
  bindGen (gen_registers 42) (fun r  =>
  bindGen gen_cache          (fun c  =>
  bindGen gen_pc             (fun pc =>
  returnGen {|
    mem   := m;
    regs  := r;
    cache := c;
    pc    := pc;
    epc   := epc (initial_state)
  |})))).

Require Import Integers.

Definition prop_mi :=
  forAllShrink (fun _ => "Foo"%string) (returnGen initial_state) (fun _ => [])
               (fun s =>
   invariant_exec concrete_int_32_fh reflect_eq_word (Z_to_word 2000)
                  (mem s) (regs s) (cache s)).

Definition toTest := quickCheck prop_mi.

QuickCheck toTest.
