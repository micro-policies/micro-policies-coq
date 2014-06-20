(* Specializing protected kernel to 32-bit machine *)

Require Import ZArith.
Require Import Integers.
Require Import List.
Require Import Bool.

Import ListNotations.

Require Import lib.FiniteMaps.
Require Import lib.utils lib.Coqlib.
Require Import common.common.
Require Import concrete.concrete.
Require Import symbolic.rules.
Require Import concrete.int_32.
Require Import eqtype.

Import DoNotation.
Import Int32.
Import Concrete.

Axiom fault_handler : list atom.

(*
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
*)

Open Scope bool_scope.
Open Scope Z_scope.

Fixpoint insert_from {A : Type} (i : int) (l : list A) 
                     (mem : Int32PMap.t A) : Int32PMap.t A :=
  match l with
    | []      => mem
    | h :: l' => insert_from (add i one) l' (Int32PMap.set i h mem)
  end.

Fixpoint constants_from {A : Type} (i : int) (n : nat) (x : A)
                        (mem : Int32PMap.t A) : Int32PMap.t A :=
  match n with
    | O    => mem
    | S n' => constants_from (add i one) n' x (Int32PMap.set i x mem)
  end.

Definition w := word concrete_int_32_t.

Definition initial_memory 
      (extra_state : relocatable_segment _ atom)
      (handler_and_syscalls : relocatable_segment w atom)
      (user_mem : relocatable_segment w atom) 
    : Concrete.memory concrete_int_32_t * w :=
  let cacheCell := Atom zero Concrete.TKernel in
  let (_,gen) := concat_relocatable_segments 
                    handler_and_syscalls
                    (concat_relocatable_segments
                       extra_state
                       user_mem) in
  let extra_state_addr := add_word (fault_handler_start concrete_int_32_ops)
                                   (nat_to_word (fst handler_and_syscalls)) in
  let user_code_addr := add_word extra_state_addr
                                 (nat_to_word (fst extra_state)) in
  let contents := 
    gen (fault_handler_start concrete_int_32_ops) extra_state_addr in
  let mem := 
     ( constants_from zero 8 cacheCell
     ∘ insert_from (fault_handler_start concrete_int_32_ops) contents )
     (Int32PMap.empty _) in
   (mem, user_code_addr).

Program Definition initial_regs : Concrete.registers concrete_int_32_t :=
  Int32TMap.init zero@zero.

Program Definition initial_state 
      (extra_state : relocatable_segment _ atom)
      (handler_and_syscalls : relocatable_segment w atom)
      (user_mem : relocatable_segment w atom) 
      (initial_pc_tag : w) 
    : Concrete.state concrete_int_32_t := 
  let (mem, start) := initial_memory extra_state handler_and_syscalls user_mem in
  {|  
    Concrete.mem := mem;
    Concrete.regs := initial_regs;
    Concrete.cache := ground_rules;
    Concrete.pc := start@initial_pc_tag; 
    Concrete.epc := zero@zero
  |}.
