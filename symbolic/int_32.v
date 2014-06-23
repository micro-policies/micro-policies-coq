(* Specializing protected kernel for symbolic machine to 32 bits *)

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

Definition kernelize (seg : @relocatable_segment concrete_int_32_t w w) 
                   : relocatable_segment w atom :=
  let (l,gen) := seg in
  (l, fun b rest => map (fun x => Atom x Concrete.TKernel) (gen b rest)).

Definition kernelize_user_tag t :=
  add (shl t (repr 2)) (repr 1).

Definition kernelize_tags (seg : @relocatable_segment concrete_int_32_t w atom) 
                   : relocatable_segment w atom :=
  let (l,gen) := seg in
  (* BCP: This has to correspond with the tag encoding used in 
     fault_handler.v -- probably better to write it there rather than here *)
  (l, 
   fun b rest => 
     map (fun x => Atom (common.val x) 
                        (kernelize_user_tag (common.tag x))) (gen b rest)).

Definition initial_memory 
      (extra_state : relocatable_segment _ w)
      (handler_and_syscalls : relocatable_segment w w)
      (user_mem : relocatable_segment w atom) 
    : Concrete.memory concrete_int_32_t * w :=
  let cacheCell := Atom zero Concrete.TKernel in
  let (_,gen) := concat_relocatable_segments 
                    (kernelize
                       (concat_relocatable_segments 
                          handler_and_syscalls
                          extra_state))
                    (kernelize_tags user_mem) in
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

(* BCP: The time argument should surely not be needed -- I got tangled
   up in numeric conversions...  If we ever try to prove something
   about this function, we need to rewrite it first! *)
Fixpoint initialize_registers 
             (min max : reg concrete_int_32_t)
             (tag : word concrete_int_32_t)
             (regs : Concrete.registers concrete_int_32_t)
             (time : nat)
           : Concrete.registers concrete_int_32_t :=
  match time with
    0%nat => regs
  | S time' =>
      if Z.leb (word_to_Z max) (word_to_Z min) then regs else 
      initialize_registers (add_word min (Z_to_word 1)) max tag (Int32TMap.set min zero@tag regs) time'
  end.

(* BCP: This may need to be generalized at some point.  Right now, it
   initializes all user registers with the tag (USER 0).  But the user
   program might conceivably want to start with a different tag
   assignment.  (On the other hand, maybe policies can always simply
   be written so that tag 0 is a reasonable default.) *)
Program Definition initial_regs
                     (user_reg_min user_reg_max : reg concrete_int_32_t)
                     (initial_reg_tag : word concrete_int_32_t)
                   : Concrete.registers concrete_int_32_t :=
  initialize_registers 
    user_reg_min user_reg_max 
    (kernelize_user_tag initial_reg_tag)
    (Int32TMap.init zero@zero)
    100.

Program Definition initial_state 
      (extra_state : relocatable_segment _ w)
      (handler_and_syscalls : relocatable_segment w w)
      (user_mem : relocatable_segment w atom) 
      (initial_pc_tag : w) 
      (user_reg_min user_reg_max : reg concrete_int_32_t)
      (initial_reg_tag : w) 
    : Concrete.state concrete_int_32_t := 
  let (mem, start) := initial_memory extra_state handler_and_syscalls user_mem in
  {|  
    Concrete.mem := mem;
    Concrete.regs := initial_regs user_reg_min user_reg_max initial_reg_tag;
    Concrete.cache := ground_rules;
    Concrete.pc := start@(kernelize_user_tag initial_pc_tag); 
    Concrete.epc := zero@zero
  |}.
