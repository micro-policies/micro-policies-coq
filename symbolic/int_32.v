(* Specializing protected kernel for symbolic machine to 32 bits *)

Require Import ZArith.
Require Import Integers.
Require Import List.
Require Import Bool.

Import ListNotations.

Require Import lib.FiniteMaps.
Require Import lib.utils lib.Coqlib.
Require Import common.common.
Require Import concrete.int_32.
Require Import concrete.concrete.
Require Import symbolic.rules.
Require Import symbolic.fault_handler.
Require Import symbolic.symbolic.
Require Import eqtype.
Require Import lib.partial_maps.

Import DoNotation.
Import Int32.
Import Concrete.

Section WithClasses.

Let t := concrete_int_32_t.

Instance concrete_int_32_fh : fault_handler_params t := {
  rop := Int32.repr 1;
  rtpc := Int32.repr 2;
  rti := Int32.repr 3; rt1 := Int32.repr 4; rt2 := Int32.repr 5;
  rt3 := Int32.repr 6;
  rb := Int32.repr 7;
  ri1 := Int32.repr 8; ri2 := Int32.repr 9; ri3 := Int32.repr 10;
  ri4 := Int32.repr 11; ri5 := Int32.repr 12;
  rtrpc := Int32.repr 13; rtr := Int32.repr 14;
  raddr := Int32.repr 15;

  (* WARNING: This doesn't quite work in the general case, because imm
     should be strictly smaller than word. However, it should work
     fine when used on small immediates *)
  load_const := fun (x : word t) (r : reg t) =>
    [Const _ (word_to_imm x) r]
}.

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

(* FIXME: right now, this definition works only for the sealing
machine, whose system calls have trivial entry tags. Ideally, the
system call should provide kernelize_syscall with a tag for its entry
point. *)
Definition kernelize_syscall (seg : @relocatable_segment concrete_int_32_t w w)
                   : relocatable_segment w atom :=
  let (l,gen) := seg in
  ((l + 1)%nat, fun b rest =>
        (* ENTRY tag with constant ut *)
        (encode_instr (Nop _))@(Z_to_word 2) ::
        map (fun x => x@Concrete.TKernel) (gen b rest)).

Definition kernelize_user_tag t :=
  add (shl t (repr 2)) (repr 1).

Definition kernelize_tags
                   {X : Type}
                   (seg : @relocatable_segment concrete_int_32_t X atom)
                   : relocatable_segment X atom :=
  let (l,gen) := seg in
  (* BCP: This has to correspond with the tag encoding used in
     fault_handler.v -- probably better to write it there rather than here *)
  (l,
   fun b rest =>
     map (fun x => Atom (common.val x)
                        (kernelize_user_tag (common.tag x))) (gen b rest)).

Definition initial_memory
      (extra_state : relocatable_segment _ w)
      (handler : relocatable_segment w w)
      (syscalls : list (relocatable_segment w w))
      (user_mem : relocatable_segment (list w) atom)
    : Concrete.memory concrete_int_32_t * w * list w :=
  let cacheCell := Atom zero Concrete.TKernel in
  let '((kernel_length,gen_kernel), offsets) :=
    concat_and_measure_relocatable_segments
      ([kernelize handler;
       kernelize extra_state] ++
       (map kernelize_syscall syscalls)) in
  match offsets with
  | _ :: extra_state_offset :: syscall_offsets =>
    let base_addr := fault_handler_start concrete_int_32_ops in
    let extra_state_addr := add_word base_addr
                                     (nat_to_word extra_state_offset) in
    let user_code_addr := add_word base_addr (nat_to_word kernel_length) in
    let syscall_addrs :=
        map (fun off => add_word base_addr (nat_to_word off))
            syscall_offsets in
    let (_, gen_user) := kernelize_tags user_mem in
    let kernel := gen_kernel base_addr extra_state_addr in
    let user := gen_user user_code_addr syscall_addrs in
    let mem :=
       ( constants_from zero 8 cacheCell
       ∘ insert_from base_addr kernel
       ∘ insert_from user_code_addr user )
       (Int32PMap.empty _) in
     (mem, user_code_addr, syscall_addrs)
   | _ =>
     (* Should not happen *)
     (Int32PMap.empty _, repr 0, [])
   end.

(* BCP: Register initialization may need to be generalized at some
   point.  Right now, it initializes all user registers with the
   tag (USER 0).  But the user program might conceivably want to start
   with a different tag assignment.  (On the other hand, maybe
   policies can always simply be written so that tag 0 is a reasonable
   default.) *)

Program Definition concrete_initial_state
      (extra_state : relocatable_segment _ w)
      (handler : relocatable_segment w w)
      (syscalls : list (relocatable_segment w w))
      (user_mem : relocatable_segment (list w) atom)
      (initial_pc_tag : w)
      (user_regs : list (reg concrete_int_32_t))
      (initial_reg_tag : w)
    : Concrete.state concrete_int_32_t * w * list w :=
  let '(mem, start, syscall_addrs) :=
    initial_memory extra_state handler syscalls user_mem in
  let regs :=
        fold_left
          (fun regs r =>
            Int32TMap.set r zero@(kernelize_user_tag initial_reg_tag) regs)
          user_regs
          (Int32TMap.init zero@zero) in
  ({|
    Concrete.mem := mem;
    Concrete.regs := regs;
    Concrete.cache := ground_rules;
    Concrete.pc := start@(kernelize_user_tag initial_pc_tag);
    Concrete.epc := zero@zero
  |},
  start, syscall_addrs).

(* TODO: Regularize naming of base addresses and system call stuff. *)

Context {sp: Symbolic.params}.

Let sym_atom := @common.atom (word t) Symbolic.tag.

Program Definition symbolic_initial_state 
      (user_mem : relocatable_segment (list (word t)) sym_atom)
      (base_addr : sym_atom) (syscall_addrs : list (word t))
      (user_regs : list (reg t))
      (initial_reg_value : sym_atom)
      (initial_internal_state : Symbolic.internal_state)
      : @Symbolic.state t sp :=
  let (_, gen) := user_mem in
  let mem_contents := gen (common.val base_addr) syscall_addrs in 
  let mem := 
    snd (fold_left
      (fun x c => let: (i,m) := x in 
                  (add_word (Z_to_word 1) i, PartMaps.set m i c))
      mem_contents
      ((common.val base_addr), PartMaps.empty))
      in
  let regs := 
        fold_left
          (fun regs r => PartMaps.set regs r initial_reg_value)
           user_regs
           PartMaps.empty in
  {|  
    Symbolic.mem := mem;
    Symbolic.regs := regs;
    Symbolic.pc := base_addr;
    Symbolic.internal := initial_internal_state
  |}.

End WithClasses.
