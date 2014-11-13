(* Specializing protected kernel for symbolic machine to 32 bits *)

Require Import ZArith.
Require Import Integers.
Require Import Bool.

Require Import lib.FiniteMaps.
Require Import lib.utils lib.Coqlib.
Require Import common.common.
Require Import concrete.int_32.
Require Import concrete.concrete.
Require Import symbolic.rules.
Require Import symbolic.fault_handler.
Require Import symbolic.symbolic.
Require Import eqtype seq.
Require Import lib.partial_maps.

Import DoNotation.
Import Concrete.

Section WithClasses.

Let t := concrete_int_32_t.

Instance concrete_int_32_fh : fault_handler_params t := {
  rop := Word.repr 1;
  rtpc := Word.repr 2;
  rti := Word.repr 3; rt1 := Word.repr 4; rt2 := Word.repr 5;
  rt3 := Word.repr 6;
  rb := Word.repr 7;
  ri1 := Word.repr 8; ri2 := Word.repr 9; ri3 := Word.repr 10;
  ri4 := Word.repr 11; ri5 := Word.repr 12;
  rtrpc := Word.repr 13; rtr := Word.repr 14;
  raddr := Word.repr 15;

  (* WARNING: This doesn't quite work in the general case, because imm
     should be strictly smaller than word. However, it should work
     fine when used on small immediates *)
  load_const := fun (x : word t) (r : reg t) =>
    [:: Const (Word.casts x) r]
}.

Open Scope bool_scope.
Open Scope Z_scope.

Fixpoint insert_from {A : Type} (i : Word.int 31) (l : seq A)
                     (mem : word_map t A) : word_map t A :=
  match l with
    | [::]      => mem
    | h :: l' => insert_from (Word.add i Word.one) l' (PartMaps.set mem i h)
  end.

Fixpoint constants_from {A : Type} (i : Word.int 31) (n : nat) (x : A)
                        (mem : word_map t A) : word_map t A :=
  match n with
    | O    => mem
    | S n' => constants_from (Word.add i Word.one) n' x (PartMaps.set mem i x)
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
        (encode_instr (Nop _))@(Word.repr 2) ::
        map (fun x => x@Concrete.TKernel) (gen b rest)).

Definition kernelize_user_tag t : Word.int 31 :=
  Word.add (Word.shl t (Word.repr 2)) (Word.repr 1).

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

(* Build the basic monitor memory on top of which we will put user
   programs. Returns a triple with the monitor memory, the base user
   address, and a list of system call addresses. *)
Definition build_monitor_memory
      (extra_state : relocatable_segment _ w)
      (handler : relocatable_segment w w)
      (syscalls : list (relocatable_segment w w))
    : Concrete.memory concrete_int_32_t * w * list w :=
  let cacheCell := Atom Word.zero Concrete.TKernel in
  let '((kernel_length,gen_kernel), offsets) :=
    concat_and_measure_relocatable_segments
      ([:: kernelize handler;
       kernelize extra_state] ++
       (map kernelize_syscall syscalls)) in
  match offsets with
  | _ :: extra_state_offset :: syscall_offsets =>
    let base_addr := fault_handler_start _ in
    let extra_state_addr := Word.add base_addr
                                     (Word.reprn extra_state_offset) in
    let user_code_addr := Word.add base_addr (Word.reprn kernel_length) in
    let syscall_addrs :=
        map (fun off => Word.add base_addr (Word.reprn off))
            syscall_offsets in
    let kernel := gen_kernel base_addr extra_state_addr in
    let mem :=
       ( constants_from Word.zero 8 cacheCell
       ∘ insert_from base_addr kernel )
       (PartMaps.empty) in
     (mem, user_code_addr, syscall_addrs)
   | _ =>
     (* Should not happen *)
     (PartMaps.empty, Word.repr 0, [::])
   end.

(* BCP: Register initialization may need to be generalized at some
   point.  Right now, it initializes all user registers with the
   tag (USER 0).  But the user program might conceivably want to start
   with a different tag assignment.  (On the other hand, maybe
   policies can always simply be written so that tag 0 is a reasonable
   default.) *)

Program Definition concrete_initial_state
      {Addrs}
      (initial_memory : Concrete.memory concrete_int_32_t)
      (user_mem_addr : w)
      (syscall_addrs : Addrs)
      (user_mem : relocatable_segment Addrs atom)
      (initial_pc_tag : w)
      (user_regs : list (reg concrete_int_32_t))
      (initial_reg_tag : w)
    : Concrete.state concrete_int_32_t :=
  let '(_, user_gen) := kernelize_tags user_mem in
  let mem' := insert_from user_mem_addr (user_gen user_mem_addr syscall_addrs) initial_memory in
  let kregs :=
        fold_left
          (fun regs r =>
             PartMaps.set regs r Word.zero@(Concrete.TKernel:w))
          (kernel_regs t concrete_int_32_fh)
          PartMaps.empty in
  let regs :=
        fold_left
          (fun regs r =>
            PartMaps.set regs r Word.zero@(kernelize_user_tag initial_reg_tag))
          user_regs
          kregs in
  {|
    Concrete.mem := mem';
    Concrete.regs := regs;
    Concrete.cache := ground_rules _;
    Concrete.pc := user_mem_addr@(kernelize_user_tag initial_pc_tag);
    Concrete.epc := Word.zero@Word.zero
  |}.

(* TODO: Regularize naming of base addresses and system call stuff. *)

Context {sp: Symbolic.params}.

Let sym_atom k := @common.atom (word t) (@Symbolic.ttypes sp k).

Program Definition symbolic_initial_state
      {Addrs}
      (user_mem : relocatable_segment Addrs (sym_atom Symbolic.M))
      (base_addr : sym_atom Symbolic.P) (syscall_addrs : Addrs)
      (user_regs : list (reg t))
      (initial_reg_value : sym_atom Symbolic.R)
      (initial_internal_state : Symbolic.internal_state)
      : @Symbolic.state t sp :=
  let (_, gen) := user_mem in
  let mem_contents := gen (common.val base_addr) syscall_addrs in
  let mem :=
    snd (fold_left
      (fun x c => let: (i,m) := x in
                  (Word.add Word.one i, PartMaps.set m i c))
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

(* BCP/MD: These should all be distinct from monitor registers in
   symbolic.int_32, though this should not cause axiom failures --
   just puzzling user program errors! *)

Global Instance concrete_int_32_scr : @syscall_regs concrete_int_32_t := {|
  syscall_ret  := Word.repr 16;
  syscall_arg1 := Word.repr 17;
  syscall_arg2 := Word.repr 18;
  syscall_arg3 := Word.repr 19
|}.

End WithClasses.
