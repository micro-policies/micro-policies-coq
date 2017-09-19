(* Specializing protected monitor for symbolic machine to 32 bits *)

Require Import lib.utils.
Require Import common.types common.segment.
Require Import concrete.int_32.
Require Import concrete.concrete.
Require Import symbolic.rules.
Require Import symbolic.fault_handler.
Require Import symbolic.symbolic.
From mathcomp Require Import ssrnat eqtype seq ssrint.

From CoqUtils Require Import word fmap.

Import DoNotation.
Import Concrete.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section WithClasses.

Let mt := concrete_int_32_mt.

Instance concrete_int_32_fh : fault_handler_params mt := {
  rop := as_word 1;
  rtpc := as_word 2;
  rti := as_word 3; rt1 := as_word 4; rt2 := as_word 5;
  rt3 := as_word 6;
  rb := as_word 7;
  ri1 := as_word 8; ri2 := as_word 9; ri3 := as_word 10;
  ri4 := as_word 11; ri5 := as_word 12;
  rtrpc := as_word 13; rtr := as_word 14;
  raddr := as_word 15;

  (* WARNING: This doesn't quite work in the general case, because imm
     should be strictly smaller than word. However, it should work
     fine when used on small immediates *)
  load_const := fun (x : mword mt) (r : reg mt) =>
    [:: Const (swcast x) r]
}.

Fixpoint insert_from {A : Type} (i : word 32) (l : seq A)
                     (mem : {fmap word 32 -> A}) : {fmap word 32 -> A} :=
  match l with
  | [::]    => mem
  | h :: l' => insert_from (i + 1)%w l' (setm mem i h)
  end.

Fixpoint constants_from {A : Type} (i : word 32) (n : nat) (x : A)
                        (mem : {fmap word 32 -> A}) : {fmap word 32 -> A} :=
  match n with
  | O    => mem
  | S n' => constants_from (i + 1)%w n' x (setm mem i x)
  end.

Definition w := mword mt.

Definition monitorize (seg : @relocatable_segment mt w w)
                   : @relocatable_segment mt w (atom (word 32) (word 32)) :=
  let (l,gen) := seg in
  (l, fun b rest => map (fun x => Atom x (Concrete.TMonitor : w)) (gen b rest)).

(* FIXME: right now, this definition works only for the sealing
machine, whose system calls have trivial entry tags. Ideally, the
system call should provide monitorize_syscall with a tag for its entry
point. *)
Definition monitorize_syscall (seg : @relocatable_segment mt w w)
                   : relocatable_segment w (atom w w) :=
  let (l,gen) := seg in
  ((l + 1)%nat, fun b rest =>
        (* ENTRY tag with constant ut *)
        (encode_instr (Nop _))@(as_word 2) ::
        map (fun x => x@Concrete.TMonitor) (gen b rest)).

Definition monitorize_user_tag t : word 32 :=
  (shlw t (as_word 2) + 1)%w.

Definition monitorize_tags
                   {X : Type}
                   (seg : @relocatable_segment mt X (atom w w))
                   : relocatable_segment X (atom w w) :=
  let (l,gen) := seg in
  (* BCP: This has to correspond with the tag encoding used in
     fault_handler.v -- probably better to write it there rather than here *)
  (l,
   fun b rest =>
     map (fun x => Atom (vala x)
                        (monitorize_user_tag (taga x))) (gen b rest)).

(* Build the basic monitor memory on top of which we will put user
   programs. Returns a triple with the monitor memory, the base user
   address, and a list of system call addresses. *)
Definition build_monitor_memory
      (extra_state : relocatable_segment _ w)
      (handler : relocatable_segment w w)
      (syscalls : seq (relocatable_segment w w))
    : Concrete.memory mt * w * seq w :=
  let cacheCell := Atom 0%w (Concrete.TMonitor : w) in
  let '((monitor_length,gen_monitor), offsets) :=
    concat_and_measure_relocatable_segments
      ([:: monitorize handler;
       monitorize extra_state] ++
       (map monitorize_syscall syscalls)) in
  match offsets with
  | _ :: extra_state_offset :: syscall_offsets =>
    let base_addr := fault_handler_start _ in
    let extra_state_addr := (base_addr + as_word extra_state_offset)%w in
    let user_code_addr := (base_addr + as_word monitor_length)%w in
    let syscall_addrs :=
        map (fun off : nat => base_addr + as_word off)%w
            syscall_offsets in
    let monitor := gen_monitor base_addr extra_state_addr in
    let mem :=
       ( constants_from 0%w 8 cacheCell
       ∘ insert_from base_addr monitor )
       emptym in
     (mem, user_code_addr, syscall_addrs)
   | _ =>
     (* Should not happen *)
     (emptym, as_word 0, [::])
   end.

(* BCP: Register initialization may need to be generalized at some
   point.  Right now, it initializes all user registers with the
   tag (USER 0).  But the user program might conceivably want to start
   with a different tag assignment.  (On the other hand, maybe
   policies can always simply be written so that tag 0 is a reasonable
   default.) *)

Program Definition concrete_initial_state
      {Addrs}
      (initial_memory : Concrete.memory mt)
      (user_mem_addr : w)
      (syscall_addrs : Addrs)
      (user_mem : relocatable_segment Addrs (atom w w))
      (initial_pc_tag : w)
      (user_regs : seq (reg mt))
      (initial_reg_tag : w)
    : Concrete.state mt :=
  let '(_, user_gen) := monitorize_tags user_mem in
  let mem' := insert_from user_mem_addr (user_gen user_mem_addr syscall_addrs) initial_memory in
  let kregs :=
        foldl
          (fun regs r =>
             setm regs r zerow@(Concrete.TMonitor:w))
          emptym (monitor_regs concrete_int_32_fh) in
  let regs :=
        foldl
          (fun regs r =>
            setm regs r zerow@(monitorize_user_tag initial_reg_tag))
          kregs user_regs in
  {|
    Concrete.mem := mem';
    Concrete.regs := regs;
    Concrete.cache := ground_rules _;
    Concrete.pc := user_mem_addr@(monitorize_user_tag initial_pc_tag);
    Concrete.epc := zerow@zerow
  |}.

(* TODO: Regularize naming of base addresses and system call stuff. *)

Context {sp: Symbolic.params}.

Let sym_atom k := atom (mword mt) (Symbolic.tag_type (@Symbolic.ttypes sp) k).

Program Definition symbolic_initial_state
      {Addrs}
      (user_mem : relocatable_segment Addrs (sym_atom Symbolic.M))
      (base_addr : sym_atom Symbolic.P) (syscall_addrs : Addrs)
      (user_regs : seq (reg mt))
      (initial_reg_value : sym_atom Symbolic.R)
      (initial_internal_state : Symbolic.internal_state)
      : @Symbolic.state mt sp :=
  let (_, gen) := user_mem in
  let mem_contents := gen (vala base_addr) syscall_addrs in
  let mem :=
    snd (foldl
      (fun x c => let: (i,m) := x in
                  (i + 1, setm m i c)%w)
      ((vala base_addr), emptym) mem_contents) in
  let regs :=
        foldl
          (fun regs r => setm regs r initial_reg_value)
           emptym user_regs in
  {|
    Symbolic.mem := mem;
    Symbolic.regs := regs;
    Symbolic.pc := base_addr;
    Symbolic.internal := initial_internal_state
  |}.

(* BCP/MD: These should all be distinct from monitor registers in
   symbolic.int_32, though this should not cause axiom failures --
   just puzzling user program errors! *)

Global Instance concrete_int_32_scr : syscall_regs mt := {|
  syscall_ret  := as_word 16;
  syscall_arg1 := as_word 17;
  syscall_arg2 := as_word 18;
  syscall_arg3 := as_word 19
|}.

End WithClasses.
