Require Import Ssreflect.ssreflect.
Require Import Ssreflect.eqtype Ssreflect.fintype.
Require Import Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.seq.
Require Import MathComp.ssrint MathComp.ssrnum MathComp.finset.
Require Import CoqUtils.ord CoqUtils.hseq CoqUtils.word CoqUtils.partmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Require Import lib.utils lib.partmap_utils.
Require Import common.types common.segment.
Require Import concrete.concrete concrete.int_32.
Require Import symbolic.symbolic symbolic.int_32 symbolic.exec.
Require Import compartmentalization.common compartmentalization.symbolic.

Import DoNotation.

Module WordZNotation.
Notation "w1 +! i2" := (w1 + as_word i2)%w (at level 50, left associativity).
Notation "i1 !+ w2" := (as_word i1 + w2)%w (at level 50, left associativity).
Notation "w1 -! i2" := (w1 - as_word i2)%w (at level 50, left associativity).
Notation "i1 !- w2" := (as_word i1 - w2)%w (at level 50, left associativity).
Notation "w1 *! i2" := (w1 * as_word i2)%w (at level 40, left associativity).
Notation "i1 !* w2" := (as_word i1 * w2)%w (at level 40, left associativity).
End WordZNotation.

Definition program (mt : machine_types) : Type := seq (instr mt).

Definition enum_from_upto (l : nat) (h : nat) : seq nat :=
  iota l (h - l).

Section os.

Import WordZNotation.

Let mt := concrete_int_32_mt.
Let sp := @Sym.sym_compartmentalization mt.
Existing Instance concrete_int_32_ops.
Existing Instance concrete_int_32_ops_spec.
Existing Instance concrete_int_32_scr.
Existing Instance sp.

(* ra = 0 is special; register 1 is caller-save; registers 2+ are callee-save *)
Definition caller_save_min : nat := 1.
Definition callee_save_min : nat := 2.

Definition caller_save_regs_nat : seq nat      := enum_from_upto caller_save_min callee_save_min.
Definition caller_save_regs_int : seq int      := map Posz caller_save_regs_nat.
Definition caller_save_regs     : seq (reg mt) := map as_word caller_save_regs_int.
Definition caller_save_regs_imm : seq (imm mt) := map as_word caller_save_regs_int.

Definition callee_save_regs_nat : seq nat      := enum_from_upto callee_save_min (2 ^ reg_field_size mt).
Definition callee_save_regs_int : seq int      := map Posz callee_save_regs_nat.
Definition callee_save_regs     : seq (reg mt) := map as_word callee_save_regs_int.
Definition callee_save_regs_imm : seq (imm mt) := map as_word callee_save_regs_int.

Definition yieldR      : reg mt := as_word callee_save_min.
Definition shared_ptrR : reg mt := (yieldR + 1)%w.
Definition tempR       : reg mt := (shared_ptrR + 1)%w.
Definition free_reg (i : nat) : reg mt := tempR +! S i.

Record process_parameters := { yield_address  : imm mt
                             ; shared_address : imm mt }.

Definition process_setup (extra : program mt)
                         (yield_addr shared_addr : imm mt) : program mt :=
  [:: Const yield_addr        yieldR
  ,   Const shared_addr       shared_ptrR
  &   extra ].

Definition process_loop (body : reg mt -> program mt) : program mt :=
  let loop_body :=
        Load shared_ptrR tempR ::
        body tempR ++
        [:: Store shared_ptrR tempR
        ;   Jal yieldR ]
  in loop_body ++
     (* Unconditionally loop, since yieldR <> 0 *)
     [:: Bnz yieldR (- as_word (length loop_body))%w].

Definition process (init : program mt) (body : reg mt -> program mt)
                   (yield_addr shared_addr : imm mt) : program mt :=
  process_setup init yield_addr shared_addr ++ process_loop body.

Definition process_add1 : imm mt -> imm mt -> program mt :=
  let oneR := free_reg 0
  in process [:: Const 1%w oneR] (fun localR => [:: Binop ADD localR oneR localR]).

Definition process_mul2 : imm mt -> imm mt -> program mt :=
  let twoR := free_reg 0
  in process [:: Const (as_word 2) twoR] (fun localR => [:: Binop MUL localR twoR localR]).

Section scheduler.

Variable scheduler_base_addr : imm mt.

(* 1 word for where to jump back to, plus one word for each register to save *)
Definition pinfo_size : nat := S (2 ^ reg_field_size mt - callee_save_min).
(* A process info block stores pc/ra, then all the caller-save registers *)

Definition pid_addr   : imm mt := scheduler_base_addr.
Definition prog1_addr : imm mt := (pid_addr + 1)%w.
Definition prog2_addr : imm mt := prog1_addr +! pinfo_size.

Definition scheduler_mem_size : imm mt := (1 + as_word (2 * pinfo_size)%nat)%w.

(* stempR is caller-save! *)
Definition stempR : reg mt := as_word caller_save_min.

Definition scheduler_set_prog_addr : program mt :=
  [:: Bnz stempR (as_word 4)
  ;     Const prog1_addr stempR
  ;   Bnz stempR (as_word 2) (* Unconditionally skip the else block *)
  ;     Const prog2_addr stempR ].

Definition scheduler_foreach_callee_save_reg (op : reg mt -> program mt) : program mt :=
  flatten [seq Binop ADD stempR ra stempR :: op r | r <- callee_save_regs].

(* Saves the callee-save registers using only the single caller-save register,
   plus ra (after saving it). *)
Definition scheduler_save_registers : program mt :=
  [:: Const pid_addr stempR
  ;   Load stempR stempR ]
  ++ scheduler_set_prog_addr ++
  [:: Store stempR ra
  ;   Const 1%w ra ]
  ++ scheduler_foreach_callee_save_reg (fun r => [:: Store stempR r]).

Definition scheduler_change_pid : program mt :=
  (* `ra' still holds 1 *)
  let stemp'R := (stempR + 1)%w
  in [:: Const pid_addr stemp'R
     ;   Load stemp'R stempR
     ;   Binop SUB ra stemp'R stemp'R (* Swap the pc between 0 and 1 *)
     ;   Store stemp'R stempR ].

Definition scheduler_call_program : program mt :=
  (* `ra' still holds 1 *)
     scheduler_set_prog_addr
  ++ scheduler_foreach_callee_save_reg (fun r => [:: Load stempR r]) ++
  [:: Const pid_addr stempR
  ;   Load stempR stempR ]
  ++ scheduler_set_prog_addr ++
  [:: Load stempR ra
  ;   Const 0%w stempR
  ;   Jump ra ].

Definition scheduler_yield : program mt :=
  scheduler_save_registers ++ scheduler_change_pid ++ scheduler_call_program.

Definition scheduler_init (prog1 : imm mt) (prog2 : imm mt) : program mt :=
  let stemp'R := (stempR + 1)%w in
  let store_imm addr val :=
        [:: Const addr stempR
        ;   Const val  stemp'R
        ;   Store stemp'R stemp'R ] in
  let preamble :=
        store_imm pid_addr   0%w   ++
        store_imm prog1_addr prog1 ++
        store_imm prog2_addr prog2
  in preamble.

End scheduler.

Definition code (base : imm mt) : program mt :=
  let preamble mem_base p1 p2 := scheduler_init mem_base p1 p2 ++ [:: Const p1 ra; Jump ra] in
  let yield_addr          := (base + as_word (length (preamble 0 0 0)))%w in
  let add1_addr           := yield_addr           +! length (scheduler_yield 0) in
  let mul2_addr           := add1_addr            +! length (process_add1 0 0) in
  let scheduler_base_addr := mul2_addr            +! length (process_mul2 0 0) in
  let shared_addr         := (scheduler_base_addr + scheduler_mem_size)%w
  in flatten [:: preamble        scheduler_base_addr add1_addr mul2_addr
             ;   scheduler_yield scheduler_base_addr
             ;   process_add1    yield_addr shared_addr
             ;   process_mul2    yield_addr shared_addr ].

Definition data_size : imm mt := scheduler_mem_size +! 1%nat.

Instance syscall_addrs : compartmentalization_syscall_addrs mt :=
  {| isolate_addr              := as_word 700
   ; add_to_jump_targets_addr  := as_word 800
   ; add_to_store_targets_addr := as_word 900 |}.

Definition symbolic_os : Symbolic.state mt :=
  let syscall_cids    := [set 0%w; 1%w; as_word 2] in
  let user_cid        := as_word 3 in
  let user_tag        := Sym.DATA user_cid syscall_cids syscall_cids in
  let syscall_tag cid := Sym.DATA (as_word cid) (set1 user_cid) (set1 user_cid)
  in symbolic_initial_state
       (length (code 0%w) + absz (int_of_word data_size),
        fun base (_ : compartmentalization_syscall_addrs mt) =>
          map (fun v => v @ (Sym.DATA user_cid set0 set0))
              (  map encode_instr (code (as_word (int_of_word base)))
              ++ nseq data_size 0%w))
       (as_word 1000)@(Sym.PC INTERNAL 0)%w
       syscall_addrs
       (map (as_word ∘ Posz) (enum_from_upto 0 16))
       0%w@tt
       {| Sym.next_id                  := user_cid +! 1%nat
        ; Sym.isolate_tag              := syscall_tag 0
        ; Sym.add_to_jump_targets_tag  := syscall_tag 1
        ; Sym.add_to_store_targets_tag := syscall_tag 2 |}.

End os.
