Require Import List. Import ListNotations.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.SetoidDec.
Require Import ssreflect eqtype.
Require Import lib.utils lib.partial_maps.

Import DoNotation.

Require Import lib.utils common.common.
Require Import sealing.classes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Abs.

Section WithClasses.

Context (t : machine_types)
        {ops : machine_ops t}
        {scr : @syscall_regs t}
        {ssa : @sealing_syscall_addrs t}.

Class sealing_key := {
  key       : eqType;

  (* This function is total, so key has to be infinite *)
  mkkey_f : list key -> key;
 
  (* This ensures freshness without fixing a generation strategy *)
  mkkey_fresh : forall ks, ~In (mkkey_f ks) ks
}.

Context {sk : sealing_key}.

Inductive value := 
| VData   : word t        -> value
| VKey    :           key -> value
| VSealed : word t -> key -> value.

Import PartMaps.

Class params := {
  memory    : Type;
  am :> partial_map memory (word t) value;
  registers : Type;
  ar :> partial_map registers (reg t) value
}.

Class params_spec (ap : params) := {
  mem_axioms :> PartMaps.axioms (@am ap);
  reg_axioms :> PartMaps.axioms (@ar ap)
}.

Context {ap : params}.

Open Scope word_scope.

Local Notation "x .+1" := (add_word x (Z_to_word 1)) (at level 60).

Record state := State {
  mem : memory;
  regs : registers;
  pc : word t;
  keys : list key
}.

Definition syscall_addrs := [mkkey_addr; seal_addr; unseal_addr].

Notation "x '=?' y" := (x = Some y) (at level 99).

Definition decode (mem : memory) (pc : word t) :=
  match get mem pc with
    | Some (VData i) => decode_instr i
    | _              => None
  end.

Inductive step (st st' : state) : Prop :=
| step_nop : forall mem reg pc ks
    (ST   : st = State mem reg pc ks)
    (INST : decode mem pc =? Nop _)
    (NEXT : st' = State mem reg (pc.+1) ks),   step st st'
| step_const : forall mem reg reg' pc n r ks
    (ST   : st = State mem reg pc ks)
    (INST : decode mem pc =? Const _ n r)
    (UPD  : upd reg r (VData (imm_to_word n)) =? reg')
    (NEXT : st' = State mem reg' (pc.+1) ks),   step st st'
| step_mov : forall mem reg reg' pc r1 v1 r2 ks
    (ST   : st = State mem reg pc ks)
    (INST : decode mem pc =? Mov _ r1 r2)
    (R1W  : get reg r1 =? v1)
    (UPD  : upd reg r2 v1 =? reg')
    (NEXT : st' = State mem reg' (pc.+1) ks),   step st st'
| step_binop : forall mem reg reg' pc op r1 r2 r3 w1 w2 ks
    (ST   : st = State mem reg pc ks)
    (INST : decode mem pc =? Binop _ op r1 r2 r3)
    (R1W  : get reg r1 =? VData w1)
    (R2W  : get reg r2 =? VData w2)
    (UPD  : upd reg r3 (VData (binop_denote op w1 w2)) =? reg')
    (NEXT : st' = State mem reg' (pc.+1) ks),   step st st'
| step_load : forall mem reg reg' pc r1 r2 w1 v2 ks
    (ST   : st = State mem reg pc ks)
    (INST : decode mem pc =? Load _ r1 r2)
    (R1W  : get reg r1 =? VData w1)
    (MEM1 : get mem w1 =? v2)
    (UPD  : upd reg r2 v2 =? reg')
    (NEXT : st' = State mem reg' (pc.+1) ks),   step st st'
| step_store : forall mem mem' reg pc r1 r2 w1 v2 ks
    (ST   : st = State mem reg pc ks)
    (INST : decode mem pc =? Store _ r1 r2)
    (R1W  : get reg r1 =? VData w1)
    (R2W  : get reg r2 =? v2)
    (UPDM : upd mem w1 v2 =? mem')
    (NEXT : st' = State mem' reg (pc.+1) ks),   step st st'
| step_jump : forall mem reg pc r w ks
    (ST   : st = State mem reg pc ks)
    (INST : decode mem pc =? Jump _ r)
    (RW   : get reg r =? VData w)
    (NEXT : st' = State mem reg w ks),   step st st'
| step_bnz : forall mem reg pc r n w ks
    (ST   : st = State mem reg pc ks)
    (INST : decode mem pc =? Bnz _ r n)
    (RW   : get reg r =? VData w),
    let pc' := add_word pc (if w ==b Z_to_word 0
                            then Z_to_word 1 else imm_to_word n) in forall
    (NEXT : st' = State mem reg pc' ks),   step st st'
| step_jal : forall mem reg reg' pc r w ks
    (ST   : st = State mem reg pc ks)
    (INST : decode mem pc =? Jal _ r)
    (RW   : get reg r =? VData w)
    (NOSC : ~In w syscall_addrs)
    (UPD  : upd reg ra (VData (pc.+1)) =? reg')
    (NEXT : st' = State mem reg' w ks),   step st st'
| step_mkkey : forall mem reg reg' pc r ks
    (ST   : st = State mem reg pc ks)
    (INST : decode mem pc =? Jal _ r)
    (RW   : get reg r =? VData mkkey_addr)
    (UPD  : upd reg syscall_ret (VKey (mkkey_f ks)) =? reg')
    (NEXT : st' = State mem reg' pc ((mkkey_f ks) :: ks)),   step st st'
| step_seal : forall mem reg reg' pc r ks payload key
    (ST   : st = State mem reg pc ks)
    (INST : decode mem pc =? Jal _ r)
    (RW   : get reg r =? VData seal_addr)
    (R1   : get reg syscall_arg1 =? VData payload)
    (R2   : get reg syscall_arg2 =? VKey key)
    (UPD  : upd reg syscall_ret (VSealed payload key) =? reg')
    (NEXT : st' = State mem reg' pc ks),   step st st'
| step_unseal : forall mem reg reg' pc r ks payload key
    (ST   : st = State mem reg pc ks)
    (INST : decode mem pc =? Jal _ r)
    (RW   : get reg r =? VData unseal_addr)
    (R1   : get reg syscall_arg1 =? VSealed payload key)
    (R2   : get reg syscall_arg2 =? VKey key)
    (UPD  : upd reg syscall_ret (VData payload) =? reg')
    (NEXT : st' = State mem reg' pc ks),   step st st'.

End WithClasses.

End Abs.

Arguments Abs.state t {_ _}.
Arguments Abs.memory t {_ _}.
Arguments Abs.registers t {_ _}.
