Require Import List. Import ListNotations.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.SetoidDec.
Require Import lib.utils.

Import DoNotation.

Require Import utils common.
Require Import classes.

Set Implicit Arguments.

Module AbsSeal.

Section WithClasses.

Context (t : machine_types)
        {ops : machine_ops t}
        {sk : sealing_key}.

Class key_generator := {
  mkkey_f : list key -> option (list key * key);
 
  (* This ensures freshness without fixing a generation strategy *)
  mkkey_fresh : forall ks ks' k,
                  mkkey_f ks = Some (ks', k) ->
                  ~In k ks /\ In k ks' /\ incl ks ks'
}.

Context {kg : key_generator}
        {scr : @syscall_regs t}
        {ssa : @sealing_syscall_addrs t}.

Inductive value := 
| VWord   : word t        -> value
| VKey    :           key -> value
| VSealed : word t -> key -> value.

Context {memory : Type}
        {am : @partial_map memory (word t) value}
        {registers : Type}
        {ar : @partial_map registers (reg t) value}.

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
    | Some (VWord i) => decode_instr i
    | _              => None
  end.

(* BCP: OK, I like the way this looks now... *)

Inductive step (st st' : state) : Prop :=
| step_nop : forall mem reg pc es
      (ST : st = State mem reg pc es)
    (INST : decode mem pc =? Nop _)
    (NEXT : st' = State mem reg (pc.+1) es),   step st st'
| step_const : forall mem reg reg' pc n r es
      (ST : st = State mem reg pc es)
    (INST : decode mem pc =? Const _ n r)
    (UPD  : upd reg r (VWord (imm_to_word n)) =? reg')
    (NEXT : st' = State mem reg' (pc.+1) es),   step st st'
| step_mov : forall mem reg reg' pc r1 v1 r2 es
      (ST : st = State mem reg pc es)
    (INST : decode mem pc =? Mov _ r1 r2)
    (R1W  : get reg r1 =? v1)
    (UPD  : upd reg r2 v1 =? reg')
    (NEXT : st' = State mem reg' (pc.+1) es),   step st st'
| step_binop : forall mem reg reg' pc op r1 r2 r3 w1 w2 es
      (ST : st = State mem reg pc es)
    (INST : decode mem pc =? Binop _ op r1 r2 r3)
    (R1W  : get reg r1 =? VWord w1)
    (R2W  : get reg r2 =? VWord w2)
    (UPD  : upd reg r3 (VWord (binop_denote op w1 w2)) =? reg')
    (NEXT : st' = State mem reg' (pc.+1) es),   step st st'
| step_load : forall mem reg reg' pc r1 r2 w1 v2 es
      (ST : st = State mem reg pc es)
    (INST : decode mem pc =? Load _ r1 r2)
    (R1W  : get reg r1 =? VWord w1)
    (MEM1 : get mem w1 =? v2)
    (UPD  : upd reg r2 v2 =? reg')
    (NEXT : st' = State mem reg' (pc.+1) es),   step st st'
| step_store : forall mem mem' reg pc r1 r2 w1 v2 es
      (ST : st = State mem reg pc es)
    (INST : decode mem pc =? Store _ r1 r2)
    (R1W  : get reg r1 =? VWord w1)
    (R2W  : get reg r2 =? v2)
    (UPDM : upd mem w1 v2 =? mem')
    (NEXT : st' = State mem' reg (pc.+1) es),   step st st'
| step_jump : forall mem reg pc r w es
      (ST : st = State mem reg pc es)
    (INST : decode mem pc =? Jump _ r)
    (RW   : get reg r =? VWord w)
    (NEXT : st' = State mem reg w es),   step st st'
| step_bnz : forall mem reg pc r n w es
      (ST : st = State mem reg pc es)
    (INST : decode mem pc =? Bnz _ r n)
    (RW   : get reg r =? VWord w),
    let pc' := add_word pc (if w ==b Z_to_word 0
                            then Z_to_word 1 else imm_to_word n) in forall
    (NEXT : st' = State mem reg pc' es),   step st st'
| step_jal : forall mem reg reg' pc r w es
      (ST : st = State mem reg pc es)
    (INST : decode mem pc =? Jal _ r)
    (RW   : get reg r =? VWord w)
    (NOSC : ~In w syscall_addrs)
    (UPD  : upd reg ra (VWord (pc.+1)) =? reg')
    (NEXT : st' = State mem reg' w es),   step st st'
| step_mkkey : forall mem reg reg' pc r es es' nk
      (ST : st = State mem reg pc es)
    (INST : decode mem pc =? Jal _ r)
    (RW   : get reg r =? VWord mkkey_addr)
    (GEN  : mkkey_f es =? (es',nk))
    (UPD  : upd reg syscall_ret (VKey nk) =? reg')
    (NEXT : st' = State mem reg' pc es'),   step st st'
| step_seal : forall mem reg reg' pc r es payload key
      (ST : st = State mem reg pc es)
    (INST : decode mem pc =? Jal _ r)
    (RW   : get reg r =? VWord seal_addr)
    (R1   : get reg syscall_arg1 =? VWord payload)
    (R2   : get reg syscall_arg2 =? VKey key)
    (UPD  : upd reg syscall_ret (VSealed payload key) =? reg')
    (NEXT : st' = State mem reg' pc es),   step st st'
| step_unseal : forall mem reg reg' pc r es payload key
      (ST : st = State mem reg pc es)
    (INST : decode mem pc =? Jal _ r)
    (RW   : get reg r =? VWord unseal_addr)
    (R1   : get reg syscall_arg1 =? VSealed payload key)
    (R2   : get reg syscall_arg2 =? VKey key)
    (UPD  : upd reg syscall_ret (VWord payload) =? reg')
    (NEXT : st' = State mem reg' pc es),   step st st'.

End WithClasses.

End AbsSeal.
