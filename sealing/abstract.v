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

Local Notation memory := (word_map t value).
Local Notation registers := (reg_map t value).

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
    let pc' := add_word pc (if w == Z_to_word 0
                            then Z_to_word 1 else imm_to_word n) in forall
    (NEXT : st' = State mem reg pc' ks),   step st st'
| step_jal : forall mem reg reg' pc r w ks
    (ST   : st = State mem reg pc ks)
    (INST : decode mem pc =? Jal _ r)
    (RW   : get reg r =? VData w)
    (UPD  : upd reg ra (VData (pc.+1)) =? reg')
    (NEXT : st' = State mem reg' w ks),   step st st'
| step_mkkey : forall mem reg reg' pc ks
    (ST   : st = State mem reg mkkey_addr ks)
    (INST : decode mem mkkey_addr = None)
    (UPD  : upd reg syscall_ret (VKey (mkkey_f ks)) =? reg')
    (RET  : get reg ra =? VData pc)
    (NEXT : st' = State mem reg' pc ((mkkey_f ks) :: ks)),   step st st'
| step_seal : forall mem reg reg' pc ks payload key
    (ST   : st = State mem reg seal_addr ks)
    (INST : decode mem seal_addr = None)
    (R1   : get reg syscall_arg1 =? VData payload)
    (R2   : get reg syscall_arg2 =? VKey key)
    (UPD  : upd reg syscall_ret (VSealed payload key) =? reg')
    (RET  : get reg ra =? VData pc)
    (NEXT : st' = State mem reg' pc ks),   step st st'
| step_unseal : forall mem reg reg' pc ks payload key
    (ST   : st = State mem reg unseal_addr ks)
    (INST : decode mem unseal_addr = None)
    (R1   : get reg syscall_arg1 =? VSealed payload key)
    (R2   : get reg syscall_arg2 =? VKey key)
    (UPD  : upd reg syscall_ret (VData payload) =? reg')
    (RET  : get reg ra =? VData pc)
    (NEXT : st' = State mem reg' pc ks),   step st st'.

Definition stepf (st : state) : option state :=
  let 'State mem reg pc keys := st in
  match decode mem pc with
    | Some Nop =>
      Some (State mem reg (pc.+1) keys)
    | Some (Const n r) =>
      do! reg' <- PartMaps.upd reg r (VData (imm_to_word n));
      Some (State mem reg' (pc.+1) keys)
    | Some (Mov r1 r2) =>
      do! v <- PartMaps.get reg r1;
      do! reg' <- PartMaps.upd reg r2 v;
      Some (State mem reg' (pc.+1) keys)
    | Some (Binop b r1 r2 r3) =>
      do! v1 <- PartMaps.get reg r1;
      do! v2 <- PartMaps.get reg r2;
      if v1 is VData i1 then if v2 is VData i2 then 
        do! reg' <- PartMaps.upd reg r3 (VData (binop_denote b i1 i2));
        Some (State mem reg' (pc.+1) keys)
      else None else None
    | Some (Load r1 r2) =>
      do! v <- PartMaps.get reg r1;
      if v is VData i then
        do! v' <- PartMaps.get mem i;
        do! reg' <- PartMaps.upd reg r2 v';
        Some (State mem reg' (pc.+1) keys)
      else None
    | Some (Store r1 r2) =>
      do! v1 <- PartMaps.get reg r1;
      do! v2 <- PartMaps.get reg r2;
      if v1 is VData i1 then
        do! mem' <- PartMaps.upd mem i1 v2;
        Some (State mem' reg (pc.+1) keys)
      else None
    | Some (Jump r) =>
      do! v <- PartMaps.get reg r;
      if v is VData i then
        Some (State mem reg i keys)
      else None
    | Some (Bnz r n) =>
      do! vr <- PartMaps.get reg r;
      if vr is VData c then
        let pc' := pc + if c == Z_to_word 0 
                        then Z_to_word 1 else imm_to_word n in
        Some (State mem reg pc' keys)
      else None
    | Some (Jal r) =>
      do! vr <- PartMaps.get reg r;
      if vr is VData i then
        do! reg' <- PartMaps.upd reg ra (VData (pc.+1));
        Some (State mem reg' i keys)
      else None
    | Some JumpEpc | Some AddRule | Some (GetTag _ _) 
    | Some (PutTag _ _ _) | Some Halt =>
    None
    | None =>
    if pc == mkkey_addr then
      let k := mkkey_f keys in
      let keys' := k :: keys in
      do! reg' <- PartMaps.upd reg syscall_ret (VKey k);        
      do! ret <- PartMaps.get reg ra;
      if ret is VData pc' then
        Some (State mem reg' pc' keys')
      else None
    else if pc == seal_addr then
      do! v1 <- PartMaps.get reg syscall_arg1;
      do! v2 <- PartMaps.get reg syscall_arg2;
      if v1 is VData payload then if v2 is VKey k then
        do! reg' <- PartMaps.upd reg syscall_ret (VSealed payload k);
        do! ret <- PartMaps.get reg ra;
        if ret is VData pc' then
          Some (State mem reg' pc' keys)
        else None
      else None else None
    else if pc == unseal_addr then
      do! v1 <- PartMaps.get reg syscall_arg1;
      do! v2 <- PartMaps.get reg syscall_arg2;
      if v1 is VSealed payload k then if v2 is VKey k' then
        if k == k' then
          do! reg' <- PartMaps.upd reg syscall_ret (VData payload);
          do! ret <- PartMaps.get reg ra;
          if ret is VData pc' then
            Some (State mem reg' pc' keys)
          else None
        else None
      else None else None
    else 
      None
    end.

(* TODO: Prove correctness *)

(* ---------------------------------------------------------------------- *)
(* Building initial machine states *)

Program Definition abstract_initial_state
      (user_mem : relocatable_segment classes.sealing_syscall_addrs value) 
      (base_addr : word t)
      (user_regs : list (reg t))
    : state := 
  let (_, gen) := user_mem in
  let mem_contents := gen base_addr ssa in 
  let mem := 
    snd (fold_left
      (fun x c => let: (i,m) := x in 
                  (add_word (Z_to_word 1) i, PartMaps.set m i c))
      mem_contents
      (base_addr, PartMaps.empty))
      in
  let regs := 
        fold_left
          (fun regs r => PartMaps.set regs r (VData (Z_to_word 0)))
           user_regs
           PartMaps.empty in
  {|  
    mem := mem;
    regs := regs;
    pc := base_addr;
    keys := []
  |}.

End WithClasses.

Notation memory t := (word_map t (@value t _)).
Notation registers t := (reg_map t (@value t _)).

End Abs.

Arguments Abs.state t {_}.
