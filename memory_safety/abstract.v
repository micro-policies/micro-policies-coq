Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype ssrint.
Require Import ord word partmap.
Require Import lib.utils.
Require Import common.types memory_safety.classes.

Import DoNotation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Abstract.

Open Scope bool_scope.

Section WithClasses.

Context (t : machine_types).
Context {ops : machine_ops t}.

Variable block : ordType.

Definition pointer := (block * mword t)%type.

Inductive value :=
| VData : mword t -> value
| VPtr : pointer -> value.

Definition value_eq v1 v2 :=
  match v1, v2 with
  | VData w1, VData w2 => w1 == w2
  | VPtr p1, VPtr p2 => p1 == p2
  | _, _ => false
  end.

Lemma value_eqP : Equality.axiom value_eq.
Proof.
move=> [w1|p1] [w2|p2] /=; try by constructor.
  apply/(iffP eqP); congruence.
apply/(iffP eqP); congruence.
Qed.

Definition value_eqMixin := EqMixin value_eqP.
Canonical value_eqType := Eval hnf in EqType value value_eqMixin.

Definition frame := seq value.

Definition memory := {partmap block -> frame}.
Definition registers := {partmap reg t -> value}.

Open Scope word_scope.

Local Notation word := (mword t).
Local Notation "x .+1" := (fst x, snd x + 1).

Record state := mkState {
  mem : memory;
  regs : registers;
  blocks: seq block;
  pc : value
}.

Definition state_eq s1 s2 :=
  [&& mem s1 == mem s2, regs s1 == regs s2,
      blocks s1 == blocks s2 & pc s1 == pc s2].

Lemma state_eqP : Equality.axiom state_eq.
Proof.
case=> [m1 r1 b1 pc1] [m2 r2 b2 pc2] /=; apply/(iffP and4P) => /=.
  by case; do 4!move/eqP => ->.
by case; do 4!move=> ->; rewrite !eqxx.
Qed.

Definition state_eqMixin := EqMixin state_eqP.
Canonical state_eqType := Eval hnf in EqType state state_eqMixin.

Implicit Type reg : registers.

Class allocator := {

(* The Coq function representing the allocator. *)
  malloc_fun : memory -> seq block -> word -> memory * block;

  free_fun : memory -> block -> option memory

}.

Definition getv (mem : memory) (ptr : pointer) :=
  match mem ptr.1 with
  | None => None
  | Some fr => if ptr.2 < size fr then
                 Some (nth (VData 0) fr ptr.2)
               else
                 None
  end.

Definition updv (mem : memory) (ptr : pointer) (v : value) :=
  match mem ptr.1 with
  | None => None
  | Some fr =>
    if ptr.2 < size fr then
      let fr' := take ptr.2 fr ++ v :: drop ptr.2.+1%N fr in
      Some (setm mem ptr.1 fr')
    else None
  end.

Class allocator_spec (alloc : allocator) := {

  malloc_fresh : forall mem sz mem' bl b,
    malloc_fun mem bl sz = (mem',b) -> b \notin bl;

  malloc_get : forall mem sz mem' bl b off,
    malloc_fun mem bl sz = (mem',b) ->
      (off < sz)%ord -> getv mem' (b,off) = Some (VData 0);

  malloc_get_neq : forall mem bl b sz mem' b',
    malloc_fun mem bl sz = (mem',b') ->
    b <> b' ->
    mem' b = mem b;

(* Similar requirements on upd_mem are not necessary because they follow from
   the above and PartMaps.axioms. *)

  free_Some : forall (mem : memory) b fr,
    mem b = Some fr ->
    exists mem', free_fun mem b = Some mem';

  free_get_fail : forall mem mem' b,
    free_fun mem b = Some mem' -> mem' b = None;

  free_get : forall mem mem' b b',
    free_fun mem b = Some mem' ->
    b != b' -> mem' b' = mem b'

}.

Context `{syscall_regs t} `{allocator} `{memory_syscall_addrs t}.

Definition syscall_addrs := [:: malloc_addr; free_addr].

(* Check binop_denote. Check VData. SearchAbout [word Z]. *)
Definition lift_binop (f : binop) (x y : value) :=
  match f with
  | ADD => match x, y with
           | VData w1, VData w2 => Some (VData (binop_denote f w1 w2))
           | VPtr (b,w1), VData w2 => Some (VPtr (b, binop_denote f w1 w2))
           | VData w1, VPtr (b,w2) => Some (VPtr (b, binop_denote f w1 w2))
           | _, _ => None
           end
  | SUB => match x, y with
           | VData w1, VData w2 => Some (VData (binop_denote f w1 w2))
           | VPtr(b,w1), VData w2 => Some (VPtr (b, binop_denote f w1 w2))
           | VPtr(b1,w1), VPtr (b2,w2)=>
             if b1 == b2 then Some (VData (binop_denote f w1 w2))
             else None
           | _, _ => None
           end
  | EQ => match x, y with
         | VData w1, VData w2 => Some (VData (binop_denote f w1 w2))
         | VPtr(b1,w1), VPtr (b2,w2)=>
           if b1 == b2 then Some (VData (binop_denote f w1 w2))
           else None
          | _, _ => None
         end
  | _ => match x, y with
         | VData w1, VData w2 => Some (VData (binop_denote f w1 w2))
         | _, _ => None
         end
  end.

Inductive step : state -> state -> Prop :=
| step_nop : forall mem reg bl pc i,
             forall (PC :    getv mem pc = Some (VData i)),
             forall (INST :  decode_instr i = Some (Nop _)),
             step (mkState mem reg bl (VPtr pc)) (mkState mem reg bl (VPtr pc.+1))
| step_const : forall mem reg reg' bl pc i n r,
             forall (PC :    getv mem pc = Some (VData i)),
             forall (INST :  decode_instr i = Some (Const n r)),
             forall (UPD :   updm reg r (VData (swcast n)) = Some reg'),
             step (mkState mem reg bl (VPtr pc)) (mkState mem reg' bl (VPtr pc.+1))
| step_mov : forall mem reg reg' bl pc i r1 r2 w1,
             forall (PC :    getv mem pc = Some (VData i)),
             forall (INST :  decode_instr i = Some (Mov r1 r2)),
             forall (R1W :   reg r1 = Some w1),
             forall (UPD :   updm reg r2 w1 = Some reg'),
             step (mkState mem reg bl (VPtr pc)) (mkState mem reg' bl (VPtr pc.+1))
| step_binop : forall mem reg reg' bl pc i f r1 r2 r3 v1 v2 v3,
             forall (PC :    getv mem pc = Some (VData i)),
             forall (INST :  decode_instr i = Some (Binop f r1 r2 r3)),
             forall (R1W :   reg r1 = Some v1),
             forall (R2W :   reg r2 = Some v2),
             forall (BINOP : lift_binop f v1 v2 = Some v3),
             forall (UPD :   updm reg r3 v3 = Some reg'),
             step (mkState mem reg bl (VPtr pc)) (mkState mem reg' bl (VPtr pc.+1))
| step_load : forall mem reg reg' bl pc i r1 r2 pt v,
             forall (PC :    getv mem pc = Some (VData i)),
             forall (INST :  decode_instr i = Some (Load r1 r2)),
             forall (R1W :   reg r1 = Some (VPtr pt)),
             forall (MEM1 :  getv mem pt = Some v),
             forall (UPD :   updm reg r2 v = Some reg'),
             step (mkState mem reg bl (VPtr pc)) (mkState mem reg' bl (VPtr pc.+1))
| step_store : forall mem mem' reg bl pc ptr i r1 r2 v,
             forall (PC :    getv mem pc = Some (VData i)),
             forall (INST :  decode_instr i = Some (Store r1 r2)),
             forall (R1W :   reg r1 = Some (VPtr ptr)),
             forall (R2W :   reg r2 = Some v),
             forall (UPD :   updv mem ptr v = Some mem'),
             step (mkState mem reg bl (VPtr pc)) (mkState mem' reg bl (VPtr pc.+1))
| step_jump : forall mem reg bl pc i r pt,
             forall (PC :    getv mem pc = Some (VData i)),
             forall (INST :  decode_instr i = Some (Jump r)),
             forall (RW :    reg r = Some (VPtr pt)),
             step (mkState mem reg bl (VPtr pc)) (mkState mem reg bl (VPtr pt))
| step_bnz : forall mem reg bl pc i r n w,
             forall (PC :    getv mem pc = Some (VData i)),
             forall (INST :  decode_instr i = Some (Bnz r n)),
             forall (RW :    reg r = Some (VData w)),
             let             off_pc' := snd pc + (if w == 0
                                                  then 1
                                                  else swcast n) in
             step (mkState mem reg bl (VPtr pc)) (mkState mem reg bl (VPtr (fst pc,off_pc')))
| step_jal : forall mem reg reg' bl pc i r v,
             forall (PC :       getv mem pc = Some (VData i)),
             forall (INST :     decode_instr i = Some (Jal r)),
             forall (RW :       reg r = Some v),
             forall (UPD :      updm reg ra (VPtr (pc.+1)) = Some reg'),
             step (mkState mem reg bl (VPtr pc)) (mkState mem reg' bl v)
| step_malloc : forall mem mem' reg reg' bl sz b pc'
    (SIZE  : reg syscall_arg1 = Some (VData sz))
    (ALLOC : malloc_fun mem bl sz = (mem', b))
    (UPD   : updm reg syscall_ret (VPtr (b,0)) = Some reg')
    (RA    : reg ra = Some (VPtr pc')),
    step (mkState mem reg bl (VData malloc_addr)) (mkState mem' reg' (b::bl) (VPtr pc'))
| step_free : forall mem mem' reg ptr bl pc'
    (PTR  : reg syscall_arg1 = Some (VPtr ptr))
    (FREE : free_fun mem ptr.1 = Some mem')
    (RA   : reg ra = Some (VPtr pc')),
    step (mkState mem reg bl (VData free_addr)) (mkState mem' reg bl (VPtr pc'))
(*
| step_size : forall mem reg reg' b o fr bl pc'
    (PTR  : reg syscall_arg1 = Some (VPtr (b,o)))
    (MEM  : mem b = Some fr),
    let size := VData (Z_to_word (Z_of_nat (List.length fr))) in forall
    (UPD  : upd reg syscall_ret size = Some reg')
    (RA   : reg ra = Some (VPtr pc')),
    step (mkState mem reg bl (VData size_addr)) (mkState mem reg' bl (VPtr pc'))
*)
| step_base : forall mem reg reg' b o bl pc'
    (PTR  : reg syscall_arg1 = Some (VPtr (b,o)))
    (UPD  : updm reg syscall_ret (VPtr (b,0)) = Some reg')
    (RA   : reg ra = Some (VPtr pc')),
    step (mkState mem reg bl (VData base_addr)) (mkState mem reg' bl (VPtr pc'))
| step_eq : forall mem reg reg' v1 v2 bl pc'
    (V1   : reg syscall_arg1 = Some v1)
    (V2   : reg syscall_arg2 = Some v2),
    let v := VData (as_word (value_eq v1 v2)) in forall
    (UPD  : updm reg syscall_ret v = Some reg')
    (RA   : reg ra = Some (VPtr pc')),
    step (mkState mem reg bl (VData eq_addr)) (mkState mem reg' bl (VPtr pc')).

(* CH: Is the next part only a way of exposing mkState? *)

(* Not used anywhere
Variable initial_block : block.
*)

(* Hypothesis: alloc never returns initial_block.
   CH: Isn't this simply a consequence of alloc never returning
       something that is already allocated, and that the initial block
       is already allocated from the start?
   Q: Can the initial block be freed?
*)

Variable initial_pc : pointer.
Variable initial_mem  : memory.
Variable initial_regs : registers.
Hypothesis initial_ra : initial_regs ra = Some (VPtr initial_pc).

Definition initial_state : state :=
  mkState initial_mem initial_regs [::] (VPtr initial_pc).

End WithClasses.

End Abstract.

Arguments Abstract.state t block.
Arguments Abstract.memory t block.
Arguments Abstract.registers t block.

Canonical Abstract.state_eqType.
