Require Import List Arith ZArith.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import lib.utils lib.partial_maps common.common memory_safety.classes.

Import DoNotation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* This abstract machine corresponds to the one described under the name
"High-level abstract machine" in Catalin's notes on memory safety:
verif/stock-pico/notes/2013-05-memory-protection-no-free/main.pdf
*)

Import ListNotations.

Module Abstract.

Open Scope bool_scope.
Open Scope Z_scope.

Section WithClasses.

Context (t : machine_types).
Context {ops : machine_ops t}.

Variable block : eqType.

Definition pointer := (block * word t)%type.

Definition eq_pointer pt1 pt2 :=
  let '(b1,i1) := pt1 in
  let '(b2,i2) := pt2 in
  Z.eqb b1 b2 && i1 == i2.

Inductive value :=
| ValInt : word t -> value
| ValPtr : pointer -> value.

Definition frame := list value.

Import PartMaps.

Class abstract_params := {
  memory : Type;
  mem_class :> partial_map memory block frame;
  registers : Type;
  reg_class :> partial_map registers (reg t) value
}.

Class params_spec (ap : abstract_params) := {

  mem_axioms :> PartMaps.axioms (@mem_class ap);

  reg_axioms :> PartMaps.axioms (@reg_class ap)

}.

Context {ap : abstract_params}.

Open Scope word_scope.

Local Notation word := (word t).
Local Notation "x .+1" := (fst x, (add_word (snd x) (Z_to_word 1))).

Record state := mkState {
  mem : memory;
  regs : registers;
  pc : pointer
  }.

Class allocator := {

(* The Coq function representing the allocator. *)
  malloc_fun : memory -> word -> memory * block;

  free_fun : memory -> block -> option memory

}.

Class allocator_spec (alloc : allocator) := {

  malloc_get_fresh : forall mem sz mem' b,
    malloc_fun mem sz = (mem',b) -> get mem b = None;

  malloc_get : forall mem sz mem' b,
    malloc_fun mem sz = (mem',b) -> exists fr, get mem' b = Some fr;

(* Similar requirements on upd_mem are not necessary because they follow from
   the above and PartMaps.axioms. *)

  free_get_fail : forall mem mem' b,
    free_fun mem b = Some mem' -> get mem' b = None;

  free_get : forall mem mem' b b',
    free_fun mem b = Some mem' ->
    b != b' -> get mem' b' = get mem b'

}.

Context `{syscall_regs t} `{allocator} `{memory_syscall_addrs t}.

Definition syscall_addrs := [malloc_addr; free_addr].

Definition getv mem (ptr : pointer) :=
  match get mem (fst ptr) with
  | None => None
  | Some fr => index_list_Z (word_to_Z (snd ptr)) fr
  end.

(* Check binop_denote. Check ValInt. SearchAbout [word Z]. *)
Definition lift_binop (f : binop) (x y : value) :=
  match f with
  | ADD => match x, y with
           | ValInt w1, ValInt w2 => Some (ValInt (binop_denote f w1 w2))
           | ValPtr (b,w1), ValInt w2 => Some (ValPtr (b, binop_denote f w1 w2))
           | ValInt w1, ValPtr (b,w2) => Some (ValPtr (b, binop_denote f w1 w2))
           | _, _ => None
           end
  | SUB => match x, y with
           | ValInt w1, ValInt w2 => Some (ValInt (binop_denote f w1 w2))
           | ValPtr(b,w1), ValInt w2 => Some (ValPtr (b, binop_denote f w1 w2))
           | ValPtr(b1,w1), ValPtr (b2,w2)=>
             if b1 == b2 then Some (ValInt (binop_denote f w1 w2))
             else None
           | _, _ => None
           end
  | EQ => match x, y with
         | ValInt w1, ValInt w2 => Some (ValInt (binop_denote f w1 w2))
         | ValPtr(b1,w1), ValPtr (b2,w2)=>
           if b1 == b2 then Some (ValInt (binop_denote f w1 w2))
           else None
          | _, _ => None
         end
  | LEQ => match x, y with
         | ValInt w1, ValInt w2 => Some (ValInt (binop_denote f w1 w2))
         | ValPtr(b1,w1), ValPtr (b2,w2)=>
           if b1 == b2 then Some (ValInt (binop_denote f w1 w2))
           else None
          | _, _ => None
         end
  | _ => match x, y with
         | ValInt w1, ValInt w2 => Some (ValInt (binop_denote f w1 w2))
         | _, _ => None
         end
  end.

Definition bool_to_word (b : bool) : word :=
  Z_to_word (if b then 1%Z else 0%Z).

Definition total_eq (x y : value) : bool :=
  match x, y with
    | ValInt w1, ValInt w2 => w1 == w2
    | ValPtr(b1,o1), ValPtr (b2,o2) => (b1 == b2) && (o1 == o2)
    | _, _ => false
  end.

Inductive step : state -> state -> Prop :=
| step_nop : forall mem reg pc i,
             forall (PC :    getv mem pc = Some (ValInt i)),
             forall (INST :  decode_instr i = Some (Nop _)),
             step (mkState mem reg pc) (mkState mem reg pc.+1)
| step_const : forall mem reg reg' pc i n r,
             forall (PC :    getv mem pc = Some (ValInt i)),
             forall (INST :  decode_instr i = Some (Const _ n r)),
             forall (UPD :   upd reg r (ValInt (imm_to_word n)) = Some reg'),
             step (mkState mem reg pc) (mkState mem reg' pc.+1)
| step_mov : forall mem reg reg' pc i r1 r2 w1,
             forall (PC :    getv mem pc = Some (ValInt i)),
             forall (INST :  decode_instr i = Some (Mov _ r1 r2)),
             forall (R1W :   get reg r1 = Some w1),
             forall (UPD :   upd reg r2 w1 = Some reg'),
             step (mkState mem reg pc) (mkState mem reg' pc.+1)
| step_binop : forall mem reg reg' pc i f r1 r2 r3 v1 v2 v3,
             forall (PC :    getv mem pc = Some (ValInt i)),
             forall (INST :  decode_instr i = Some (Binop _ f r1 r2 r3)),
             forall (R1W :   get reg r1 = Some v1),
             forall (R2W :   get reg r2 = Some v2),
             forall (BINOP : lift_binop f v1 v2 = Some v3),
             forall (UPD :   upd reg r3 v3 = Some reg'),
             step (mkState mem reg pc) (mkState mem reg' pc.+1)
| step_load : forall mem reg reg' pc i r1 r2 pt v,
             forall (PC :    getv mem pc = Some (ValInt i)),
             forall (INST :  decode_instr i = Some (Load _ r1 r2)),
             forall (R1W :   get reg r1 = Some (ValPtr pt)),
             forall (MEM1 :  getv mem pt = Some v),
             forall (UPD :   upd reg r2 v = Some reg'),
             step (mkState mem reg pc) (mkState mem reg' pc.+1)
| step_store : forall mem mem' reg pc b off i r1 r2 fr fr' v,
             forall (PC :    getv mem pc = Some (ValInt i)),
             forall (INST :  decode_instr i = Some (Store _ r1 r2)),
             forall (R1W :   get reg r1 = Some (ValPtr (b,off))),
             forall (R2W :   get reg r2 = Some v),
             forall (MEM1 :  get mem b = Some fr),
             forall (UPDFR : update_list_Z (word_to_Z off) v fr = Some fr'),
             forall (UPD :   upd mem b fr' = Some mem'),
             step (mkState mem reg pc) (mkState mem' reg pc.+1)
| step_jump : forall mem reg pc i r pt,
             forall (PC :    getv mem pc = Some (ValInt i)),
             forall (INST :  decode_instr i = Some (Jump _ r)),
             forall (RW :    get reg r = Some (ValPtr pt)),
             step (mkState mem reg pc) (mkState mem reg pt)
| step_bnz : forall mem reg pc i r n w,
             forall (PC :    getv mem pc = Some (ValInt i)),
             forall (INST :  decode_instr i = Some (Bnz _ r n)),
             forall (RW :    get reg r = Some (ValInt w)),
             let             off_pc' := add_word (snd pc) (if w == Z_to_word 0
                                                   then Z_to_word 1
                                                   else imm_to_word n) in
             step (mkState mem reg pc) (mkState mem reg (fst pc,off_pc'))
| step_jal : forall mem reg reg' pc i r pt,
             forall (PC :       getv mem pc = Some (ValInt i)),
             forall (INST :     decode_instr i = Some (Jal _ r)),
             forall (RW :       get reg r = Some (ValPtr pt)),
             forall (UPD :      upd reg ra (ValPtr (pc.+1)) = Some reg'),
             step (mkState mem reg pc) (mkState mem reg' pt)
| step_malloc : forall mem mem' reg reg' pc i r sz b,
             forall (PC :       getv mem pc = Some (ValInt i)),
             forall (INST :     decode_instr i = Some (Jal _ r)),
             forall (RW :       get reg r = Some (ValInt malloc_addr)),
             forall (SIZE :     get reg syscall_arg1 = Some (ValInt sz)),
             forall (ALLOC :    malloc_fun mem sz = (mem', b)),
             forall (UPD :      upd reg syscall_ret (ValPtr (b,Z_to_word 0%Z)) = Some reg'),
             step (mkState mem reg pc) (mkState mem' reg' pc.+1)
| step_free : forall mem mem' reg pc i r ptr,
             forall (PC :       getv mem pc = Some (ValInt i)),
             forall (INST :     decode_instr i = Some (Jal _ r)),
             forall (RW :       get reg r = Some (ValInt free_addr)),
             forall (PTR :      get reg syscall_arg1 = Some (ValPtr ptr)),
             forall (ALLOC :    free_fun mem ptr.1 = Some mem'),
             step (mkState mem reg pc) (mkState mem' reg pc.+1)
| step_size : forall mem reg reg' pc i r b o fr,
    forall (PC   : getv mem pc = Some (ValInt i)),
    forall (INST : decode_instr i = Some (Jal _ r)),
    forall (RW   : get reg r = Some (ValInt size_addr)),
    forall (PTR  : get reg syscall_arg1 = Some (ValPtr (b,o))),
    forall (MEM  : get mem b = Some fr),
    let size := ValInt (Z_to_word (Z_of_nat (List.length fr))) in
    forall (UPD  : upd reg syscall_ret size = Some reg'),
    step (mkState mem reg pc) (mkState mem reg' pc.+1)
| step_base : forall mem reg reg' pc i r b o,
    forall (PC   : getv mem pc = Some (ValInt i)),
    forall (INST : decode_instr i = Some (Jal _ r)),
    forall (RW   : get reg r = Some (ValInt base_addr)),
    forall (PTR  : get reg syscall_arg1 = Some (ValPtr (b,o))),
    forall (UPD  : upd reg syscall_ret (ValPtr (b,Z_to_word 0%Z)) = Some reg'),
    step (mkState mem reg pc) (mkState mem reg' pc.+1)
| step_eq : forall mem reg reg' pc i r v1 v2,
    forall (PC   : getv mem pc = Some (ValInt i)),
    forall (INST : decode_instr i = Some (Jal _ r)),
    forall (RW   : get reg r = Some (ValInt eq_addr)),
    forall (V1   : get reg syscall_arg1 = Some v1),
    forall (V2   : get reg syscall_arg2 = Some v2),
    let v := ValInt (bool_to_word (total_eq v1 v2)) in
    forall (UPD  : upd reg syscall_ret v = Some reg'),
    step (mkState mem reg pc) (mkState mem reg' pc.+1).

Variable initial_block : block.

(* Hypothesis: alloc never returns initial_block. *)

Variable initial_pc : pointer.
Variable initial_mem  : memory.
Variable initial_registers : registers.
Hypothesis initial_ra : get initial_registers ra = Some (ValPtr initial_pc).

Definition initial_state : state :=
  mkState initial_mem initial_registers initial_pc.

End WithClasses.

End Abstract.

Arguments Abstract.state t {_ _}.
Arguments Abstract.memory t {_ _}.
Arguments Abstract.registers t {_ _}.