Require Import List Arith ZArith.
Require Import Coq.Classes.SetoidDec.
Require Import utils common.

Set Implicit Arguments.

(* This abstract machine corresponds to the one described under the name
"Slightly less high-level abstract machine" in Catalin's notes on memory safety:
verif/stock-pico/notes/2013-05-memory-protection-no-free/main.pdf

It is an intermediate between a high level memory safety machine and the
concrete stock pico machine. *)

(* Main features:
- pointer/integer distinction
- labels on memory location expressing the memory safety (distinct from TMU tags)
*)

(* APT:
   - Nothing stops you from jumping or branching or just falling through
     to a system call address, which surely does not make sense.
     CH: Kernel memory should already be abstracted away at this point,
         thus unaccessible.
   - Nothing describes the extent (as opposed to just the entry point) of 
     system calls.
     CH: Why is the extent relevant for anything? They live outside
         user memory anyway.
*)

Import DoNotation.
Import ListNotations.

Module QuasiAbstract.

Open Scope bool_scope.
Open Scope Z_scope.

Section WithClasses.

Context (t : machine_types).
Context {ops : machine_ops t}.

Definition block := word t.

Inductive type :=
| TypeInt
| TypePointer : block -> type.

(* CH: calling this tag would be better *)
Inductive label :=
| LabelValue : type -> label
| LabelMemory : block -> type -> label.

Local Notation INT := TypeInt.
Local Notation PTR := TypePointer.
Local Notation "V( ty )" := (LabelValue ty) (at level 4).
Notation "M( n , ty )" := (LabelMemory n ty) (at level 4).

Record atom := mkatom { val : word t; atom_label : label }.

Notation "x @ t" := (mkatom x t) (at level 5, format "x '@' t").

Class abstract_params := {
  memory : Type;
  registers : Type;

  get_mem : memory -> word t -> option atom;
  upd_mem : memory -> word t -> atom -> option memory;

  (* Contrary to concrete machine, here register access and update
     might fail, since they might correspond to kernel registers *)

  get_reg : registers -> reg t -> option (atom);
  upd_reg : registers -> reg t -> atom -> option registers

}.

Class params_spec (ap : abstract_params) := {

  mem_axioms :> PartMaps.axioms get_mem upd_mem;

  reg_axioms :> PartMaps.axioms get_reg upd_reg

}.

Context {ap : abstract_params}.

Local Coercion Z_to_word : Z >-> word.
Open Scope word_scope.

Local Notation word := (word t).
Local Notation "x .+1" := (add_word x (Z_to_word 1)) (at level 9).

Record state := mkState {
  mem : memory;
  regs : registers;
  pc : atom
}.

Record syscall := Syscall {
  address : word;
  sem : state -> option state
}.

Class allocator := {

(* "Address" of the malloc system call. *)
  alloc_addr : word;

(* The register used to read the size of the block to be allocated
   and return the pointer to that block. May change if we have a
   calling convention for system calls. *)
  alloc_reg : reg t;

(* The Coq function representing the allocator. *)
  alloc_fun : state -> option (state * block)

}.

Class allocator_spec (alloc : allocator) := {

  alloc_get_fresh : forall s s' b,
    alloc_fun s = Some (s',b) -> get_mem (mem s) b = None;

  alloc_get : forall s s' b,
    alloc_fun s = Some (s',b) -> exists fr, get_mem (mem s') b = Some fr

(* Similar requirements on upd_mem are not necessary because they follow from
   the above and PartMaps.axioms. *)

}.

Context `{allocator}.

Definition malloc : syscall :=
{| address := alloc_addr;
   sem := fun s => do r <- alloc_fun s;
                   let '(s',b) := r in
                   do regs' <- upd_reg (regs s') alloc_reg (Z_to_word 0)@V(PTR b);
                   Some (mkState (mem s') regs' (pc s'))
|}.

Variable othercalls : list syscall.

Let table := malloc :: othercalls.

Definition get_syscall (addr : word) : option syscall :=
  find (fun sc => address sc ==b addr) table.

Definition lift_binop (f : binop) (x y : atom) :=
  match f with
  | ADD => match x, y with
           | w1@V(INT), w2@V(INT) => Some (binop_denote f w1 w2, INT)
           | w1@V(PTR b), w2@V(INT) => Some (binop_denote f w1 w2, PTR b)
           | w1@V(INT), w2@V(PTR b) => Some (binop_denote f w1 w2, PTR b)
           | _, _ => None
           end
  | SUB => match x, y with
           | w1@V(INT), w2@V(INT) => Some (binop_denote f w1 w2, INT)
           | w1@V(PTR b), w2@V(INT) => Some (binop_denote f w1 w2, PTR b)
           | w1@V(PTR b1), w2@V(PTR b2) =>
             if b1 ==b b2 then Some (binop_denote f w1 w2, INT)
             else None
           | _, _ => None
           end
  | EQ => match x, y with
          | w1@V(INT), w2@V(INT) => Some (binop_denote f w1 w2, INT)
          | w1@V(PTR b1), w2@V(PTR b2) =>
            if b1 ==b b2 then Some (binop_denote f w1 w2, INT)
            else Some (Z_to_word (0%Z), INT) (* 0 for false *)
          | _, _ => None
          end
  | _ => match x, y with
         | w1@V(INT), w2@V(INT) => Some (binop_denote f w1 w2, INT)
         | _, _ => None
         end
  end.

Inductive step : state -> state -> Prop :=
| step_nop : forall mem reg pc b i,
             forall (PC :    get_mem mem pc = Some i@M(b,INT)),
             forall (INST :  decode_instr i = Some (Nop _)),
             step (mkState mem reg pc@V(PTR b)) (mkState mem reg pc.+1@V(PTR b))
| step_const : forall mem reg reg' pc b i n r,
             forall (PC :    get_mem mem pc = Some i@M(b,INT)),
             forall (INST :  decode_instr i = Some (Const _ n r)),
             forall (UPD :   upd_reg reg r (imm_to_word n)@V(INT) = Some reg'),
             step (mkState mem reg pc@V(PTR b)) (mkState mem reg' pc.+1@V(PTR b))
| step_mov : forall mem reg reg' pc b i r1 r2 w ty,
             forall (PC :    get_mem mem pc = Some i@M(b,INT)),
             forall (INST :  decode_instr i = Some (Mov _ r1 r2)),
             forall (R1W :   get_reg reg r1 = Some w@V(ty)),
             forall (UPD :   upd_reg reg r2 w@V(ty) = Some reg'),
             step (mkState mem reg pc@V(PTR b)) (mkState mem reg' pc.+1@V(PTR b))
| step_binop : forall mem reg reg' pc b i f r1 r2 r3 w1 w2 ty1 ty2 w3 ty3,
             forall (PC :    get_mem mem pc = Some i@M(b,INT)),
             forall (INST :  decode_instr i = Some (Binop _ f r1 r2 r3)),
             forall (R1W :   get_reg reg r1 = Some w1@V(ty1)),
             forall (R2W :   get_reg reg r2 = Some w2@V(ty2)),
             forall (BINOP : lift_binop f w1@V(ty1) w2@V(ty2) = Some (w3,ty3)),
             forall (UPD :   upd_reg reg r3 w3@V(ty3) = Some reg'),
             step (mkState mem reg pc@V(PTR b)) (mkState mem reg' pc.+1@V(PTR b))
| step_load : forall mem reg reg' pc b i r1 r2 w1 w2 n ty,
             forall (PC :    get_mem mem pc = Some i@M(b,INT)),
             forall (INST :  decode_instr i = Some (Load _ r1 r2)),
             forall (R1W :   get_reg reg r1 = Some w1@V(PTR n)),
             forall (MEM1 :  get_mem mem w1 = Some w2@M(n,ty)),
             forall (UPD :   upd_reg reg r2 w2@V(ty) = Some reg'),
             step (mkState mem reg pc@V(PTR b)) (mkState mem reg' pc.+1@V(PTR b))
| step_store : forall mem mem' reg pc b i r1 r2 w1 w2 w3 n ty ty',
             forall (PC :    get_mem mem pc = Some i@M(b,INT)),
             forall (INST :  decode_instr i = Some (Store _ r1 r2)),
             forall (R1W :   get_reg reg r1 = Some w1@V(PTR n)),
             forall (R2W :   get_reg reg r2 = Some w2@V(ty)),
             (* The line below checks that the block was allocated *)
             forall (MEM1 :  get_mem mem w1 = Some w3@M(n,ty')),
             forall (UPD :   upd_mem mem w1 w2@M(n,ty) = Some mem'),
             step (mkState mem reg pc@V(PTR b)) (mkState mem' reg pc.+1@V(PTR b))
| step_jump : forall mem reg pc b b' i r w,
             forall (PC :    get_mem mem pc = Some i@M(b,INT)),
             forall (INST :  decode_instr i = Some (Jump _ r)),
             forall (RW :    get_reg reg r = Some w@V(PTR b')),
             step (mkState mem reg pc@V(PTR b)) (mkState mem reg w@V(PTR b'))
| step_bnz : forall mem reg pc b i r n w,
             forall (PC :    get_mem mem pc = Some i@M(b,INT)),
             forall (INST :  decode_instr i = Some (Bnz _ r n)),
             forall (RW :    get_reg reg r = Some w@V(INT)),
             let             pc' := add_word pc (if w ==b Z_to_word 0
                                                   then Z_to_word 1
                                                   else imm_to_word n) in
             step (mkState mem reg pc@V(PTR b)) (mkState mem reg pc'@V(PTR b))
| step_jal : forall mem reg reg' pc b b' i r w,
             forall (PC :       get_mem mem pc = Some i@M(b,INT)),
             forall (INST :     decode_instr i = Some (Jal _ r)),
             forall (RW :       get_reg reg r = Some w@V(PTR b')),
             forall (NOTCALL :  get_syscall w = None),
             forall (UPD :      upd_reg reg ra (pc.+1)@V(PTR b) = Some reg'),
             step (mkState mem reg pc@V(PTR b)) (mkState mem reg' w@V(PTR b'))
| step_syscall : forall mem reg pc b i r w st' sc,
                 forall (PC :      get_mem mem pc = Some i@M(b,INT)),
                 forall (INST :    decode_instr i = Some (Jal _ r)),
                 forall (RW :      get_reg reg r = Some w@V(INT)),
                 forall (GETCALL:  get_syscall w = Some sc),
                 forall (CALL :    sem sc (mkState mem reg pc@V(PTR b)) = Some st'),
                 step (mkState mem reg pc@V(PTR b)) st'.

Variable initial_block : block.

(* Hypothesis: alloc never returns initial_block. *)

Variable initial_pc : word.
Variable initial_mem  : memory.
Variable initial_registers : registers.
Hypothesis initial_ra : get_reg initial_registers ra = Some initial_pc@V(PTR initial_block).

Definition initial_state := (initial_mem, initial_registers, initial_pc@V(PTR initial_block)).

End WithClasses.

Module Notations.

Notation INT := (TypeInt _).
Notation PTR := (TypePointer _).
Notation "V( ty )" := (LabelValue ty) (at level 4).
Notation "M( n , ty )" := (LabelMemory n ty) (at level 4).

Notation "x @ t" := (mkatom x t) (at level 5, format "x '@' t").

End Notations.

End QuasiAbstract.

Arguments QuasiAbstract.state t {_}.
Arguments QuasiAbstract.memory t {_}.
Arguments QuasiAbstract.registers t {_}.
Arguments QuasiAbstract.syscall t {_}.
