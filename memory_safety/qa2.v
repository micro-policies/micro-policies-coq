Require Import List Arith ZArith.
Require Vector.

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

(* This alternative version illustrates one possible way for handling
   instruction memory in a way that is more uniform with data memory.
   Basic idea: instructions live in memory blocks just like
   (allocated) data, with block numbers drawn from the same space as
   for allocated data.  Indeed, instructions and data can live in the
   same block, and data can be written to an allocated block and later
   interpreted as instructions.  Instructions are just (decodable)
   integers.  Instruction pointers carry pointer tags in the obvious
   way.  The machine state includes a "current instruction block" in
   addition to the PC, and the instruction pointed to by the PC must
   be tagged with this block at each step (else the machine gets
   stuck).  
   CH: another way to look at this is that the pc is an atom stamped
       with V(b), like normal pointers living in registers are; this
       would correspond closer to what the concrete machine will do
   APT: Agreed (assuming you meant V(PTR b) ) 

   To get things bootstrapped, one block number is reserved
   (i.e. should not be returned later by alloc) to be the initial
   state's current instruction block, and the initial PC is an address
   in this block.  The full contents of this initial block, which
   could include non-instruction data too, are part of the initial
   machine state.  The initial value register ra is set to
   (initial-block,initial-pc), to allow boot-up code to perform
   absolute jumps within the block and to access non-instruction data
   values.  If desired, the initial memory state could contain other
   blocks as well (also reserved against being returned by alloc); if
   so, they need to be reachable via pointer chains rooted at globals
   in initial block.
   CH: not sure I understand what the ra part is for or how it works
   APT: I'm assuming blocks are abstract and cannot be forged. So the
   machine cannot access instructions or data in the initial block unless
   it is started with a "capability" to that block -- which is what goes
   in ra (it could go anywhere, but ra is already special).

   With this machinery in place, there are several options for
   handling system call entrypoints.  One, reflected in the code
   below, is that they are just special addresses in the initial
   block.  It might be cleaner to put them in (an) other special
   block(s) instead; but in this case, access to calls would need to
   indirect through a global in the initial block.
   CH: My assumption was that kernel memory is completely separate
       from allocatable user memory (i.e. memory safety builds on top
       of everything we're already doing for kernel protection). So
       the V(INT) tag on the syscall "pointer" in Maxime's code seems
       just fine. The address is outside "user space" anyway.
   APT: OK, I think this makes sense for this machine, where we have
       tags available to tell the difference.  (I continue to be 
       completely unconvinced by the more generic abstract machine
       in kernel/abstract.v, where there are no tags, and the magic 
       list of syscall entry points can "punch holes" in the memory 
       space.) 

   Note: in this version, there really seems no point in modelling
   registers and memories as containing (arbitrary) atoms; instead,
   registers always contain (value,type) and memory locations always
   contain (value,block,type).  But I haven't changed this, since
   possibly the atom-based form is somehow usefully closer to the
   concrete machine?
   CH: What you propose seems like a reasonable alternative.
       The current thing is indeed a bit closer to the concrete machine.

*)

Import ListNotations.

Module Abstract.

Open Scope bool_scope.
Open Scope Z_scope.

Section WithClasses.

Context (t : machine_types).
Context {ops : machine_ops t}.

Definition block := Z. 

Inductive type :=
| TypeInt
| TypePointer : block -> type.

Inductive label :=
| LabelValue : type -> label
| LabelMemory : block -> type -> label.

Local Notation INT := TypeInt.
Local Notation PTR := TypePointer.
Local Notation "V( ty )" := (LabelValue ty) (at level 4).

(*
Notation "V(Int)" := (LabelValue TypeInt) (at level 4).
Notation "V(Ptr n )" := (LabelValue (TypeDPointer n)) (at level 4).
*)
(*
Notation "M( n , Int)" := (LabelMemory n TypeInt) (at level 4).
Notation "M( n , Ptr)" := (LabelMemory n TypeDPointer) (at level 4).
*)
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

  mem_axioms : PartMaps.axioms get_mem upd_mem;

  reg_axioms : PartMaps.axioms get_reg upd_reg

}.

Context {ap : abstract_params}.

Local Coercion Z_to_word : Z >-> word.
Open Scope word_scope.

Local Notation word := (word t).
Local Notation "x .+1" := (add_word x (Z_to_word 1)) (at level 60).

Definition state := (memory * registers * word (* pc *) * block)%type.

Record syscall := Syscall {
  address : word;
  sem : state -> option state
}.

Variable table : list syscall.

Definition get_syscall (addr : word) : option syscall :=
  find (fun sc => eq_word (address sc) addr) table.

Inductive step : state -> state -> Prop :=
| step_nop : forall mem reg pc b i,
             forall (PC :    get_mem mem pc = Some i@M(b,INT)),
             forall (INST :  decode_instr i = Some (Nop _)),
             step (mem,reg,pc,b) (mem,reg,pc.+1,b)
| step_const : forall mem reg reg' pc b i n r,
             forall (PC :    get_mem mem pc = Some i@M(b,INT)),
             forall (INST :  decode_instr i = Some (Const _ n r)),
             forall (UPD :   upd_reg reg r (imm_to_word n)@V(INT) = Some reg'),   
             step (mem,reg,pc,b) (mem,reg',pc.+1,b)
| step_mov : forall mem reg reg' pc b i r1 r2 w1,
             forall (PC :    get_mem mem pc = Some i@M(b,INT)),
             forall (INST :  decode_instr i = Some (Mov _ r1 r2)),
             forall (R1W :   get_reg reg r1 = Some w1),
             forall (UPD :   upd_reg reg r2 w1 = Some reg'),
             step (mem,reg,pc,b) (mem,reg',pc.+1,b)
| step_binop : forall mem reg reg' pc b i f r1 r2 r3 w1 w2,
             forall (PC :    get_mem mem pc = Some i@M(b,INT)),
             forall (INST :  decode_instr i = Some (Binop _ f r1 r2 r3)),
             forall (R1W :   get_reg reg r1 = Some w1@V(INT)),
             forall (R2W :   get_reg reg r2 = Some w2@V(INT)),
             forall (UPD :   upd_reg reg r3 (binop_denote f w1 w2)@V(INT) = Some reg'),
             step (mem,reg,pc,b) (mem,reg',pc.+1,b)
(* APT: what about address arithmetic? 
users/catalin/internships/micro-policies/micro-policies.pdf allows I/I P/I I/P for add
verif/stock-pico/notes/2013-05-memory-protection-no-free/main.pdf has offP and (buggy?) subP
*)
| step_load : forall mem reg reg' pc b i r1 r2 w1 w2 n ty,
             forall (PC :    get_mem mem pc = Some i@M(b,INT)),
             forall (INST :  decode_instr i = Some (Load _ r1 r2)),
             forall (R1W :   get_reg reg r1 = Some w1@V(PTR n)),
             forall (MEM1 :  get_mem mem w1 = Some w2@M(n,ty)),
             forall (UPD :   upd_reg reg r2 w2@V(ty) = Some reg'),
             step (mem,reg,pc,b) (mem,reg',pc.+1,b)
| step_store : forall mem mem' reg pc b i r1 r2 w1 w2 w3 n ty,
             forall (PC :    get_mem mem pc = Some i@M(b,INT)),
             forall (INST :  decode_instr i = Some (Store _ r1 r2)),
             forall (R1W :   get_reg reg r1 = Some w1@V(PTR n)),
             forall (R2W :   get_reg reg r2 = Some w2@V(ty)),
             forall (MEM1 :  get_mem mem w1 = Some w3@M(n,ty)),
             forall (UPD :   upd_mem mem w1 w2@M(n,ty) = Some mem'),
             step (mem,reg,pc,b) (mem',reg,pc.+1,b)
| step_jump : forall mem reg pc b b' i r w,
             forall (PC :    get_mem mem pc = Some i@M(b,INT)),
             forall (INST :  decode_instr i = Some (Jump _ r)),
             forall (RW :    get_reg reg r = Some w@V(PTR b')),
             step (mem,reg,pc,b) (mem,reg,w,b')
| step_bnz : forall mem reg pc b i r n w,
             forall (PC :    get_mem mem pc = Some i@M(b,INT)),
             forall (INST :  decode_instr i = Some (Bnz _ r n)),
             forall (RW :    get_reg reg r = Some w@V(INT)),
             let             pc' := add_word pc (if w =? Z_to_word 0 
                                                   then Z_to_word 1 
                                                   else imm_to_word n) in
             step (mem,reg,pc,b) (mem,reg,pc',b)
| step_jal : forall mem reg reg' pc b b' i r w,
             forall (PC :       get_mem mem pc = Some i@M(b,INT)),
             forall (INST :     decode_instr i = Some (Jal _ r)),
             forall (RW :       get_reg reg r = Some w@V(PTR b')),
             forall (NOTCALL :  get_syscall w = None),
             forall (UPD :      upd_reg reg ra (pc.+1)@V(PTR b) = Some reg'),
             step (mem,reg,pc,b) (mem,reg',w,b')
| step_syscall : forall mem reg pc i b r w b' st' sc,
                 forall (PC :      get_mem mem pc = Some i@M(b,INT)),
                 forall (INST :    decode_instr i = Some (Jal _ r)),
                 forall (RW :      get_reg reg r = Some w@V(PTR b')),
                 forall (GETCALL:  get_syscall w = Some sc),
                 forall (CALL :    sem sc (mem,reg,pc,b) = Some st'),
                 step (mem,reg,pc,b) st'.

Variable initial_block : block.

(* Hypothesis: alloc never returns initial_block. *)

Variable initial_pc : word.
Variable initial_mem  : memory.
Variable initial_registers : registers.
Hypothesis initial_ra : get_reg initial_registers ra = Some initial_pc@V(PTR initial_block).

Definition initial_state := (initial_mem, initial_registers, initial_pc, initial_block).

End WithClasses.

End Abstract.

Arguments Abstract.state t {_}.
Arguments Abstract.memory t {_}.
Arguments Abstract.registers t {_}.
Arguments Abstract.syscall t {_}.
