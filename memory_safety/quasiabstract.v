Require Import List Arith ZArith.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
Require Import lib.utils lib.ordered lib.partial_maps common.common.
Require Import memory_safety.classes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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
| LabelMemory : block -> type -> label
| LabelFree.

Local Notation INT := TypeInt.
Local Notation PTR := TypePointer.
Local Notation "V( ty )" := (LabelValue ty) (at level 4).
Notation "M( n , ty )" := (LabelMemory n ty) (at level 4).
Local Notation FREE := LabelFree.

Record atom := mkatom { val : word t; atom_label : label }.

Notation "x @ t" := (mkatom x t) (at level 5, format "x '@' t").

Import PartMaps.

Class abstract_params := {
  memory : Type;
  mem_class :> partial_map memory (word t) atom;
  registers : Type;
  reg_class :> partial_map registers (reg t) atom
}.

Class params_spec (ap : abstract_params) := {

  mem_axioms :> PartMaps.axioms (@mem_class ap);

  reg_axioms :> PartMaps.axioms (@reg_class ap)

}.

Context `{ap : abstract_params, syscall_regs t, memory_syscall_addrs t}.

Open Scope word_scope.

Local Notation word := (word t).
Local Notation "x .+1" := (add_word x (Z_to_word 1)).

Record block_info := mkBlockInfo {
  block_base : word;
  block_size : word;
  block_color : option word
}.

Section BlockInfoEq.

(*
Variable info1 info2 : block_info.
*)

Definition block_info_eq :=
  [rel u v : block_info | [&& block_base u == block_base v,
                           block_size u == block_size v &
                           block_color u == block_color v]].

Lemma block_info_eqP : Equality.axiom block_info_eq.
Proof.
move=> [x1 x2 x3] [y1 y2 y3] /=; apply: (iffP and3P) => [[]|[<- <- <-]] //=.
by repeat move/eqP->.
Qed.

Definition block_info_eqMixin := EqMixin block_info_eqP.
Canonical block_info_eqType := Eval hnf in EqType block_info block_info_eqMixin.

End BlockInfoEq.

Record state := mkState {
  mem : memory;
  regs : registers;
  internal : word * list block_info;
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

(*
Class allocator_spec (alloc : allocator) := {

  alloc_get_fresh : forall s s' b,
    alloc_fun s = Some (s',b) -> get (mem s) b = None;

  alloc_get : forall s s' b,
    alloc_fun s = Some (s',b) -> exists fr, get (mem s') b = Some fr

(* Similar requirements on upd are not necessary because they follow from
   the above and PartMaps.axioms. *)

}.

Context `{allocator}.
*)

Definition malloc_fun st : option state :=
  let: pcv@pcl := pc st in
  let: (color,info) := internal st in
  do! sz <- get (regs st) syscall_arg1;
  match sz with
    | sz@V(INT) =>
      match compare 0 sz with
        | Lt =>
          if ohead [seq x <- info | ((sz <=? block_size x) && ~~ is_some (block_color x))%ordered] is Some x then
          let i := index x info in
          let block1 := mkBlockInfo (block_base x) sz (Some color) in
          let pre := take i info in
          let post := drop (i+1) info in
          let info' :=
              if sz == block_size x then
                pre ++ [block1] ++ post
              else
                let block2 := mkBlockInfo (block_base x + sz) (block_size x - sz) None in
                pre ++ [block1;block2] ++ post
          in
          let P := fun n => memory in
          let upd_fun := fun n acc =>
            if @upd memory _ _ (@mem_class _) acc (block_base x + (Z_to_word (Z.of_nat n))) (0@M(color,INT)) is Some mem then mem else acc
          in
          let mem' := nat_rect P (mem st) upd_fun (Z.to_nat (word_to_Z sz)) in
          let regs' := if @upd registers _ _ (@reg_class _) (regs st) syscall_ret ((block_base x)@V(PTR color)) is Some regs' then regs' else regs st in
          let color' := color + 1 in
          Some (mkState mem' regs' (color',info') (pcv.+1@pcl))
          else None
        | _ => None
      end
    | _ => None
  end.

Definition def_info : block_info :=
  mkBlockInfo 0 0 None.

(* TODO: avoid memory fragmentation *)
Definition free_fun st : option state :=
  let: pcv@pcl := pc st in
  let: (color,info) := internal st in
  do! ptr <- get (regs st) syscall_arg1;
    (* Removing the return clause makes Coq loop... *)
  match ptr return option state with
  | ptr@V(PTR color) =>
    if ohead [seq x <- info | block_color x == Some color] is Some x then
      let i := index x info in
      if (block_base x <=? ptr <? block_base x + block_size x) then
        let P := fun n => memory in
        let upd_fun := fun n acc =>
          if upd acc (block_base x + Z_to_word (Z.of_nat n)) (0@FREE) is Some mem then mem else acc
        in
        let mem' := nat_rect P (mem st) upd_fun (Z.to_nat (word_to_Z (block_size x))) in
        let info' := set_nth def_info info i (mkBlockInfo (block_base x) (block_size x) None)
        in
        Some (mkState mem' (regs st) (color,info') pcv.+1@pcl)
        else None
    else None
  | _ => None
  end.

Definition malloc : syscall :=
  {| address := malloc_addr;
     sem := malloc_fun
  |}.

Definition free : syscall :=
  {| address := free_addr;
     sem := free_fun
  |}.

Let syscalls := [malloc;free].

Definition get_syscall (addr : word) : option syscall :=
  List.find (fun sc => address sc == addr) syscalls.

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
             if b1 == b2 then Some (binop_denote f w1 w2, INT)
             else None
           | _, _ => None
           end
  | EQ => match x, y with
          | w1@V(INT), w2@V(INT) => Some (binop_denote f w1 w2, INT)
          | w1@V(PTR b1), w2@V(PTR b2) =>
            if b1 == b2 then Some (binop_denote f w1 w2, INT)
            else None
          | _, _ => None
          end
  | LEQ => match x, y with
          | w1@V(INT), w2@V(INT) => Some (binop_denote f w1 w2, INT)
          | w1@V(PTR b1), w2@V(PTR b2) =>
            if b1 == b2 then Some (binop_denote f w1 w2, INT)
            else None
          | _, _ => None
          end
  | _ => match x, y with
         | w1@V(INT), w2@V(INT) => Some (binop_denote f w1 w2, INT)
         | _, _ => None
         end
  end.

Inductive step : state -> state -> Prop :=
| step_nop : forall mem reg ist pc b i,
             forall (PC :    get mem pc = Some i@M(b,INT)),
             forall (INST :  decode_instr i = Some (Nop _)),
             step (mkState mem reg ist pc@V(PTR b)) (mkState mem reg ist pc.+1@V(PTR b))
| step_const : forall mem reg reg' ist pc b i n r,
             forall (PC :    get mem pc = Some i@M(b,INT)),
             forall (INST :  decode_instr i = Some (Const _ n r)),
             forall (UPD :   upd reg r (imm_to_word n)@V(INT) = Some reg'),
             step (mkState mem reg ist pc@V(PTR b)) (mkState mem reg' ist pc.+1@V(PTR b))
| step_mov : forall mem reg reg' ist pc b i r1 r2 w ty,
             forall (PC :    get mem pc = Some i@M(b,INT)),
             forall (INST :  decode_instr i = Some (Mov _ r1 r2)),
             forall (R1W :   get reg r1 = Some w@V(ty)),
             forall (UPD :   upd reg r2 w@V(ty) = Some reg'),
             step (mkState mem reg ist pc@V(PTR b)) (mkState mem reg' ist pc.+1@V(PTR b))
| step_binop : forall mem reg reg' ist pc b i f r1 r2 r3 w1 w2 ty1 ty2 w3 ty3,
             forall (PC :    get mem pc = Some i@M(b,INT)),
             forall (INST :  decode_instr i = Some (Binop _ f r1 r2 r3)),
             forall (R1W :   get reg r1 = Some w1@V(ty1)),
             forall (R2W :   get reg r2 = Some w2@V(ty2)),
             forall (BINOP : lift_binop f w1@V(ty1) w2@V(ty2) = Some (w3,ty3)),
             forall (UPD :   upd reg r3 w3@V(ty3) = Some reg'),
             step (mkState mem reg ist pc@V(PTR b)) (mkState mem reg' ist pc.+1@V(PTR b))
| step_load : forall mem reg reg' ist pc b i r1 r2 w1 w2 n ty,
             forall (PC :    get mem pc = Some i@M(b,INT)),
             forall (INST :  decode_instr i = Some (Load _ r1 r2)),
             forall (R1W :   get reg r1 = Some w1@V(PTR n)),
             forall (MEM1 :  get mem w1 = Some w2@M(n,ty)),
             forall (UPD :   upd reg r2 w2@V(ty) = Some reg'),
             step (mkState mem reg ist pc@V(PTR b)) (mkState mem reg' ist pc.+1@V(PTR b))
| step_store : forall mem mem' reg ist pc b i r1 r2 w1 w2 w3 n ty ty',
             forall (PC :    get mem pc = Some i@M(b,INT)),
             forall (INST :  decode_instr i = Some (Store _ r1 r2)),
             forall (R1W :   get reg r1 = Some w1@V(PTR n)),
             forall (R2W :   get reg r2 = Some w2@V(ty)),
             (* The line below checks that the block was allocated *)
             forall (MEM1 :  get mem w1 = Some w3@M(n,ty')),
             forall (UPD :   upd mem w1 w2@M(n,ty) = Some mem'),
             step (mkState mem reg ist pc@V(PTR b)) (mkState mem' reg ist pc.+1@V(PTR b))
| step_jump : forall mem reg ist pc b b' i r w,
             forall (PC :    get mem pc = Some i@M(b,INT)),
             forall (INST :  decode_instr i = Some (Jump _ r)),
             forall (RW :    get reg r = Some w@V(PTR b')),
             step (mkState mem reg ist pc@V(PTR b)) (mkState mem reg ist w@V(PTR b'))
| step_bnz : forall mem reg ist pc b i r n w,
             forall (PC :    get mem pc = Some i@M(b,INT)),
             forall (INST :  decode_instr i = Some (Bnz _ r n)),
             forall (RW :    get reg r = Some w@V(INT)),
             let             pc' := add_word pc (if w == Z_to_word 0
                                                   then Z_to_word 1
                                                   else imm_to_word n) in
             step (mkState mem reg ist pc@V(PTR b)) (mkState mem reg ist pc'@V(PTR b))
| step_jal : forall mem reg reg' ist pc b b' i r w,
             forall (PC :       get mem pc = Some i@M(b,INT)),
             forall (INST :     decode_instr i = Some (Jal _ r)),
             forall (RW :       get reg r = Some w@V(PTR b')),
(*             forall (NOTCALL :  get_syscall w = None), *)
             forall (UPD :      upd reg ra (pc.+1)@V(PTR b) = Some reg'),
             step (mkState mem reg ist pc@V(PTR b)) (mkState mem reg' ist w@V(PTR b'))
| step_syscall : forall mem reg ist pc b i r w st' sc,
                 (* XXX: completely off compared to current model of system calls *)
                 forall (PC :      get mem pc = Some i@M(b,INT)),
                 forall (INST :    decode_instr i = Some (Jal _ r)),
                 forall (RW :      get reg r = Some w@V(INT)),
                 forall (GETCALL:  get_syscall w = Some sc),
                 forall (CALL :    sem sc (mkState mem reg ist pc@V(PTR b)) = Some st'),
                 step (mkState mem reg ist pc@V(PTR b)) st'.

Variable initial_block : block.

(* Hypothesis: alloc never returns initial_block. *)

Variable initial_pc : word.
Variable initial_mem  : memory.
Variable initial_registers : registers.
Hypothesis initial_ra : get initial_registers ra = Some initial_pc@V(PTR initial_block).

Definition initial_state := (initial_mem, initial_registers, initial_pc@V(PTR initial_block)).

End WithClasses.

Module Notations.

Notation INT := (TypeInt _).
Notation PTR := TypePointer.
Notation "V( ty )" := (LabelValue ty) (at level 4).
Notation "M( n , ty )" := (LabelMemory n ty) (at level 4).

Notation "x @ t" := (mkatom x t) (at level 5, format "x '@' t").

End Notations.

End QuasiAbstract.

Arguments QuasiAbstract.state t {_}.
Arguments QuasiAbstract.memory t {_}.
Arguments QuasiAbstract.registers t {_}.
Arguments QuasiAbstract.syscall t {_}.
