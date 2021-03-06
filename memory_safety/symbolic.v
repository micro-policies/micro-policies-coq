From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype ssrint.
From extructures Require Import ord fmap.
From CoqUtils Require Import hseq word nominal.
Require Import lib.utils common.types.
Require Import symbolic.symbolic memory_safety.classes.

Import Symbolic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import DoNotation.

Module Sym.

Section WithClasses.

Context (mt : machine_types).
Context {ops : machine_ops mt}.
Context `{syscall_regs mt}
        {msa : memory_syscall_addrs mt}.

Open Scope word_scope.

Local Notation word := (mword mt).
Local Notation "x .+1" := (addw x onew).

Inductive type :=
| TypeData
| TypePointer : name -> type.

Inductive mem_tag :=
| TagMemory : name -> type -> mem_tag
| TagFree.

Local Notation DATA := TypeData.
Local Notation PTR := TypePointer.
Notation "M( n , ty )" := (TagMemory n ty) (at level 4).
Local Notation FREE := TagFree.
Local Notation matom := (atom word mem_tag).
Local Notation datom := (atom word type).

Record block_info := mkBlockInfo {
  block_base : word;
  block_size : word;
  block_color : option name
}.

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

Definition type_eq t1 t2 :=
  match t1, t2 with
    | TypeData, TypeData => true
    | TypePointer b1, TypePointer b2 => b1 == b2
    | _, _ => false
  end.

Lemma type_eqP : Equality.axiom type_eq.
Proof.
  move => [|b1] [|b2] /=; try (constructor; congruence).
  have [->|/eqP NEQ] := altP (b1 =P b2); constructor; congruence.
Qed.

Definition type_eqMixin := EqMixin type_eqP.
Canonical type_eqType := Eval hnf in EqType type type_eqMixin.

Definition mem_tag_eq l1 l2 :=
  match l1, l2 with
    | TagMemory b1 t1, TagMemory b2 t2 => (b1 == b2) && (t1 == t2)
    | TagFree, TagFree => true
    | _, _ => false
  end.

Lemma mem_tag_eqP : Equality.axiom mem_tag_eq.
Proof.
  move => [b1 t1|] [b2 t2|] /=; try (constructor; congruence).
  by have [->|/eqP ?] := altP (b1 =P b2); have [->|/eqP ?] := altP (t1 =P t2);
  constructor; congruence.
Qed.

Definition mem_tag_eqMixin := EqMixin mem_tag_eqP.
Canonical mem_tag_eqType := Eval hnf in EqType mem_tag mem_tag_eqMixin.

Definition ms_tags := {|
  pc_tag_type := [eqType of type];
  reg_tag_type := [eqType of type];
  mem_tag_type := [eqType of mem_tag];
  entry_tag_type := [eqType of unit]
|}.

Definition rules_normal (op : opcode) (c : name)
           (ts : hseq (tag_type ms_tags) (inputs op)) : option (ovec ms_tags op) :=
  let ret  := fun rtpc (rt : type_of_result ms_tags (outputs op)) => Some (@OVec ms_tags op rtpc rt) in
  let retv := fun (rt : type_of_result ms_tags (outputs op)) => ret (PTR c) rt in
  match op, ts, ret, retv with
  | NOP, _, ret, retv => retv tt
  | CONST, _, ret, retv => retv DATA
  | MOV, [hseq ty; _], ret, retv => retv ty
  | BINOP bo, [hseq t1; t2; _], ret, retv =>
    match bo with
    | ADD =>
      match t1, t2 with
      | DATA, DATA => retv DATA
      | PTR b1, DATA => retv (PTR b1)
      | DATA, PTR b2 => retv (PTR b2)
      | _, _ => None
      end
    | SUB =>
      match t1, t2 with
      | DATA, DATA => retv DATA
      | PTR b1, DATA => retv (PTR b1)
      | PTR b1, PTR b2 =>
        if b1 == b2 then retv DATA
        else None
      | _, _ => None
      end
    | EQ =>
      match t1, t2 with
      | DATA, DATA => retv DATA
      | PTR b1, PTR b2 =>
        if b1 == b2 then retv DATA
        else None
      | _, _ => None
      end
    | _ =>
      match t1, t2 with
      | DATA, DATA => retv DATA
      | _, _ => None
      end
    end
  | LOAD, [hseq PTR b1; M(b2,ty); _], ret, retv =>
    if b1 == b2 then retv ty
    else None
  | STORE, [hseq PTR b1; ty; M(bd,_)], ret, retv =>
    if b1 == bd then retv M(bd,ty)
    else None
  | JUMP, [hseq PTR b'], ret, retv =>
    ret (PTR b') tt
  | BNZ, [hseq DATA], ret, retv =>
    retv tt
  | JAL, [hseq ty; _], ret, retv =>
    ret ty (PTR c)
  | _, _, _, _ => None
  end.

Definition rules (ivec : ivec ms_tags) : option (vovec ms_tags (op ivec)) :=
  match ivec return option (vovec ms_tags (op ivec)) with
  | IVec (OP op) tpc ti ts =>
    match tpc, ti with
    | PTR b, M(b', DATA) =>
      if b == b' then rules_normal b ts
      else None
    | _, _ => None
    end
  | IVec SERVICE DATA _ _ => Some tt
  | IVec SERVICE _ _ _ => None
  end.

Variable initial_color : name.

(* Hypothesis: alloc never returns initial_color. *)

Variable initial_pc : word.
Variable initial_mem  : {fmap mword mt -> matom}.
Variable initial_registers : {fmap reg mt -> datom}.
Hypothesis initial_ra : getm initial_registers ra = Some initial_pc@(PTR initial_color).

Definition initial_state := (initial_mem, initial_registers, initial_pc@(PTR initial_color)).

Global Instance sym_memory_safety : params := {
  ttypes := ms_tags;

  transfer := rules;

  internal_state := [eqType of (name * seq block_info)%type]
}.

Fixpoint write_block_rec mem base (v : matom) n : option (Symbolic.memory mt _) :=
  match n with
  | O => Some mem
  | S p => do! mem' <- write_block_rec mem base v p;
           updm mem' (base + as_word p) v
  end.

Definition write_block init (base : word) (v : matom) (sz : word) : option (Symbolic.memory mt _) :=
  if base + sz < 2 ^ (word_size mt) then
     write_block_rec init base v (val sz)
  else None.

Definition update_block_info info x (color : name) sz :=
  let i := index x info in
  let color1 := mkBlockInfo (block_base x) sz (Some color) in
  let res := set_nth color1 info i color1 in
  if sz == block_size x then res
    else
    let block2 := mkBlockInfo (block_base x + sz) (block_size x - sz) None in
    block2 :: res.

Definition malloc_fun st : option (state mt) :=
  let: (color,info) := internal st in
  do! sz <- regs st syscall_arg1;
  match sz with
    | sz@DATA =>
      if 0 < (sz : word) then
          if ohead [seq x <- info | ((sz <= block_size x) && (block_color x == None))%ord] is Some x then
          do! mem' <- write_block (mem st) (block_base x) 0@M(color,DATA) sz;
          do! regs' <- updm (regs st) syscall_ret ((block_base x)@(PTR color));
          let color' := Name (val color).+1 in
          do! raddr <- regs st ra;
          if raddr is _@(PTR _) then
            Some (State mem' regs' raddr (color', update_block_info info x color sz))
          else None
          else None
      else None
    | _ => None
  end.

Definition def_info : block_info :=
  mkBlockInfo 0 0 None.

(* TODO: avoid memory fragmentation *)
Definition free_fun (st : state mt) : option (state mt) :=
  let: (next_color,info) := internal st in
  do! ptr <- regs st syscall_arg1;
    (* Removing the return clause makes Coq loop... *)
  match ptr return option (state mt) with
  | ptr@(PTR color) =>
    do! x <- ohead [seq x <- info | block_color x == Some color];
    let i := index x info in
    if (block_base x <= ptr < block_base x + block_size x)%ord then
      do! mem' <- write_block (mem st) (block_base x) 0@FREE (block_size x);
      let info' := set_nth def_info info i (mkBlockInfo (block_base x) (block_size x) None)
      in
      do! raddr <- regs st ra;
      if raddr is _@(PTR _) then
        Some (State mem' (regs st) raddr (next_color,info'))
      else None
    else None
  | _ => None
  end.

(* This factors out the common part of sizeof, basep, and offp *)
Definition ptr_fun (st : state mt)
    (f : block_info -> name -> datom) : option (state mt) :=
  let: (next_color,inf) := internal st in
  do! ptr <- regs st syscall_arg1;
  match ptr return option (state mt) with
  | ptr@(PTR color) =>
    do! x <- ohead [seq x <- inf | block_color x == Some color];
    do! regs' <- updm (regs st) syscall_ret (f x color);
    do! raddr <- regs st ra;
    if raddr is _@(PTR _) then
      Some (State (mem st) regs' raddr (next_color,inf))
    else None
  | _ => None
  end.

(* Not yet used *)
Definition sizeof_fun (st : state mt) : option (state mt) :=
  ptr_fun st (fun x _ => (block_size x)@DATA).

Definition basep_fun (st : state mt) : option (state mt) :=
  ptr_fun st (fun x color => (block_base x)@(PTR color)).

Definition eqp_fun (st : state mt) : option (state mt) :=
  let: (next_color,inf) := internal st in
  do! ptr1 <- regs st syscall_arg1;
  do! ptr2 <- regs st syscall_arg2;
  let b := as_word (ptr1 == ptr2) in
  do! regs' <- updm (regs st) syscall_ret b@DATA;
  do! raddr <- regs st ra;
  if raddr is _@(PTR _) then
    Some (State (mem st) regs' raddr (next_color,inf))
  else None.

Definition memsafe_syscalls : syscall_table mt :=
  [fmap (addr Malloc, Syscall tt malloc_fun);
        (addr Free,   Syscall tt free_fun);
      (*(addr Size,   Syscall tt sizeof_fun); *)
        (addr Base,   Syscall tt basep_fun);
        (addr Eq,     Syscall tt eqp_fun)].

Definition step := step memsafe_syscalls.

End WithClasses.

Canonical block_info_eqType.

Notation memory mt := (Symbolic.memory mt (@sym_memory_safety mt)).
Notation registers mt := (Symbolic.registers mt (@sym_memory_safety mt)).

Module Notations.

Notation DATA := TypeData.
Notation PTR := TypePointer.
Notation "M( n , ty )" := (TagMemory n ty) (at level 4).
Notation FREE := TagFree.

End Notations.

End Sym.

Canonical Sym.type_eqType.
Canonical Sym.block_info_eqType.
