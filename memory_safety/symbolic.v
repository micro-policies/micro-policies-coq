Require Import List Arith ZArith.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
Require Import lib.Integers lib.utils lib.ordered lib.partial_maps common.common.
Require Import lib.hlist.
Require Import symbolic.symbolic memory_safety.classes.

Import Symbolic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import DoNotation.
Import ListNotations.

Module Sym.

Open Scope bool_scope.
Open Scope Z_scope.

Section WithClasses.

Context (t : machine_types).
Context {ops : machine_ops t}.

Import PartMaps.

Context `{syscall_regs t}
        {msa : @memory_syscall_addrs t}.

Open Scope word_scope.

Local Notation word := (word t).
Local Notation "x .+1" := (Word.add x Word.one).

Class color_class := {
  color : eqType;
  max_color : color;
  inc_color : color -> color;
  ord_color :> Ordered color;
  ltb_inc : forall col, (col <? max_color -> col <? inc_color col)%ordered
}.

Context {cl : color_class}.

Inductive type :=
| TypeData
| TypePointer : color -> type.

Inductive tag :=
| TagValue : type -> tag
| TagMemory : color -> type -> tag
| TagFree.

Local Notation DATA := TypeData.
Local Notation PTR := TypePointer.
Local Notation "V( ty )" := (TagValue ty) (at level 4).
Notation "M( n , ty )" := (TagMemory n ty) (at level 4).
Local Notation FREE := TagFree.
Local Notation atom := (atom word tag).

Record block_info := mkBlockInfo {
  block_base : word;
  block_size : word;
  block_color : option color
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

Definition tag_eq l1 l2 :=
  match l1, l2 with
    | TagValue t1, TagValue t2 => t1 == t2
    | TagMemory b1 t1, TagMemory b2 t2 => (b1 == b2) && (t1 == t2)
    | TagFree, TagFree => true
    | _, _ => false
  end.

Lemma tag_eqP : Equality.axiom tag_eq.
Proof.
  move => [t1|b1 t1|] [t2|b2 t2|] /=; try (constructor; congruence).
  - by have [->|/eqP NEQ] := altP (t1 =P t2); constructor; congruence.
  - by have [->|/eqP ?] := altP (b1 =P b2); have [->|/eqP ?] := altP (t1 =P t2);
    constructor; congruence.
Qed.

Definition tag_eqMixin := EqMixin tag_eqP.
Canonical tag_eqType := Eval hnf in EqType tag tag_eqMixin.

Section WithHListNotations.
Import HListNotations.

Definition ms_tags : tag_kind -> eqType := fun _ => [eqType of tag].

Definition rules_normal (op : opcode) (c : color)
           (ts : hlist ms_tags (inputs op)) : option (OVec ms_tags op) :=
  let ret  := fun rtpc (rt : type_of_result ms_tags (outputs op)) => Some (@mkOVec ms_tags op rtpc rt) in
  let retv := fun (rt : type_of_result ms_tags (outputs op)) => ret V(PTR c) rt in
  match op, ts, ret, retv with
  | NOP, _, ret, retv => retv tt
  | CONST, _, ret, retv => retv V(DATA)
  | MOV, [V(ty); _], ret, retv => retv V(ty)
  | BINOP bo, [t1; t2; _], ret, retv =>
    match bo with
    | ADD =>
      match t1, t2 with
      | V(DATA), V(DATA) => retv V(DATA)
      | V(PTR b1), V(DATA) => retv V(PTR b1)
      | V(DATA), V(PTR b2) => retv V(PTR b2)
      | _, _ => None
      end
    | SUB =>
      match t1, t2 with
      | V(DATA), V(DATA) => retv V(DATA)
      | V(PTR b1), V(DATA) => retv V(PTR b1)
      | V(PTR b1), V(PTR b2) =>
        if b1 == b2 then retv V(DATA)
        else None
      | _, _ => None
      end
    | EQ =>
      match t1, t2 with
      | V(DATA), V(DATA) => retv V(DATA)
      | V(PTR b1), V(PTR b2) =>
        if b1 == b2 then retv V(DATA)
        else None
      | _, _ => None
      end
    | _ =>
      match t1, t2 with
      | V(DATA), V(DATA) => retv V(DATA)
      | _, _ => None
      end
    end
  | LOAD, [V(PTR b1); M(b2,ty); _], ret, retv =>
    if b1 == b2 then retv V(ty)
    else None
  | STORE, [V(PTR b1); V(ty); M(bd,_)], ret, retv =>
    if b1 == bd then retv M(bd,ty)
    else None
  | JUMP, [V(PTR b')], ret, retv =>
    ret V(PTR b') tt
  | BNZ, [V(DATA)], ret, retv =>
    retv tt
  | JAL, [V(ty); _], ret, retv =>
    ret V(ty) V(PTR c)
  | _, _, _, _ => None
  end.

Definition rules (ivec : IVec ms_tags) : option (OVec ms_tags (op ivec)) :=
  match ivec return option (OVec ms_tags (op ivec)) with
  | mkIVec op tpc ti ts =>
    match tpc, ti with
    | V(DATA), _ =>
      match op return option (OVec ms_tags op) with
      | SERVICE => Some (@mkOVec ms_tags SERVICE V(DATA) tt)
      | _ => None
      end
    | V(PTR b), M(b', DATA) =>
      if b == b' then
        rules_normal b ts
      else None
    | _, _ => None
    end
  end.

End WithHListNotations.

Variable initial_color : color.

(* Hypothesis: alloc never returns initial_color. *)

Variable initial_pc : word.
Variable initial_mem  : word_map t atom.
Variable initial_registers : reg_map t atom.
Hypothesis initial_ra : get initial_registers ra = Some initial_pc@V(PTR initial_color).

Definition initial_state := (initial_mem, initial_registers, initial_pc@V(PTR initial_color)).

Global Instance sym_memory_safety : params := {
  ttypes := ms_tags;

  transfer := rules;

  internal_state := [eqType of (color * list block_info)%type]
}.

Fixpoint write_block_rec mem base (v : atom) n : option (Symbolic.memory t _) :=
  match n with
  | O => Some mem
  | S p => do! mem' <- write_block_rec mem base v p;
           upd mem' (base + Word.reprn p) v
  end.

Definition write_block init base (v : atom) (sz : word) : option (Symbolic.memory t _) :=
  if Word.unsigned base + Word.unsigned sz <=? Word.max_unsigned (word_size_minus_one t) then
     write_block_rec init base v (Z.to_nat (Word.unsigned sz))
  else None.

Definition update_block_info info x (color : color) sz :=
  let i := index x info in
  let color1 := mkBlockInfo (block_base x) sz (Some color) in
  let res := set_nth color1 info i color1 in
  if sz == block_size x then res
    else
    let block2 := mkBlockInfo (block_base x + sz) (block_size x - sz) None in
    block2 :: res.

Definition malloc_fun st : option (state t) :=
  let: (color,info) := internal st in
  if (color <? max_color)%ordered then
  do! sz <- get (regs st) syscall_arg1;
  match sz with
    | sz@V(DATA) =>
      if (0 <? sz)%ordered then
          if ohead [seq x <- info | ((sz <=? block_size x) && (block_color x == None))%ordered] is Some x then
          do! mem' <- write_block (mem st) (block_base x) 0@M(color,DATA) sz;
          do! regs' <- upd (regs st) syscall_ret ((block_base x)@V(PTR color));
          let color' := inc_color color in
          do! raddr <- get (regs st) ra;
          if raddr is _@V(PTR _) then
            Some (State mem' regs' raddr (color', update_block_info info x color sz))
          else None
          else None
      else None
    | _ => None
  end
  else None.

Definition def_info : block_info :=
  mkBlockInfo 0 0 None.

(* TODO: avoid memory fragmentation *)
Definition free_fun (st : state t) : option (state t) :=
  let: (next_color,info) := internal st in
  do! ptr <- get (regs st) syscall_arg1;
    (* Removing the return clause makes Coq loop... *)
  match ptr return option (state t) with
  | ptr@V(PTR color) =>
    do! x <- ohead [seq x <- info | block_color x == Some color];
    let i := index x info in
    if (block_base x <=? ptr <? block_base x + block_size x) then
      do! mem' <- write_block (mem st) (block_base x) 0@FREE (block_size x);
      let info' := set_nth def_info info i (mkBlockInfo (block_base x) (block_size x) None)
      in
      do! raddr <- get (regs st) ra;
      if raddr is _@V(PTR _) then
        Some (State mem' (regs st) raddr (next_color,info'))
      else None
    else None
  | _ => None
  end.

(* This factors out the common part of sizeof, basep, and offp *)
Definition ptr_fun (st : state t)
    (f : block_info -> color -> atom) : option (state t) :=
  let: (next_color,inf) := internal st in
  do! ptr <- get (regs st) syscall_arg1;
  match ptr return option (state t) with
  | ptr@V(PTR color) =>
    do! x <- ohead [seq x <- inf | block_color x == Some color];
    do! regs' <- upd (regs st) syscall_ret (f x color);
    do! raddr <- get (regs st) ra;
    if raddr is _@V(PTR _) then
      Some (State (mem st) regs' raddr (next_color,inf))
    else None
  | _ => None
  end.

(* Not yet used *)
Definition sizeof_fun (st : state t) : option (state t) :=
  ptr_fun st (fun x _ => (block_size x)@V(DATA)).

Definition basep_fun (st : state t) : option (state t) :=
  ptr_fun st (fun x color => (block_base x)@V(PTR color)).

Definition eqp_fun (st : state t) : option (state t) :=
  let: (next_color,inf) := internal st in
  do! ptr1 <- get (regs st) syscall_arg1;
  do! ptr2 <- get (regs st) syscall_arg2;
  match ptr1, ptr2 return option (state t) with
  | ptr1@V(PTR color1), ptr2@V(PTR color2) =>
    let b := if (color1 == color2) && (ptr1 == ptr2) then Word.one
             else Word.zero in
    do! regs' <- upd (regs st) syscall_ret b@V(DATA);
    do! raddr <- get (regs st) ra;
    if raddr is _@V(PTR _) then
      Some (State (mem st) regs' raddr (next_color,inf))
    else None
  | _, _ => None
  end.

Definition memsafe_syscalls : list (syscall t) :=
  [Syscall malloc_addr V(DATA) malloc_fun;
   Syscall free_addr V(DATA) free_fun;
(* Syscall size_addr V(DATA) sizeof_fun; *)
   Syscall base_addr V(DATA) basep_fun;
   Syscall eq_addr V(DATA) eqp_fun].

Definition step := step memsafe_syscalls.

End WithClasses.

Canonical block_info_eqType.

Notation memory t := (Symbolic.memory t (@sym_memory_safety t _)).
Notation registers t := (Symbolic.registers t (@sym_memory_safety t _)).

Module Notations.

Notation DATA := TypeData.
Notation PTR := TypePointer.
Notation "V( ty )" := (TagValue ty) (at level 4).
Notation "M( n , ty )" := (TagMemory n ty) (at level 4).
Notation FREE := TagFree.

End Notations.

Arguments def_info t {_}.

End Sym.
