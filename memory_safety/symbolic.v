Require Import List Arith ZArith.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
Require Import lib.utils lib.ordered lib.partial_maps common.common.
Require Import symbolic.symbolic memory_safety.classes.

Import Symbolic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* This is an instantiation of the machine in quasiabstract.v using
the symbolic machine. *)

Import DoNotation.
Import ListNotations.

Module Sym.

Open Scope bool_scope.
Open Scope Z_scope.

Section WithClasses.

Context (t : machine_types).
Context {ops : machine_ops t}.

(* CH: This should be called color *)
Definition block := word t.

Inductive type :=
| TypeData
| TypePointer : block -> type.

Inductive tag :=
| TagValue : type -> tag
| TagMemory : block -> type -> tag
| TagFree.

Local Notation DATA := TypeData.
Local Notation PTR := TypePointer.
Local Notation "V( ty )" := (TagValue ty) (at level 4).
Notation "M( n , ty )" := (TagMemory n ty) (at level 4).
Local Notation FREE := TagFree.
Local Notation atom := (atom (word t) tag).

Import PartMaps.

Context `{syscall_regs t}
        {msa : @memory_syscall_addrs t}.

Open Scope word_scope.

Local Notation word := (word t).
Local Notation "x .+1" := (add_word x (Z_to_word 1)).

Record block_info := mkBlockInfo {
  block_base : word;
  block_size : word;
  block_color : option word
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

Section WithVectorNotations.
Import Vector.VectorNotations.

(* Convient wrapper for making writing rules easier. Move somewhere else *)
Require Import Coq.Numbers.NaryFunctions.

Fixpoint nfun_vec_ap {A B n} : forall (f : nfun A n B) (v : Vector.t A n), B :=
  match n with
  | O => fun f _ => f
  | S n' => fun f v => nfun_vec_ap (f (Vector.hd v)) (Vector.tl v)
  end.

Fixpoint const_nfun {A B n} (b : B) : nfun A n B :=
  match n with
  | O => b
  | S n' => fun _ => const_nfun b
  end.

Definition mvec_dest A B op :=
  match nfields op with
  | Some nf => nfun A nf.1 B
  | None => Empty_set -> B
  end.

Definition mvec_const_dest {A B} op (b : B) : mvec_dest A B op :=
  match nfields op as nf
                  return match nf with
                         | Some nf => nfun A nf.1 B
                         | None => Empty_set -> B
                         end
  with
  | Some nf => const_nfun b
  | None => fun contra => match contra with end
  end.

Definition mvec_match {A B} op : forall (fs : mvec_operands A (nfields op))
                                        (f : mvec_dest A B op), B :=
  match nfields op as nf
                   return match nf with
                          | Some nf => Vector.t A nf.1
                          | None => Empty_set
                          end ->
                          match nf with
                          | Some nf => nfun A nf.1 B
                          | None => Empty_set -> B
                          end -> B
  with
  | Some nf => fun fs f => nfun_vec_ap f fs
  | None => fun fs f => match fs with end
  end.

Definition rules (mvec : MVec tag) : option (RVec tag) :=
  match mvec with
  | mkMVec SERVICE V(DATA) ti ts => Some (mkRVec V(DATA) V(DATA))
  | mkMVec op V(PTR b) ti ts =>
    if ti is M(b', DATA) then
    if b == b' then
      let ret tpc tr := Some (mkRVec tpc tr) in
      let retv tr := ret V(PTR b) tr in
      mvec_match ts
                 match op return mvec_dest _ (option (RVec tag)) op with
                 | NOP => retv V(DATA)
                 | CONST => fun _ => retv V(DATA)
                 | MOV => fun t1 t2 =>
                   match t1 with
                   | V(ty) => retv V(ty)
                   | _ => None
                   end
                 | BINOP bo => fun t1 t2 _ =>
                   match bo with
                   | ADD =>
                     match t1, t2 with
                     | V(DATA), V(DATA) => Some (mkRVec V(PTR b) V(DATA))
                     | V(PTR b1), V(DATA) => Some (mkRVec V(PTR b) V(PTR b1))
                     | V(DATA), V(PTR b2) => Some (mkRVec V(PTR b) V(PTR b2))
                     | _, _ => None
                     end
                   | SUB =>
                     match t1, t2 with
                     | V(DATA), V(DATA) => Some (mkRVec V(PTR b) V(DATA))
                     | V(PTR b1), V(DATA) => Some (mkRVec V(PTR b) V(PTR b1))
                     | V(PTR b1), V(PTR b2) =>
                       if b1 == b2 then Some (mkRVec V(PTR b) V(DATA))
                       else None
                     | _, _ => None
                     end
                   | EQ =>
                     match t1, t2 with
                     | V(DATA), V(DATA) => Some (mkRVec V(PTR b) V(DATA))
                     | V(PTR b1), V(PTR b2) =>
                       if b1 == b2 then Some (mkRVec V(PTR b) V(DATA))
                       else None
                     | _, _ => None
                     end
                   | _ =>
                     match t1, t2 with
                     | V(DATA), V(DATA) => Some (mkRVec V(PTR b) V(DATA))
                     | _, _ => None
                     end
                   end
                 | LOAD => fun t1 t2 _ =>
                   match t1, t2 with
                   | V(PTR b1), M(b2,ty) =>
                     if b1 == b2 then Some (mkRVec V(PTR b) V(ty))
                     else None
                   | _, _ => None
                   end
                 | STORE => fun t1 t2 t3 =>
                   match t1, t2, t3 with
                   | V(PTR b1), V(ty), M(bd,_) =>
                     if b1 == bd then Some (mkRVec V(PTR b) M(bd,ty))
                     else None
                   | _, _, _ => None
                   end
                 | JUMP => fun t =>
                   match t with
                   | V(PTR b') =>
                     ret V(PTR b') V(DATA)
                   | _ => None
                   end
                 | BNZ => fun t =>
                   match t with
                   | V(DATA) => retv V(DATA)
                   | _ => None
                   end
                 | JAL => fun t _ =>
                   match t with
                   | V(ty) => ret V(ty) V(PTR b)
                   | _ => None
                   end
                 | JUMPEPC as op | ADDRULE as op | GETTAG as op
                 | PUTTAG as op | HALT as op | SERVICE as op =>
                     @mvec_const_dest tag (option (RVec tag)) op None
                 end
    else None else None
  | _ => None
  end.

End WithVectorNotations.

Variable initial_block : block.

(* Hypothesis: alloc never returns initial_block. *)

Variable initial_pc : word.
Variable initial_mem  : word_map t atom.
Variable initial_registers : reg_map t atom.
Hypothesis initial_ra : get initial_registers ra = Some initial_pc@V(PTR initial_block).

Definition initial_state := (initial_mem, initial_registers, initial_pc@V(PTR initial_block)).

Definition type_eq t1 t2 :=
  match t1, t2 with
    | TypeData, TypeData => true
    | TypePointer b1, TypePointer b2 => b1 == b2
    | _, _ => false
  end.

Lemma type_eqP : Equality.axiom type_eq.
Admitted.

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
Admitted.

Definition tag_eqMixin := EqMixin tag_eqP.
Canonical tag_eqType := Eval hnf in EqType tag tag_eqMixin.

Global Instance sym_memory_safety : symbolic_params := {
  tag := tag_eqType;

  handler := rules;

  internal_state := (word * list block_info)%type
}.


Fixpoint write_block init base (v : atom) n : Symbolic.memory t _ :=
  match n with
  | O => init
  | S p => if upd init (base + Z_to_word (Z.of_nat n)) 0@FREE is Some mem then
           write_block mem base v p else init
  end.

Definition update_block_info info x color sz :=
  let i := index x info in
  let block1 := mkBlockInfo (block_base x) sz (Some color) in
  let pre := take i info in
  let post := drop (i+1) info in
  if sz == block_size x then
    pre ++ [block1] ++ post
  else
    let block2 := mkBlockInfo (block_base x + sz) (block_size x - sz) None in
    pre ++ [block1;block2] ++ post.

Definition malloc_fun st : option (state t) :=
  let: (color,info) := internal st in
  do! sz <- get (regs st) syscall_arg1;
  match sz with
    | sz@V(DATA) =>
      match compare 0 sz with
        | Lt =>
          if ohead [seq x <- info | ((sz <=? block_size x) && (block_color x == None))%ordered] is Some x then
          let mem' := write_block (mem st) (block_base x) 0@M(color,DATA) (Z.to_nat (word_to_Z sz)) in
          do! regs' <- upd (regs st) syscall_ret ((block_base x)@V(PTR color));
          let color' := color + 1 in
          do! raddr <- get (regs st) ra;
          if raddr is _@V(PTR _) then
            Some (State mem' regs' raddr (color', update_block_info info x color sz))
          else None
          else None
        | _ => None
      end
    | _ => None
  end.

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
      let mem' := write_block (mem st) (block_base x) 0@FREE (Z.to_nat (word_to_Z (block_size x))) in
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
    (f : block_info -> word -> atom) : option (state t) :=
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
    let b := if (color1 == color2) && (ptr1 == ptr2) then Z_to_word 1%Z
             else Z_to_word 0%Z in
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
   Syscall size_addr V(DATA) sizeof_fun;
   Syscall base_addr V(DATA) basep_fun;
   Syscall eq_addr V(DATA) eqp_fun].

Definition step := step memsafe_syscalls.

End WithClasses.

Canonical block_info_eqType.

Notation memory t := (Symbolic.memory t (@sym_memory_safety t)).
Notation registers t := (Symbolic.registers t (@sym_memory_safety t)).

Module Notations.

Notation DATA := (TypeData _).
Notation PTR := TypePointer.
Notation "V( ty )" := (TagValue ty) (at level 4).
Notation "M( n , ty )" := (TagMemory n ty) (at level 4).
Notation FREE := (TagFree _).

End Notations.

End Sym.
