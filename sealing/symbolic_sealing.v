Require Import List. Import ListNotations.
Require Import Coq.Classes.SetoidDec.

Require Import utils common symbolic. Import rules.
Require Import classes.

Set Implicit Arguments.

Module SymbolicSealing.

Section WithClasses.

Context {t : machine_types}.
Context {ops : machine_ops t}.
Context {opss : machine_ops_spec ops}.
Context {sk : sealing_key}.
Context {sko : sealing_key_ops}.
Context {scr : @syscall_regs t}.
Context {ssa : @sealing_syscall_addrs t}.

Inductive stag :=
| WORD   :        stag
| KEY    : key -> stag
| SEALED : key -> stag.

Context {memory : Type}.
Context {sm : @partial_map memory (word t) (atom (word t) stag)}.

Context {registers : Type}.
Context {sr : @partial_map registers (reg t) (atom (word t) stag)}.

Definition none := WORD.

Section WithVectors.
Import Coq.Vectors.Vector.VectorNotations.

Definition sealing_handler (mv : MVec stag) : option (RVec stag) :=
  match mv with
  | mkMVec NOP       _ _ []           => Some (mkRVec none none)
  | mkMVec CONST     _ _ []           => Some (mkRVec none WORD)
  | mkMVec MOV       _ _ [tsrc]       => Some (mkRVec none tsrc)
  | mkMVec (BINOP _) _ _ [WORD; WORD] => Some (mkRVec none WORD)
  | mkMVec LOAD      _ _ [WORD; tmem] => Some (mkRVec none tmem)
  | mkMVec STORE     _ _ [WORD; tsrc] => Some (mkRVec none tsrc)
  | mkMVec JUMP      _ _ [WORD]       => Some (mkRVec none none)
  | mkMVec BNZ       _ _ [WORD]       => Some (mkRVec none none)
  | mkMVec JAL       _ _ [WORD]       => Some (mkRVec none WORD)
  | mkMVec _         _ _ _            => None
  end.

End WithVectors.

Global Instance equ : EqDec (eq_setoid stag).
  intros t1 t2.
  refine (
      match t1, t2 with
      | WORD, WORD => left eq_refl
      | KEY k1, KEY k2
      |  SEALED k1, SEALED k2 =>
        match k1 == k2 with
        | left H1 => _
        | _ => _
        end
      | _, _ => _
      end
    ); simpl in *; subst; auto; right; congruence. 
Defined.

Program Instance sym_sealing : (Symbolic.symbolic_params t) := {
  memory := memory;
  registers := registers;
  tag := stag;

  get_mem := get;
  upd_mem := upd;

  get_reg := get;
  upd_reg := upd;

  handler := sealing_handler;

  internal_state := key  (* next key to generate *)
}.

Import DoNotation. 

Set Printing All.

Definition mkkey (s : Symbolic.state t) : option (Symbolic.state t) :=
  let 'Symbolic.State mem reg pc key := s in
  if key == max_key then None
  else
    let key' := inc_key key in
    do reg' <- upd reg syscall_ret (max_word@(KEY key));
    Some (Symbolic.State mem reg' pc key').

Definition seal (s : Symbolic.state t) : option (Symbolic.state t) :=
  let 'Symbolic.State mem reg pc next_key := s in
  match get reg syscall_arg1, get reg syscall_arg2 with
  | Some (payload@WORD), Some (_@(KEY key)) =>
    do reg' <- upd reg syscall_ret (payload@(SEALED key));
    Some (Symbolic.State mem reg' pc next_key)
  | _, _ => None
  end.

Definition unseal (s : Symbolic.state t) : option (Symbolic.state t) :=
  let 'Symbolic.State mem reg pc next_key := s in
  match get reg syscall_arg1, get reg syscall_arg2 with
  | Some (payload@(SEALED key)), Some (_@(KEY key')) =>
    if key == key' then None
    else
      do reg' <- upd reg syscall_ret (payload@WORD);
      Some (Symbolic.State mem reg' pc next_key)
  | _, _ => None
  end.

Definition sealing_syscalls : list (Symbolic.syscall t) :=
  [Symbolic.Syscall mkkey_addr mkkey;
   Symbolic.Syscall seal_addr seal;
   Symbolic.Syscall unseal_addr unseal].

Definition sealing_step := Symbolic.step sealing_syscalls.

End WithClasses.

(* BCP: Aren't there also some proof obligations that we need to satisfy? *)
(* CH: You mean for the concrete-symbolic refinement?
   I expect those to appear when talking about that refinement,
   which we don't yet *)

End SymbolicSealing.
