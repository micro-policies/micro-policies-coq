Require Import List. Import ListNotations.
Require Import Coq.Classes.SetoidDec.

Require Import utils common symbolic. Import rules.
Require Import classes.

Set Implicit Arguments.

Module SymSeal.

Section WithClasses.

Import PartMaps.

Context {t : machine_types}
        {ops : machine_ops t}
        {opss : machine_ops_spec ops}
        {sk : sealing_key}
        {sko : sealing_key_ops}
        {scr : @syscall_regs t}
        {ssa : @sealing_syscall_addrs t}.

Inductive stag :=
| DATA   :        stag
| KEY    : key -> stag
| SEALED : key -> stag.

Context {memory : Type}
        {sm : partial_map memory (word t) (atom (word t) stag)}
        {registers : Type}
        {sr : partial_map registers (reg t) (atom (word t) stag)}.

Definition none := DATA.

Section WithVectors.
Import Coq.Vectors.Vector.VectorNotations.

Definition sealing_handler (mv : MVec stag) : option (RVec stag) :=
  match mv with
  | mkMVec NOP       _ _ []           => Some (mkRVec none none)
  | mkMVec CONST     _ _ []           => Some (mkRVec none DATA)
  | mkMVec MOV       _ _ [tsrc]       => Some (mkRVec none tsrc)
  | mkMVec (BINOP _) _ _ [DATA; DATA] => Some (mkRVec none DATA)
  | mkMVec LOAD      _ _ [DATA; tmem] => Some (mkRVec none tmem)
  | mkMVec STORE     _ _ [DATA; tsrc] => Some (mkRVec none tsrc)
  | mkMVec JUMP      _ _ [DATA]       => Some (mkRVec none none)
  | mkMVec BNZ       _ _ [DATA]       => Some (mkRVec none none)
  | mkMVec JAL       _ _ [DATA]       => Some (mkRVec none DATA)
  | mkMVec _         _ _ _            => None
  end.

End WithVectors.

Global Instance equ : EqDec (eq_setoid stag).
  intros t1 t2.
  refine (
      match t1, t2 with
      | DATA, DATA => left eq_refl
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
  tag := stag;

  handler := sealing_handler;

  internal_state := key;  (* next key to generate *)

  memory := memory;
  sm := sm;

  registers := registers;
  sr := sr
}.

Import DoNotation. 

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
  | Some (payload@DATA), Some (_@(KEY key)) =>
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
      do reg' <- upd reg syscall_ret (payload@DATA);
      Some (Symbolic.State mem reg' pc next_key)
  | _, _ => None
  end.

Definition sealing_syscalls : list (Symbolic.syscall t) :=
  [Symbolic.Syscall mkkey_addr mkkey;
   Symbolic.Syscall seal_addr seal;
   Symbolic.Syscall unseal_addr unseal].

Definition step := Symbolic.step sealing_syscalls.

End WithClasses.

(* BCP: Aren't there also some proof obligations that we need to satisfy? *)
(* CH: You mean for the concrete-symbolic refinement?
   I expect those to appear when talking about that refinement,
   which we don't yet *)

(* BCP: Yes, that's what I meant.  I know we're not there yet, but I
   am wondering where we want to write them.  Still confused about the
   modularization strategy for the whole codebase... *)
(* CH: We will probably make a refinementCS.v file at some point,
   and I expect that to use any of Arthur's results we'll need
   to give this kind of details *)

End SymSeal.
