Require Import List. Import ListNotations.
Require Import Coq.Classes.SetoidDec.

Require Import utils common symbolic. Import rules.

Set Implicit Arguments.

Module SymbolicSealing.

Section WithClasses.

Context {t : machine_types}.
Context {ops : machine_ops t}.
Context {opss : machine_ops_spec ops}.

Class symbolic_sealing_types := {
  memory    : Type;
  registers : Type;
  key       : Type
}.

Context {sst : symbolic_sealing_types}.

Inductive stag :=
| WORD   :        stag
| KEY    :        stag
| SEALED : key -> stag.

Class symbolic_sealing_params := {
  get_mem : memory -> word t -> option (atom (word t) stag);
  upd_mem : memory -> word t -> atom (word t) stag -> option memory;

  get_reg : registers -> reg t -> option (atom (word t) stag);
  upd_reg : registers -> reg t -> atom (word t) stag -> option registers;

  word_to_key : word t -> option key;
  eq_key :> EqDec (eq_setoid key);

  mkkey_addr  : word t;
  seal_addr   : word t;
  unseal_addr : word t;

  syscall_ret  : reg t;
  syscall_arg1 : reg t;
  syscall_arg2 : reg t
}.

Class params_spec (ap : symbolic_sealing_params) := {
  mem_axioms : PartMaps.axioms get_mem upd_mem;
  reg_axioms : PartMaps.axioms get_reg upd_reg
}.

Context {ssp : symbolic_sealing_params}.

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
      | SEALED k1, SEALED k2 =>
        match k1 == k2 with
        | left H1 => _
        | _ => _
        end
      | WORD, WORD => left eq_refl
      | KEY, KEY => left eq_refl
      | _, _ => _
      end
    ); simpl in *; subst; auto; right; congruence. 
Defined.

Program Instance sym_sealing : (Symbolic.symbolic_params t) := {
  memory := memory;
  registers := registers;
  tag := stag;

  get_mem := get_mem;
  upd_mem := upd_mem;

  get_reg := get_reg;
  upd_reg := upd_reg;

  handler := sealing_handler;

  internal_state := word t  (* next key to generate *)
}.

Import DoNotation.

Definition mkkey (s : Symbolic.state t) : option (Symbolic.state t) :=
  let 'Symbolic.State mem reg pc key := s in
  if key == max_word then None
  else
    let key' := add_word key (Z_to_word 1) in
    do reg' <- upd_reg reg syscall_ret (key@KEY);
    Some (Symbolic.State mem reg' pc key').

Definition seal (s : Symbolic.state t) : option (Symbolic.state t) :=
  let 'Symbolic.State mem reg pc next_key := s in
  match get_reg reg syscall_arg1, get_reg reg syscall_arg2 with
  | Some (payload@WORD), Some (wkey@KEY) =>
    do key  <- word_to_key wkey;
    do reg' <- upd_reg reg syscall_ret (payload@(SEALED key));
    Some (Symbolic.State mem reg' pc next_key)
  | _, _ => None
  end.

Definition unseal (s : Symbolic.state t) : option (Symbolic.state t) :=
  let 'Symbolic.State mem reg pc next_key := s in
  match get_reg reg syscall_arg1, get_reg reg syscall_arg2 with
  | Some (payload@(SEALED key)), Some (wkey@KEY) =>
    do key  <- word_to_key wkey;
    do reg' <- upd_reg reg syscall_ret (payload@WORD);
    Some (Symbolic.State mem reg' pc next_key)
  | _, _ => None
  end.

Definition sealing_syscalls : list (Symbolic.syscall t) :=
  [Symbolic.Syscall mkkey_addr mkkey;
   Symbolic.Syscall seal_addr seal;
   Symbolic.Syscall unseal_addr unseal].

Definition sealing_step := Symbolic.step sealing_syscalls.

End WithClasses.

End SymbolicSealing.
