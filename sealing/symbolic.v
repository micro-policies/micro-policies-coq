Require Import List. Import ListNotations.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Require Import lib.utils lib.ordered lib.partial_maps common.common.
Require Import symbolic.symbolic symbolic.rules.
Require Import sealing.classes.

Import Symbolic.

Set Implicit Arguments.

Module Sym.

Section WithClasses.

Import PartMaps.

Context {t : machine_types}
        {ops : machine_ops t}
        {opss : machine_ops_spec ops}
        {scr : @syscall_regs t}
        {ssa : @sealing_syscall_addrs t}.

Class sealing_key := {
  key : eqType;
  max_key : key;
  inc_key : key -> key;
  ord_key :> Ordered key;
  ltb_inc : forall sk, sk <? max_key -> sk <? inc_key sk
}.

Context {sk : sealing_key}.

Inductive stag :=
| DATA   :        stag
| KEY    : key -> stag
| SEALED : key -> stag.

Class params := {
  memory : Type;
  sm :> partial_map memory (word t) (atom (word t) stag);
  registers : Type;
  sr :> partial_map registers (reg t) (atom (word t) stag)
}.

Class params_spec (sp : params) := {
  mem_axioms :> PartMaps.axioms (@sm sp);
  reg_axioms :> PartMaps.axioms (@sr sp)
}.

Context {sp : params}.

(* One should not depend on the precise value of this tag! *)
Definition none := KEY max_key.

Section WithVectors.
Import Coq.Vectors.Vector.VectorNotations.

Definition sealing_handler (mv : MVec stag) : option (RVec stag) :=
  match mv with
  | mkMVec NOP       _ DATA []              => Some (mkRVec none none)
  | mkMVec CONST     _ DATA [_]             => Some (mkRVec none DATA)
  | mkMVec MOV       _ DATA [tsrc; _]       => Some (mkRVec none tsrc)
  | mkMVec (BINOP _) _ DATA [DATA; DATA; _] => Some (mkRVec none DATA)
  | mkMVec LOAD      _ DATA [DATA; tmem; _] => Some (mkRVec none tmem)
  | mkMVec STORE     _ DATA [DATA; tsrc; _] => Some (mkRVec none tsrc)
  | mkMVec JUMP      _ DATA [DATA]          => Some (mkRVec none none)
  | mkMVec BNZ       _ DATA [DATA]          => Some (mkRVec none none)
  | mkMVec JAL       _ DATA [DATA; _]       => Some (mkRVec none DATA)
  | mkMVec _         _ _ _                  => None
  end.

End WithVectors.

Definition stag_eq t1 t2 :=
  match t1, t2 with
    | DATA, DATA => true
    | KEY k1, KEY k2
    | SEALED k1, SEALED k2 => k1 == k2
    | _, _ => false
  end.

Lemma stag_eqP : Equality.axiom stag_eq.
Proof.
by move=> [|k1|k1] [|k2|k2] /=; apply: (iffP idP) => // [/eqP->|[->]].
Qed.

Definition stag_eqMixin := EqMixin stag_eqP.
Canonical stag_eqType := Eval hnf in EqType stag stag_eqMixin.

Program Instance sym_sealing : (symbolic_params) := {
  tag := stag_eqType;

  handler := sealing_handler;

  internal_state := key;  (* next key to generate *)

  memory := memory;
  sm := sm;

  registers := registers;
  sr := sr
}.

Import DoNotation. 

Definition mkkey (s : state t) : option (state t) :=
  let 'State mem reg pc@pct key := s in
  if key <? max_key then 
    let key' := inc_key key in
    do! reg' <- upd reg syscall_ret (max_word@(KEY key));
    Some (State mem reg' (pc + 1)%w@pct key')
  else
    None.

Definition seal (s : state t) : option (state t) :=
  let 'State mem reg pc@pct next_key := s in
  match get reg syscall_arg1, get reg syscall_arg2 with
  | Some (payload@DATA), Some (_@(KEY key)) =>
    do! reg' <- upd reg syscall_ret (payload@(SEALED key));
    Some (State mem reg' (pc + 1)%w@pct next_key)
  | _, _ => None
  end.

Definition unseal (s : state t) : option (state t) :=
  let 'State mem reg pc@pct next_key := s in
  match get reg syscall_arg1, get reg syscall_arg2 with
  | Some (payload@(SEALED key)), Some (_@(KEY key')) =>
    if key == key' then
      do! reg' <- upd reg syscall_ret (payload@DATA);
      Some (State mem reg' (pc + 1)%w@pct next_key)
    else None
  | _, _ => None
  end.

Definition sealing_syscalls : list (syscall t) :=
  [Syscall mkkey_addr mkkey;
   Syscall seal_addr seal;
   Syscall unseal_addr unseal].

Definition step := step sealing_syscalls.

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

End Sym.
