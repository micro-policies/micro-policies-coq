Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Require Import ord hseq word partmap.

Require Import lib.utils common.common.
Require Import symbolic.symbolic sealing.classes.

Import Symbolic.

Set Implicit Arguments.

Module Sym.

Section WithClasses.

Context {t : machine_types}
        {ops : machine_ops t}
        {opss : machine_ops_spec ops}
        {scr : @syscall_regs t}
        {ssa : @sealing_syscall_addrs t}.

Open Scope ord_scope.

Class sealing_key := {
  key : ordType;
  max_key;
  inc_key : key -> key;
  ltb_inc : forall sk, sk < max_key -> sk < inc_key sk
}.

Context {sk : sealing_key}.

(* We represent keys as tags on dummy values instead of payloads
  because this eliminates conversions from keys to words and back. *)
Inductive stag :=
| DATA   :        stag
| KEY    : key -> stag
| SEALED : key -> stag.

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

Definition stags : tag_kind -> eqType := fun k =>
  match k with
  | P => [eqType of unit]
  | _ => [eqType of stag]
  end.

Section WithHLists.

Definition sealing_handler (iv : IVec stags) : option (VOVec stags (op iv)) :=
  match iv with
  | mkIVec (OP NOP)       tt DATA [hseq]               => Some (@mkOVec stags NOP tt tt)
  | mkIVec (OP CONST)     tt DATA [hseq _]             => Some (@mkOVec stags CONST tt DATA)
  | mkIVec (OP MOV)       tt DATA [hseq tsrc; _]       => Some (@mkOVec stags MOV tt tsrc)
  | mkIVec (OP (BINOP o)) tt DATA [hseq DATA; DATA; _] => Some (@mkOVec stags (BINOP o) tt DATA)
  | mkIVec (OP LOAD)      tt DATA [hseq DATA; tmem; _] => Some (@mkOVec stags LOAD tt tmem)
  | mkIVec (OP STORE)     tt DATA [hseq DATA; tsrc; _] => Some (@mkOVec stags STORE tt tsrc)
  | mkIVec (OP JUMP)      tt DATA [hseq DATA]          => Some (@mkOVec stags JUMP tt tt)
  | mkIVec (OP BNZ)       tt DATA [hseq DATA]          => Some (@mkOVec stags BNZ tt tt)
  | mkIVec (OP JAL)       tt DATA [hseq DATA; _]       => Some (@mkOVec stags JAL tt DATA)
  | mkIVec SERVICE        tt _    [hseq]               => Some tt
  | mkIVec _              tt _ _                       => None
  end.

End WithHLists.

Program Instance sym_sealing : params := {
  ttypes := stags;

  transfer := sealing_handler;

  internal_state := key  (* next key to generate *)
}.

Import DoNotation.

Definition mkkey (s : state t) : option (state t) :=
  let 'State mem reg pc@pct key := s in
  if key <? max_key then
    let key' := inc_key key in
    do! reg' <- upd reg syscall_ret ((max_word t)@(KEY key));
    do! ret  <- get reg ra;
    match ret with
    | pc'@DATA => Some (State mem reg' (pc'@tt) key')
    | _ => None
    end
  else
    None.

Definition seal (s : state t) : option (state t) :=
  let 'State mem reg pc@pct next_key := s in
  match get reg syscall_arg1, get reg syscall_arg2 with
  | Some (payload@DATA), Some (_@(KEY key)) =>
    do! reg' <- upd reg syscall_ret (payload@(SEALED key));
    do! ret  <- get reg ra;
    match ret with
    | pc'@DATA => Some (State mem reg' (pc'@tt) next_key)
    | _ => None
    end
  | _, _ => None
  end.

Definition unseal (s : state t) : option (state t) :=
  let 'State mem reg pc@pct next_key := s in
  match get reg syscall_arg1, get reg syscall_arg2 with
  | Some (payload@(SEALED key)), Some (_@(KEY key')) =>
    if key == key' then
      do! reg' <- upd reg syscall_ret (payload@DATA);
      do! ret  <- get reg ra;
      match ret with
      | pc'@DATA => Some (State mem reg' (pc'@tt) next_key)
      | _ => None
      end
    else None
  | _, _ => None
  end.

Definition sealing_syscalls : list (syscall t) :=
  [Syscall mkkey_addr DATA mkkey;
   Syscall seal_addr DATA seal;
   Syscall unseal_addr DATA unseal].

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

Notation memory t := (Symbolic.memory t sym_sealing).
Notation registers t := (Symbolic.registers t sym_sealing).

End Sym.
