Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.ssrnat Ssreflect.seq.
Require Import CoqUtils.ord CoqUtils.hseq CoqUtils.word CoqUtils.partmap.

Require Import lib.utils common.types.
Require Import symbolic.symbolic sealing.classes.

Import Symbolic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Sym.

Section WithClasses.

Context {mt : machine_types}
        {ops : machine_ops mt}
        {opss : machine_ops_spec ops}
        {scr : syscall_regs mt}
        {ssa : @sealing_syscall_addrs mt}.

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

Section WithHSeqs.

Definition sealing_handler (iv : ivec stags) : option (vovec stags (op iv)) :=
  match iv with
  | IVec (OP NOP)       tt DATA [hseq]               => Some (@OVec stags NOP tt tt)
  | IVec (OP CONST)     tt DATA [hseq _]             => Some (@OVec stags CONST tt DATA)
  | IVec (OP MOV)       tt DATA [hseq tsrc; _]       => Some (@OVec stags MOV tt tsrc)
  | IVec (OP (BINOP o)) tt DATA [hseq DATA; DATA; _] => Some (@OVec stags (BINOP o) tt DATA)
  | IVec (OP LOAD)      tt DATA [hseq DATA; tmem; _] => Some (@OVec stags LOAD tt tmem)
  | IVec (OP STORE)     tt DATA [hseq DATA; tsrc; _] => Some (@OVec stags STORE tt tsrc)
  | IVec (OP JUMP)      tt DATA [hseq DATA]          => Some (@OVec stags JUMP tt tt)
  | IVec (OP BNZ)       tt DATA [hseq DATA]          => Some (@OVec stags BNZ tt tt)
  | IVec (OP JAL)       tt DATA [hseq DATA; _]       => Some (@OVec stags JAL tt DATA)
  | IVec SERVICE        tt _    [hseq]               => Some tt
  | IVec _              tt _ _                       => None
  end.

End WithHSeqs.

Program Instance sym_sealing : params := {
  ttypes := stags;

  transfer := sealing_handler;

  internal_state := key  (* next key to generate *)
}.

Import DoNotation.

Definition mkkey (s : state mt) : option (state mt) :=
  let 'State mem reg pc@pct key := s in
  if key < max_key then
    let key' := inc_key key in
    do! reg' <- updm reg syscall_ret monew@(KEY key);
    do! ret  <- reg ra;
    match ret with
    | pc'@DATA => Some (State mem reg' (pc'@tt) key')
    | _ => None
    end
  else
    None.

Definition seal (s : state mt) : option (state mt) :=
  let 'State mem reg pc@pct next_key := s in
  match reg syscall_arg1, reg syscall_arg2 with
  | Some payload@DATA, Some _@(KEY key) =>
    do! reg' <- updm reg syscall_ret payload@(SEALED key);
    do! ret  <- reg ra;
    match ret with
    | pc'@DATA => Some (State mem reg' (pc'@tt) next_key)
    | _ => None
    end
  | _, _ => None
  end.

Definition unseal (s : state mt) : option (state mt) :=
  let 'State mem reg pc@pct next_key := s in
  match reg syscall_arg1, reg syscall_arg2 with
  | Some payload@(SEALED key), Some _@(KEY key') =>
    if key == key' then
      do! reg' <- updm reg syscall_ret payload@DATA;
      do! ret  <- reg ra;
      match ret with
      | pc'@DATA => Some (State mem reg' (pc'@tt) next_key)
      | _ => None
      end
    else None
  | _, _ => None
  end.

Definition sealing_syscalls : seq (syscall mt) :=
  [:: Syscall mkkey_addr DATA mkkey;
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

Notation memory mt := (Symbolic.memory mt sym_sealing).
Notation registers mt := (Symbolic.registers mt sym_sealing).

End Sym.
