Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.ssrnat Ssreflect.seq.
Require Import CoqUtils.hseq.

Require Import lib.utils.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import DoNotation.

Fixpoint hmapo {I : Type} {T S : I -> Type} {idx : seq I}
               (f : forall i, T i -> option (S i))
               : hseq T idx -> option (hseq S idx) := 
  match idx with
    | [::]      => fun _   => Some [hseq]
    | i :: idx' => fun ts0 => let: (t::ts)%hseq := ts0
                              in do! t'  <- f i t;
                                 do! ts' <- hmapo f ts;
                                     Some (t' :: ts')%hseq
  end.

Fixpoint hzipwith {I : Type} {T1 T2 T' : I -> Type} {idx : seq I}
                  (f : forall i, T1 i -> T2 i -> T' i)
                  : hseq T1 idx -> hseq T2 idx -> hseq T' idx := 
  match idx with
    | [::]      =>  fun _    _    => [hseq]
    | i :: idx' => (fun t1s0 t2s0 => let: (t1::t1s) := t1s0 in
                                     let: (t2::t2s) := t2s0
                                     in f i t1 t2 :: hzipwith f t1s t2s)%hseq
  end.

Definition hzip {I : Type} {T1 T2 : I -> Type} {idx : seq I} : hseq T1 idx -> hseq T2 idx -> hseq (fun i => T1 i * T2 i)%type idx :=
  hzipwith (fun _ => pair).

Fixpoint hmapseq {I : Type} {T : I -> Type} {S : Type} {idx : seq I}
                 (f : forall i, T i -> S)
                 : hseq T idx -> seq S := 
  match idx with
    | [::]      => fun _   => [::]
    | i :: idx' => fun ts0 => let: (t::ts)%hseq := ts0
                              in f i t :: hmapseq f ts
  end.

Definition hhomogeneous {I : Type} {T : Type} {idx : seq I} : hseq (fun _ => T) idx -> seq T :=
  hmapseq (fun _ (t : T) => t).
