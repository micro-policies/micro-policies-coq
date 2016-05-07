From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq.

Require Import lib.utils.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Definition rem_all {T : eqType} : T -> seq T -> seq T :=
  filter \o predC1.

(* This corollary's proof is so trivial, you'd think we could always use
   `rewrite mem_filter /=` instead.  That's true, but I'd rather have an actual
   lemma so that we're not dependent on implementation details. *)
Corollary in_rem_all (T : eqType) (a b : T) (xs : seq T) :
  a \in rem_all b xs = (a != b) && (a \in xs).
Proof. by rewrite mem_filter. Qed.
