From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype fintype finfun.
From CoqUtils Require Import hseq ord fset partmap.

Section Dev.

Parameter F : finType.

Record rifAutomaton := RifAutomaton {
  rif_states : nat;
  rif_trans : {ffun 'I_rif_states * F -> 'I_rif_states};
  rif_prins : {ffun 'I_rif_states -> {fset nat}}
}.

End Dev.
