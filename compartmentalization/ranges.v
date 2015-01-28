Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Require Import ord word.
Require Import common.types.

Section WithClasses.

Context {mt   : machine_types}
        {ops  : machine_ops mt}
        {spec : machine_ops_spec ops}.

Local Notation word := (mword mt).
Open Scope word_scope.
Open Scope ord_scope.

Definition range (l h : word) := [pred e | l <= e <= h].

End WithClasses.
