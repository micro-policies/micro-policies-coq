Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Require Import ord word.
Require Import common.common.

Section WithClasses.

Context {t    : machine_types}
        {ops  : machine_ops t}
        {spec : machine_ops_spec ops}.

Local Notation word := (mword t).
Open Scope word_scope.
Open Scope ord_scope.

Definition range (l h : word) := [pred e | l <= e <= h].

End WithClasses.
