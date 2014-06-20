Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Require Import common.common.
Require Import sfi.classes sfi.abstract.

Module AbsSlow.

Section WithClasses.

Set Implicit Arguments.

Context (t   : machine_types)
        {ops : machine_ops t}
        {ap  : abstract_params t}
        {sfi_syscalls : sfi_syscall_params t}.

Definition state := option (@Abs.state t ap).

Inductive step (othercalls : list (@Abs.syscall t ap)) (s s' : state) : Prop :=
| step_go   : forall MM MM'
                     (PREV : s  = Some MM)
                     (NEXT : s' = Some MM')
                     (STEP : Abs.step othercalls MM MM'),
                step othercalls s s'
| step_stop : forall MM
                     (PREV : s  = Some MM)
                     (NEXT : s' = None)
                     (STOP : forall MM', ~ Abs.step othercalls MM MM'),
                step othercalls s s'.

Theorem slow_same : forall othercalls MM MM',
  step othercalls (Some MM) (Some MM') <-> Abs.step othercalls MM MM'.
Proof.
  move=> oc MM MM'; split.
  - by move=> [? ? [<-] [<-]|].
  - by move=> ?; eapply step_go.
Qed.

Theorem slow_stops_late : forall othercalls MM,
  step othercalls (Some MM) None <-> forall MM', ~ Abs.step othercalls MM MM'.
Proof.
  move=> oc MM; split.
  - by move=> [|? [<-]].
  - by move=> NO; apply: step_stop.
Qed.

Theorem slow_stopped : forall othercalls s',
  ~ step othercalls None s'.
Proof. by move=> oc s' []. Qed.

End WithClasses.

End AbsSlow.
