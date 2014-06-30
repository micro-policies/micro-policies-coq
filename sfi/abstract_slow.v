Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Require Import common.common.
Require Import sfi.classes sfi.abstract.

Set Bullet Behavior "Strict Subproofs".

Module AbsSlow.

Section WithClasses.

Set Implicit Arguments.

Context (t            : machine_types)
        {ops          : machine_ops t}
        {ap           : abstract_params t}
        {scr          : @syscall_regs t}
        {sfi_syscalls : sfi_syscall_addrs t}.

Definition state := option (@Abs.state t ap).

Inductive step (s s' : state) : Prop :=
| step_go   : forall MM MM'
                     (PREV : s  = Some MM)
                     (NEXT : s' = Some MM')
                     (STEP : Abs.step MM MM'),
                step s s'
| step_stop : forall MM
                     (PREV : s  = Some MM)
                     (NEXT : s' = None)
                     (STOP : forall MM', ~ Abs.step MM MM'),
                step s s'.

Theorem slow_same : forall MM MM',
  step (Some MM) (Some MM') <-> Abs.step MM MM'.
Proof.
  move=> MM MM'; split.
  - by move=> [? ? [<-] [<-]|].
  - by move=> ?; eapply step_go.
Qed.

Theorem slow_stops_late : forall MM,
  step (Some MM) None <-> forall MM', ~ Abs.step MM MM'.
Proof.
  move=> MM; split.
  - by move=> [|? [<-]].
  - by move=> NO; apply: step_stop.
Qed.

Theorem slow_stopped : forall s',
  ~ step None s'.
Proof. by move=> s' []. Qed.

Definition good_state (s : state) : bool :=
  match s with
    | Some MM => Abs.good_state MM
    | None    => true
  end.

End WithClasses.

End AbsSlow.
