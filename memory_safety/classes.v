From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import common.types.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive syscall := Malloc | Free | Size | Base | Eq.

Scheme Equality for syscall.

Lemma syscall_eqP : Equality.axiom syscall_beq.
Proof.
move=> sc1 sc2; apply/(iffP idP).
exact: internal_syscall_dec_bl.
exact: internal_syscall_dec_lb.
Qed.

Definition syscall_eqMixin := EqMixin syscall_eqP.

Canonical syscall_eqType := Eval hnf in EqType syscall syscall_eqMixin.

Definition syscalls :=
  [:: Malloc; Free; Size; Base; Eq].

Class memory_syscall_addrs mt := {
  addr : syscall -> mword mt;
  uniq_addr : injective addr
}.

Section Syscalls.

Context mt {sc : memory_syscall_addrs mt}.

Definition syscall_of_addr (a : mword mt) :=
  nth None (map some syscalls)
      (find (pred1 a) [seq addr sc | sc <- syscalls]).

Lemma addrK : pcancel addr syscall_of_addr.
Proof.
by case; rewrite /syscall_of_addr /= !(inj_eq (@uniq_addr _ sc)).
Qed.

End Syscalls.
