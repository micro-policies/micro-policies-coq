From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype finfun.
From CoqUtils Require Import hseq ord fset fmap word.
From MicroPolicies Require Import
  lib.utils lib.fmap_utils common.types symbolic.symbolic symbolic.exec
  ifc.labels ifc.common ifc.symbolic ifc.abstract ifc.noninterference ifc.refinementSA.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Noninterference.

Import DoNotation.

Variable L : labType.
Variable mt : machine_types.
Variable mops : machine_ops mt.
Context {sregs : syscall_regs mt}.
Context {addrs : ifc_addrs mt}.

Local Notation word := (mword mt).
Local Notation d_atom := (atom word L).

Local Notation sstate := (@Symbolic.state mt (sym_ifc L mt)).
Local Notation sstep :=
  (@stepf _ _ _ (@ifc_syscalls L mt mops sregs addrs)).
Local Notation strace :=
  (@symbolic.trace _ _ _ sregs addrs).
Local Notation astate := (ifc.abstract.state L mt).
Local Notation astep := (@step L mt mops sregs addrs).
Local Notation atrace :=
  (@abstract.trace _ _ _ sregs addrs).
Implicit Types (st : sstate).

Local Open Scope label_scope.

Inductive s_indist rs st1 st2 :=
| SIndist of  taga (Symbolic.pc st1) ⊑ rs
             &  Symbolic.pc st1 = Symbolic.pc st2
             &  pointwise (indist taga rs)
                          (Symbolic.regs st1) (Symbolic.regs st2)
             &  pointwise (indist (fun t =>
                                     if taga t is MemData rl
                                     then rl
                                     else ⊥) rs)
                          (Symbolic.mem st1) (Symbolic.mem st2)
             & Symbolic.internal st1 = IntIFC [::] [::]
             & Symbolic.internal st2 = IntIFC [::] [::].

Theorem noninterference rs st1 st2 n1 n2 :
  s_indist rs st1 st2 ->
  indist_seq_prefix eq
                    [seq x <- strace n1 st1 | taga x ⊑ rs]
                    [seq x <- strace n2 st2 | taga x ⊑ rs].
Proof.
move=> ind.
have {ind} ind:
  noninterference.s_indist rs (abs_of_sym mops st1) (abs_of_sym mops st2).
  case: ind => lo_pc e_pc ind_r ind_m int01 int02.
  rewrite /abs_of_sym; apply: SIndistLow=> //=.
    move=> ptr; rewrite !mapmE /=.
    move: (ind_m ptr).
    case: (Symbolic.mem st1 ptr) => [[v1 l1]|] //=;
    case: (Symbolic.mem st2 ptr) => [[v2 l2]|] //=.
    rewrite /indist /=.
    case: l1 l2 => [|l1] [|l2] //=; rewrite ?botP ?orbT ?eqxx /= => /eqP //.
    by move => [<-].
  by rewrite int01 int02 /=.
have [t1 et1] : exists t, atrace n1 (abs_of_sym mops st1) = strace n1 st1 ++ t.
  exact/refinement/abs_of_symP.
have [t2 et2] : exists t, atrace n2 (abs_of_sym mops st2) = strace n2 st2 ++ t.
  exact/refinement/abs_of_symP.
have:
  indist_seq_prefix eq
                    [seq x <- atrace n1 (abs_of_sym mops st1) | taga x ⊑ rs]
                    [seq x <- atrace n2 (abs_of_sym mops st2) | taga x ⊑ rs].
  exact: noninterference ind.
rewrite et1 et2 !filter_cat.
exact: indist_seq_prefix_sub.
Qed.

End Noninterference.
