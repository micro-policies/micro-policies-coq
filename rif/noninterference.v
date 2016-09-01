From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype finfun.
From CoqUtils Require Import hseq ord fset partmap word.
From MicroPolicies Require Import
  lib.utils lib.partmap_utils common.types rif.common rif.abstract.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Noninterference.

Import DoNotation.

Local Open Scope rif_scope.

Variable Σ : finType.
Variable mt : machine_types.
Variable mops : machine_ops mt.
Variable r_arg : reg mt.
Variable output_addr : mword mt.
Variable reclassify_addr : mword mt.

Local Notation rifAutomaton := (rifAutomaton Σ).
Local Notation rifLabel := (rifLabel Σ).
Local Notation event := (event Σ mt).
Local Notation ainstr := (ainstr Σ mt).
Local Notation atom := (atom (mword mt) rifLabel).
Local Notation state := (state Σ mt).
Local Notation step := (@step Σ mt mops r_arg output_addr reclassify_addr).
Local Notation stepn := (@stepn Σ mt mops r_arg output_addr reclassify_addr).

Implicit Type st : state.

CoInductive s_indist rs st1 st2 : Prop :=
| SIndistLow of rl_readers (taga (pc st1)) ⊑ᵣ rs
             &  pc st1 = pc st2
             &  pointwise (indist (@rl_readers _ \o taga) rs)
                          (regs st1) (regs st2)
             &  pointwise (indist (fun t =>
                                     if t is inr t'
                                     then rl_readers (taga t')
                                     else Anybody) rs)
                          (mem st1) (mem st2)
| SIndistHigh of ~~ (rl_readers (taga (pc st1)) ⊑ᵣ rs)
              &  ~~ (rl_readers (taga (pc st2)) ⊑ᵣ rs).

Ltac match_upd t1 :=
  match goal with
  | ind : pointwise ?P t1 ?t2,
    upd : updm t1 ?x ?v1 = Some ?t1'
    |- context[updm ?t2 ?x ?v2] =>
    have: P v1 v2; last move=> /(refine_upd_pointwiseL ind upd)
  end.

Lemma low_step rs st1 st2 st1' oe1 :
  s_indist rs st1 st2 ->
  rl_readers (taga (pc st1)) ⊑ᵣ rs ->
  step st1 = Some (st1', oe1) ->
  match step st2 with
  | Some (st2', oe2) =>
    match oe1, oe2 with
    | Some (Output w1 rs1), Some (Output w2 rs2) =>
      indist (@snd _ _) rs (w1, rs1) (w2, rs2)
      /\ s_indist rs st1' st2'
    | Some (Reclassify rl1 F1), Some (Reclassify rl2 F2) =>
      (rl1 == rl2) && (F1 == F2)
    | None, None => s_indist rs st1' st2'
    | _, _ => False
    end
  | None => False
  end.
Proof.
move=> h_indist h_low1; case: h_indist; last by rewrite h_low1.
rewrite (lock step).
case: st1 {h_low1} => mem1 reg1 [pc1 rl1] oF1 /=.
case: st2=> mem2 reg2 [pc2 rl2] oF2 /= h_pc e.
move: pc1 rl1 e h_pc => pc rl [<- <-] h_pc {pc2 rl2} ind_r ind_m.
rewrite -{1}lock /=.
move: (ind_m pc).
case get_pc1: (mem1 pc) => [[i1|a1]|] //=;
case get_pc2: (mem2 pc) => [[i2|a2]|] //=;
rewrite /indist /=.
  (* Instructions *)
  move=> e; move: i1 e get_pc1 get_pc2 => i /eqP [<-] {i2}.
  case: i=> //=.
  - (* Nop *)
    move=> get_pc1 get_pc2 [<- <-] {st1' oe1}.
    by rewrite -lock /= get_pc2; constructor.
  - (* Const *)
    move=> k r get_pc1 get_pc2.
    case upd1: updm=> [reg1'|] //= [<- <-] {st1' oe1}.
    rewrite -lock /= get_pc2.
    match_upd reg1; first exact: indist_refl.
    case=> reg2' [upd2 ind_r'].
    by rewrite upd2 /=; constructor.
  - (* Mov *)
    move=> r1 r2 get_pc1 get_pc2.
    move: (ind_r r1).
    case get1: (reg1 r1) => [v1|] //=.
    case get2: (reg2 r1) => [v2|] //= ind_v.
    case upd1: (updm reg1) => [reg1'|] //= [<- <-] {st1' oe1}.
    rewrite -lock /= get_pc2 get2 /=.
    match_upd reg1=> // - [reg2' [upd2 ind_r']].
    by rewrite upd2 /=; constructor.
  - (* Binop *)
    move=> b r1 r2 r3 get_pc1 get_pc2.
    move: (ind_r r1).
    case get11: (reg1 r1) => [[v11 l11]|] //=.
    case get12: (reg2 r1) => [[v12 l12]|] //= ind_v1.
    move: (ind_r r2).
    case get21: (reg1 r2) => [[v21 l21]|] //=.
    case get22: (reg2 r2) => [[v22 l22]|] //= ind_v2.
    case upd1: updm=> [reg1'|] //= [<- <-] {st1' oe1}.
    rewrite -lock /= get_pc2 get12 get22 /=.
    match_upd reg1=> //=.
      move: ind_v1 ind_v2; rewrite /indist /= !rl_readers_join !readers_join_min.
      by repeat match goal with
      | |- context[_ ⊑ᵣ _] => case: readers_leq=> //=
      end; move=> /eqP [-> ->] /eqP [-> ->].
    case=> regs2' [upd2 ind_r'].
    by rewrite upd2 /=; constructor.
  - (* Load *)
    move=> r1 r2 get_pc1 get_pc2.
    move: (ind_r r1).
    case get_r1: (reg1 r1) => [[v1 l1]|] //=.
    case get_r2: (reg2 r1) => [[v2 l2]|] //= ind_v.
    move: (ind_m v1).
    admit.
  - (* Store *)
    move=> r1 r2 get_pc1 get_pc2.
    move: (ind_r r1).
    case get_r11: (reg1 r1) => [[v11 l11]|] //=.
    case get_r12: (reg2 r1) => [[v12 l12]|] //= ind_v1.
    move: (ind_r r2).
    case get_r21: (reg1 r2) => [[v21 l21]|] //=.
    case get_r22: (reg2 r2) => [[v22 l22]|] //= ind_v2.
    admit.
  - (* Jump *)
    move=> r get_pc1 get_pc2.
    move: (ind_r r).
    case get_r1: (reg1 r) => [[v1 l1]|] //=.
    case get_r2: (reg2 r) => [[v2 l2]|] //= ind_v [<- <-] {st1' oe1}.
    rewrite -lock /= get_pc2 get_r2 /=.
    case/indistP: ind_v=> /= [lo1 lo2 [<- <-]|hi1 hi2].
      constructor=> //=.
      by rewrite rl_readers_join readers_join_min lo1.
    by apply: SIndistHigh=> //=;
    rewrite rl_readers_join readers_join_min negb_and ?hi1 ?hi2.
  - (* Bnz *)
    move=> r i get_pc1 get_pc2.
    move: (ind_r r).
    case get_r1: (reg1 r) => [[v1 l1]|] //=.
    case get_r2: (reg2 r) => [[v2 l2]|] //= ind_v [<- <-] {st1' oe1}.
    rewrite -lock /= get_pc2 get_r2 /=.
    case/indistP: ind_v=> /= [lo1 lo2 [<- <-]|hi1 hi2].
      constructor=> //=.
      by rewrite rl_readers_join readers_join_min lo1.
    by apply: SIndistHigh=> //=;
    rewrite rl_readers_join readers_join_min negb_and ?hi1 ?hi2.
  (* Jal *)
  move=> r oF get_pc1 get_pc2.
  move: (ind_r r).
  case get_r1: (reg1 r) => [[v1 l1]|] //=.
  case get_r2: (reg2 r) => [[v2 l2]|] //= ind_v.
  case upd1: updm => [reg1'|] //= [<- <-] {st1' oe1}.
  rewrite -lock /= get_pc2 get_r2 /=.
  admit.
(* System services *)
admit.
Admitted.

End Noninterference.
