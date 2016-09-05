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
  | None => True
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
    case/indistP: ind_v get_r1 get_r2=> [/= lo _ [<- <-] {v2 l2}|/= hi1 hi2].
      (* Both pointers are low *)
      move: v1 l1 lo => v l lo get_r1 get_r2.
      move: (ind_m v).
      case getm_v1: (mem1 v)=> [[|[v1 l1]]|] //=.
      case getm_v2: (mem2 v)=> [[|[v2 l2]]|] //=.
        by rewrite {1}/indist orbT implybF.
      move=> ind_v.
      case upd1: updm => [reg1'|] //= [<- <-] {st1' oe1}.
      rewrite -lock /= get_pc2 get_r2 /= getm_v2 /=.
      match_upd reg1.
        move: ind_v; rewrite /indist /= -sum_eqE /=.
        rewrite !rl_readers_join !readers_join_min.
        case: (rl_readers l1 ⊑ᵣ rs)=> //=.
          by move=> /eqP [-> ->]; rewrite eqxx implybT.
        rewrite andbF /=.
        case: (rl_readers l2 ⊑ᵣ rs)=> //= [|_].
          by move=> /eqP [-> ->]; rewrite eqxx implybT.
        by rewrite andbF.
      case=> reg2' [upd2 ind_r'].
      rewrite upd2 /=.
      by constructor.
    (* Both pointers are high *)
    move=> get_r1 get_r2.
    case getm_v1: (mem1 v1)=> [[|[v1' l1']]|] //=.
    case upd1: updm => [reg1'|] //= [<- <-] {st1' oe1}.
    rewrite -lock /= get_pc2 get_r2 /=.
    case getm_v2: (mem2 v2)=> [[|[v2' l2']]|] //=.
    match_upd reg1.
      rewrite /indist /= !rl_readers_join !readers_join_min.
      by rewrite implybE negb_or !negb_and hi1 hi2 /=.
    case=> reg2' [upd2 ind_r'].
    by rewrite upd2 /=; constructor.
  - (* Store *)
    move=> rptr rv get_pc1 get_pc2.
    move: (ind_r rptr).
    case get_rptr1: (reg1 rptr) => [[ptr1 lptr1]|] //=.
    case get_rptr2: (reg2 rptr) => [[ptr2 lptr2]|] //= ind_ptr.
    move: (ind_r rv).
    case get_rv1: (reg1 rv) => [[v1 lv1]|] //=.
    case get_rv2: (reg2 rv) => [[v2 lv2]|] //=.
    rewrite {1}/indist /= => ind_v.
    case/indistP: ind_ptr get_rptr1 get_rptr2
                  => [/= lo _ [<- <-] {ptr2 lptr2}|/= hi1 hi2].
      (* Both pointers are low *)
      move: ptr1 lptr1 lo => ptr lptr lo get_rptr1 get_rptr2.
      move: (ind_m ptr).
      case getm_ptr1: (mem1 ptr)=> [[|[vold1 lvold1]]|] //=.
      case getm_ptr2: (mem2 ptr)=> [[|[vold2 lvold2]]|] //=.
        by rewrite {1}/indist orbT -sum_eqE.
      rewrite {1}/indist /= -sum_eqE /=.
      rewrite rl_join_min; case: ifP=> //= /andP [lo_lptr1 lo_rl1].
      case upd1: updm=> [mem1'|] //= ind_vold [<- <-] {st1' oe1}.
      rewrite -lock /= get_pc2 get_rptr2 /= getm_ptr2 /= get_rv2 /=.
      rewrite rl_join_min; case: ifP=> //= /andP [lo_lptr2 lo_rl2].
      match_upd mem1.
        rewrite /indist /= !rl_readers_join !readers_join_min h_pc !andbT.
        rewrite -sum_eqE /= -andb_orr; apply/implyP=> /andP [lo_lptr_rs lo_lv_rs].
        by move/implyP/(_ lo_lv_rs)/eqP: ind_v => [-> ->].
      by case=> mem2' [upd2 ind_m']; rewrite upd2 /=; constructor.
    (* Both pointers are high *)
    move=> get_rptr1 get_rptr2.
    case getm_ptr1: (mem1 ptr1)=> [[|[vold1 lvold1]]|] //=.
    rewrite rl_join_min; case: ifP=> //= /andP [lo_lptr1 lo_rl1].
    case upd1: updm=> [mem1'|] //= [<- <-] {st1' oe1}.
    rewrite -lock /= get_pc2 /= get_rptr2 /= get_rv2 /=.
    case getm_ptr2: (mem2 ptr2)=> [[|[vold2 lvold2]]|] //=.
    rewrite rl_join_min; case: ifP=> //= /andP [lo_lptr2 lo_rl2].
    rewrite /updm getm_ptr2 /=; constructor=> // x /=.
    rewrite (updm_set upd1) !setmE; move: (ind_m x) {upd1}.
    have [-> {x}|] := altP (x =P ptr1).
      have [_ {ptr2 getm_ptr2 get_rptr2}|_] := altP (ptr1 =P ptr2).
        rewrite /indist /= -sum_eqE /= !rl_readers_join !readers_join_min.
        by rewrite (negbTE hi1) (negbTE hi2) /=.
      rewrite getm_ptr1.
      move: ptr1 lptr1 hi1 get_rptr1 lo_lptr1 getm_ptr1
            {ptr2 lptr2 hi2 get_rptr2 getm_ptr2 vold2 lvold2 lo_lptr2 lo_rl2}
            => ptr lptr hi1 get_rptr1 lo_lptr1 getm_ptr1.
      case getm_ptr2: (mem2 ptr)=> [[|[vold2 lvold2]]|] //=.
        by rewrite /indist /= orbT -sum_eqE /=.
      rewrite /indist /= !rl_readers_join !readers_join_min -sum_eqE /=.
      rewrite (negbTE hi1) /= => ind_vold; apply/implyP=> lo_lvold2.
      move: ind_vold getm_ptr2.
      rewrite lo_lvold2 orbT /=  => /eqP [evold elvold].
      move: evold elvold lo_lvold2 => <- <- {vold2 lvold2} lo_lvold.
      by move: hi1; rewrite (readers_leq_trans (rl_readers_leq lo_lptr1) lo_lvold).
    have [-> {x} _|//] := altP (x =P ptr2).
    rewrite getm_ptr2 => {ptr1 lptr1 vold1 lvold1 hi1 lo_lptr1 lo_rl1 get_rptr1 getm_ptr1}.
    case getm_ptr1: (mem1 ptr2) => [[|[vold1 lvold1]]|] //=.
    rewrite /indist /= !rl_readers_join !readers_join_min -sum_eqE /= (negbTE hi2) /=.
    rewrite orbF => ind_vold; apply/implyP=> low_lvold1.
    move: ind_vold lo_lptr2; rewrite low_lvold1 /= => /eqP [_ <-] lo_lptr2.
    by move: hi2; rewrite (readers_leq_trans (rl_readers_leq lo_lptr2) low_lvold1).
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
  match_upd reg1.
    rewrite /indist /= !rl_readers_join !readers_join_min !h_pc !andbT.
    case/indistP: ind_v=> [-> -> [_ ->]//=|/= hi1 hi2].
      by rewrite -[X in X ==> _]negbK negb_or hi1 hi2.
  case=> reg2' [upd2 ind_r'].
  rewrite upd2 /=.
  case/indistP: ind_v upd1 upd2=> [/= lo1 lo2 [<- <-]|/= hi1 hi2] upd1 upd2.
    constructor=> //=.
    by rewrite rl_readers_join readers_join_min lo1 /=.
  by apply: SIndistHigh=> //=;
  rewrite rl_readers_join readers_join_min negb_and ?hi1 ?hi2.
(* System services *)
admit.
Admitted.

End Noninterference.
