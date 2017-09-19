From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype finfun.
From CoqUtils Require Import hseq ord fset fmap word.
From MicroPolicies Require Import
  lib.utils lib.fmap_utils common.types ifc.labels ifc.common ifc.abstract.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Noninterference.

Import DoNotation.

Local Open Scope label_scope.

Variable L : labType.
Variable mt : machine_types.
Variable mops : machine_ops mt.

Local Notation word := (mword mt).
Local Notation atom := (atom word L).
Context {sregs : syscall_regs mt}.
Context {addrs : ifc_addrs mt}.

Local Notation state := (state L mt).
Local Notation step := (@step L mt mops sregs addrs).
Local Notation trace := (@trace L mt mops sregs addrs).

Implicit Type st : state.

Definition indist_call_frame rs (cf1 cf2 : call_frame mt L) :=
  [/\ indist taga rs (cf_pc cf1) (cf_pc cf2) &
      pointwise (indist taga rs) (cf_regs cf1) (cf_regs cf2)].

Lemma indist_call_frame_sym rs cf1 cf2 :
  indist_call_frame rs cf1 cf2 ->
  indist_call_frame rs cf2 cf1.
Proof.
  case; rewrite indist_sym => ? ind_regs.
  split=> //.
  apply: pointwise_sym ind_regs.
  by move=> ??; rewrite indist_sym.
Qed.

Definition indist_stacks high rs (stk1 stk2 : seq (call_frame mt L)) :=
  nosimpl (if high then
    indist_seq (indist_call_frame rs)
               (reap (fun cf => ~~ (taga (cf_pc cf) ⊑ rs)) stk1)
               (reap (fun cf => ~~ (taga (cf_pc cf) ⊑ rs)) stk2)
  else
    indist_seq (indist_call_frame rs) stk1 stk2).

Lemma indist_stacks_sym high rs stk1 stk2 :
  indist_stacks high rs stk1 stk2 ->
  indist_stacks high rs stk2 stk1.
Proof.
rewrite /indist_stacks; case: high;
apply: indist_seq_sym;
exact: indist_call_frame_sym.
Qed.

Lemma indist_stacks_strengthen rs stk1 stk2 :
  indist_stacks false rs stk1 stk2 ->
  indist_stacks true rs stk1 stk2.
Proof.
rewrite /indist_stacks /=.
elim: stk1 stk2=> [|cf1 stk1 IH] [|cf2 stk2] //= [ind_cf ind_stk].
case: (ind_cf)=> [ind_pc _].
case/indistP: (ind_pc) => [l1 l2 e|h1 h2].
  by rewrite l1 l2 /=; split.
by rewrite h1 h2 /=; apply: IH.
Qed.

CoInductive s_indist rs st1 st2 : Prop :=
| SIndistLow of taga (pc st1) ⊑ rs
             &  pc st1 = pc st2
             &  pointwise (indist (taga) rs)
                          (regs st1) (regs st2)
             &  pointwise (indist (fun t =>
                                     if t is inr t'
                                     then (taga t')
                                     else ⊥) rs)
                          (mem st1) (mem st2)
             & indist_stacks false rs (call_stack st1) (call_stack st2)
| SIndistHigh of ~~ (taga (pc st1) ⊑ rs)
              &  ~~ (taga (pc st2) ⊑ rs)
              &  pointwise (indist (fun t =>
                                      if t is inr t'
                                      then (taga t')
                                      else ⊥) rs)
                           (mem st1) (mem st2)
              & indist_stacks true rs (call_stack st1) (call_stack st2).

Lemma s_indist_sym rs st1 st2 :
  s_indist rs st1 st2 -> s_indist rs st2 st1.
Proof.
case.
  move=> lo epc i_r i_m i_stk.
  apply: SIndistLow.
  - by rewrite -epc.
  - exact/esym.
  - by apply: pointwise_sym=> // ??; rewrite indist_sym.
  - by apply: pointwise_sym=> // ??; rewrite indist_sym.
  exact: indist_stacks_sym.
move=> hi1 hi2 i_m i_stk.
apply: SIndistHigh=> //.
  by apply: pointwise_sym=> // ??; rewrite indist_sym.
exact: indist_stacks_sym.
Qed.

Ltac match_upd t1 :=
  match goal with
  | ind : pointwise ?P t1 ?t2,
    upd : updm t1 ?x ?v1 = Some ?t1'
    |- context[updm ?t2 ?x ?v2] =>
    have: P v1 v2; last move=> /(refine_upd_pointwiseL ind upd)
  end.

Lemma low_step rs st1 st2 st1' oe1 :
  s_indist rs st1 st2 ->
  taga (pc st1) ⊑ rs ->
  step st1 = Some (st1', oe1) ->
  match step st2 with
  | Some (st2', oe2) =>
    s_indist rs st1' st2'
    /\ indist (oapp taga ⊥) rs oe1 oe2
  | None => True
  end.
Proof.
move=> h_indist h_low1; case: h_indist; last by rewrite h_low1.
rewrite (lock step).
case: st1 {h_low1} => mem1 reg1 [pc1 rl1] stk1 /=.
case: st2=> mem2 reg2 [pc2 rl2] stk2 /= h_pc e.
move: pc1 rl1 e h_pc => pc rl [<- <-] h_pc {pc2 rl2} ind_r ind_m ind_stk.
rewrite -{1}lock /=.
move: (ind_m pc).
case get_pc1: (mem1 pc) => [[i1|a1]|] //=;
case get_pc2: (mem2 pc) => [[i2|a2]|] //=;
rewrite /indist ?botP //=.
  (* Instructions *)
  move=> e; move: i1 e get_pc1 get_pc2 => i /eqP [<-] {i2}.
  case: i=> //=.
  - (* Nop *)
    move=> get_pc1 get_pc2 [<- <-] {st1' oe1}.
    by rewrite -lock /= get_pc2 implybT; split; constructor.
  - (* Const *)
    move=> k r get_pc1 get_pc2.
    case upd1: updm=> [reg1'|] //= [<- <-] {st1' oe1}.
    rewrite -lock /= get_pc2.
    match_upd reg1; first exact: indist_refl.
    case=> reg2' [upd2 ind_r'].
    by rewrite upd2 /= implybT; split; constructor.
  - (* Mov *)
    move=> r1 r2 get_pc1 get_pc2.
    move: (ind_r r1).
    case get1: (reg1 r1) => [v1|] //=.
    case get2: (reg2 r1) => [v2|] //= ind_v.
    case upd1: (updm reg1) => [reg1'|] //= [<- <-] {st1' oe1}.
    rewrite -lock /= get_pc2 get2 /=.
    match_upd reg1=> // - [reg2' [upd2 ind_r']].
    by rewrite upd2 /= implybT; split; constructor.
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
      move: ind_v1 ind_v2; rewrite /indist /= !flows_join.
      by repeat match goal with
      | |- context[_ ⊑ _] => case: flows=> //=
      end; move=> /eqP [-> ->] /eqP [-> ->].
    case=> regs2' [upd2 ind_r'].
    by rewrite upd2 /= implybT; split; constructor.
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
        by rewrite {1}/indist botP orbT implybF.
      move=> ind_v.
      case upd1: updm => [reg1'|] //= [<- <-] {st1' oe1}.
      rewrite -lock /= get_pc2 get_r2 /= getm_v2 /=.
      match_upd reg1.
        move: ind_v; rewrite /indist /= -sum_eqE /=.
        rewrite !flows_join.
        case: (l1 ⊑ rs)=> //=.
          by move=> /eqP [-> ->]; rewrite eqxx implybT.
        rewrite andbF /=.
        case: (l2 ⊑ rs)=> //= [|_].
          by move=> /eqP [-> ->]; rewrite eqxx implybT.
        by rewrite andbF.
      case=> reg2' [upd2 ind_r'].
      rewrite upd2 /= implybT.
      by split; constructor.
    (* Both pointers are high *)
    move=> get_r1 get_r2.
    case getm_v1: (mem1 v1)=> [[|[v1' l1']]|] //=.
    case upd1: updm => [reg1'|] //= [<- <-] {st1' oe1}.
    rewrite -lock /= get_pc2 get_r2 /=.
    case getm_v2: (mem2 v2)=> [[|[v2' l2']]|] //=.
    match_upd reg1.
      rewrite /indist /= !flows_join.
      by rewrite implybE negb_or !negb_and hi1 hi2 /=.
    case=> reg2' [upd2 ind_r'].
    by rewrite upd2 /= implybT; split; constructor.
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
        by rewrite {1}/indist botP orbT -sum_eqE.
      rewrite {1}/indist /= -sum_eqE /=.
      rewrite flows_join; case: ifP=> //= /andP [lo_lptr1 lo_rl1].
      case upd1: updm=> [mem1'|] //= ind_vold [<- <-] {st1' oe1}.
      rewrite -lock /= get_pc2 get_rptr2 /= getm_ptr2 /= get_rv2 /=.
      rewrite flows_join; case: ifP=> //= /andP [lo_lptr2 lo_rl2].
      match_upd mem1.
        rewrite /indist /= !flows_join h_pc !andbT.
        rewrite -sum_eqE /= -andb_orr; apply/implyP=> /andP [lo_lptr_rs lo_lv_rs].
        by move/implyP/(_ lo_lv_rs)/eqP: ind_v => [-> ->].
      case=> mem2' [upd2 ind_m'].
      by rewrite upd2 /= implybT; split; constructor.
    (* Both pointers are high *)
    move=> get_rptr1 get_rptr2.
    case getm_ptr1: (mem1 ptr1)=> [[|[vold1 lvold1]]|] //=.
    rewrite flows_join; case: ifP=> //= /andP [lo_lptr1 lo_rl1].
    case upd1: updm=> [mem1'|] //= [<- <-] {st1' oe1}.
    rewrite -lock /= get_pc2 /= get_rptr2 /= get_rv2 /=.
    case getm_ptr2: (mem2 ptr2)=> [[|[vold2 lvold2]]|] //=.
    rewrite flows_join; case: ifP=> //= /andP [lo_lptr2 lo_rl2].
    rewrite /updm getm_ptr2 /= implybT; split; constructor=> // x /=.
    rewrite (updm_set upd1) !setmE; move: (ind_m x) {upd1}.
    have [-> {x}|] := altP (x =P ptr1).
      have [_ {ptr2 getm_ptr2 get_rptr2}|_] := altP (ptr1 =P ptr2).
        rewrite /indist /= -sum_eqE /= !flows_join.
        by rewrite (negbTE hi1) (negbTE hi2) /=.
      rewrite getm_ptr1.
      move: ptr1 lptr1 hi1 get_rptr1 lo_lptr1 getm_ptr1
            {ptr2 lptr2 hi2 get_rptr2 getm_ptr2 vold2 lvold2 lo_lptr2 lo_rl2}
            => ptr lptr hi1 get_rptr1 lo_lptr1 getm_ptr1.
      case getm_ptr2: (mem2 ptr)=> [[|[vold2 lvold2]]|] //=.
        by rewrite /indist /= botP orbT -sum_eqE /=.
      rewrite /indist /= !flows_join -sum_eqE /=.
      rewrite (negbTE hi1) /= => ind_vold; apply/implyP=> lo_lvold2.
      move: ind_vold getm_ptr2.
      rewrite lo_lvold2 orbT /=  => /eqP [evold elvold].
      move: evold elvold lo_lvold2 => <- <- {vold2 lvold2} lo_lvold.
      by move: hi1; rewrite (flows_trans lo_lptr1 lo_lvold).
    have [-> {x} _|//] := altP (x =P ptr2).
    rewrite getm_ptr2 => {ptr1 lptr1 vold1 lvold1 hi1 lo_lptr1 lo_rl1 get_rptr1 getm_ptr1}.
    case getm_ptr1: (mem1 ptr2) => [vold|] //=.
    rewrite /indist -sum_eqE; case vold=> [i|[vold1 lvold1]] //=.
      by rewrite botP.
    rewrite !flows_join /= (negbTE hi2) /= orbF.
    case: (boolP (lvold1 ⊑ rs))=> //= ind_vold /eqP [ev el].
    by subst lvold2; rewrite (flows_trans lo_lptr2 ind_vold) in hi2.
  - (* Jump *)
    move=> r get_pc1 get_pc2.
    move: (ind_r r).
    case get_r1: (reg1 r) => [[v1 l1]|] //=.
    case get_r2: (reg2 r) => [[v2 l2]|] //= ind_v [<- <-] {st1' oe1}.
    rewrite -lock /= get_pc2 get_r2 /= implybT; split=> //.
    case/indistP: ind_v=> /= [lo1 lo2 [<- <-]|hi1 hi2].
      constructor=> //=.
      by rewrite flows_join lo1.
    apply: SIndistHigh=> //=;
    try by rewrite flows_join negb_and ?hi1 ?hi2.
    by apply: indist_stacks_strengthen.
  - (* Bnz *)
    move=> r i get_pc1 get_pc2.
    move: (ind_r r).
    case get_r1: (reg1 r) => [[v1 l1]|] //=.
    case get_r2: (reg2 r) => [[v2 l2]|] //= ind_v [<- <-] {st1' oe1}.
    rewrite -lock /= get_pc2 get_r2 /= implybT; split=> //.
    case/indistP: ind_v=> /= [lo1 lo2 [<- <-]|hi1 hi2].
      constructor=> //=.
      by rewrite flows_join lo1.
    apply: SIndistHigh=> //=;
    try by rewrite flows_join negb_and ?hi1 ?hi2.
    by apply: indist_stacks_strengthen.
  (* Jal *)
  move=> r get_pc1 get_pc2.
  move: (ind_r r).
  case get_r1: (reg1 r) => [[v1 l1]|] //=.
  case get_r2: (reg2 r) => [[v2 l2]|] //= ind_v.
  case upd1: updm => [reg1'|] //= [<- <-] {st1' oe1}.
  rewrite -lock /= get_pc2 get_r2 /=.
  match_upd reg1.
    rewrite /indist /= !flows_join !h_pc !andbT.
    case/indistP: ind_v=> [-> -> [_ ->]//=|/= hi1 hi2].
      by rewrite -[X in X ==> _]negbK negb_or hi1 hi2.
  case=> reg2' [upd2 ind_r'].
  rewrite upd2 /= implybT; split=> //.
  case/indistP: ind_v upd1 upd2=> [/= lo1 lo2 [<- <-]|/= hi1 hi2] upd1 upd2.
    constructor=> //=.
    by rewrite flows_join lo1 /=.
  apply: SIndistHigh=> //=; try by rewrite flows_join negb_and ?hi1 ?hi2.
  by apply: indist_stacks_strengthen.
(* System services *)
move=> _.
case: ifP=> [/eqP pc_return|pc_n_return] //=.
  (* Return *)
  case: stk1 ind_stk=> [|cf1 stk1] //= ind_stk.
  move: (ind_r (@syscall_ret _ sregs)).
  case get_ret1: (reg1 syscall_ret) => [[r1 lr1]|] //=.
  case get_ret2: (reg2 syscall_ret) => [[r2 lr2]|] //= ind_ret.
  case upd_reg1: updm=> [reg1'|] //= [<- <-] {st1' oe1}.
  rewrite -lock /= get_pc2 pc_return eqxx.
  case: stk2 ind_stk => [|cf2 stk2] //= ind_stk.
  rewrite get_ret2 /=.
  move: ind_stk; rewrite /indist_stacks /=.
  case=> [[ind_pc' ind_regs] ind_stk].
  case/indistP: ind_pc' (*check2*) => [lo_pc _ <-|hi_pc1 hi_pc2] (*check2*).
    match_upd (cf_regs cf1)=> //=.
      move: ind_ret; rewrite /indist /= !flows_join !h_pc /=.
      by case: orb => //= /eqP [-> ->].
    case=> [reg2' [upd_reg2 ind_reg']].
    rewrite upd_reg2 /= implybT; split=> //.
    exact: SIndistLow.
  case upd_reg2: updm=> [reg2'|] //=.
  rewrite implybT; split=> //=.
  apply: SIndistHigh=> //=.
  by apply: indist_stacks_strengthen.
case: ifP=> [/eqP pc_call|pc_n_call] //=.
  (* Call *)
  move: (ind_r (@ra _ mops)).
  case get_ra1: (reg1 ra) => [[caller1 lcaller1]|] //=.
  case get_ra2: (reg2 ra) => [[caller2 lcaller2]|] //= ind_caller.
  move: (ind_r (@syscall_arg1 _ sregs)).
  case get_arg11: (reg1 syscall_arg1) => [[called1 lcalled1]|] //=.
  case get_arg12: (reg2 syscall_arg1) => [[called2 lcalled2]|] //= ind_called [<- <-] {st1' oe1}.
  rewrite -lock /= get_pc2 pc_n_return pc_call eqxx get_ra2 get_arg12 /=.
  split; last by rewrite implybT.
  case/indistP: ind_called => /=.
    move=> lo_calld _ [<- <-] {called2 lcalled2 get_arg12}.
    case/indistP: ind_caller => /=.
      move=> lo_callr _ [<- <-] {caller2 lcaller2 get_ra2}.
      apply: SIndistLow=> //=; first by rewrite !flows_join lo_calld lo_callr.
      rewrite /indist_stacks /=; split=> //; split=> //.
      exact: indist_refl.
    move=> hi_callr1 hi_callr2.
    apply: SIndistHigh=> //=;
    try rewrite !flows_join !negb_and ?hi_callr1 ?hi_callr2 orbT //.
    rewrite /indist_stacks /= !flows_join !negb_and hi_callr1 hi_callr2 /=.
    exact: (indist_stacks_strengthen ind_stk).
  move=> hi_calld1 hi_calld2.
  apply: SIndistHigh=> //=;
  try rewrite flows_join negb_and ?hi_calld1 ?hi_calld2 //.
  rewrite /indist_stacks /=.
  case/indistP: (ind_caller)=> //= [lo_callr _ [<- <-]|hi_callr1 hi_callr2].
    rewrite !flows_join negb_and lo_callr h_pc /=; split=> //.
    split=> //=.
    by rewrite indist_refl.
  rewrite !flows_join !negb_and hi_callr1 hi_callr2 /=.
  exact: (indist_stacks_strengthen ind_stk).
case: ifP => [/eqP pc_output|pc_n_output] //.
  (* Output *)
  move: (ind_r (@ra _ mops)).
  case get_ra1: (reg1 ra) => [[raddr1 lraddr1]|] //=.
  case get_ra2: (reg2 ra) => [[raddr2 lraddr2]|] //= ind_raddr.
  move: (ind_r (@syscall_arg1 _ sregs)).
  case get_arg11: (reg1 syscall_arg1) => [[out1 lout1]|] //=.
  case get_arg12: (reg2 syscall_arg1) => [[out2 lout2]|] //= ind_out [<- <-] {st1' oe1}.
  rewrite -lock /= get_pc2 pc_n_return pc_n_call pc_output eqxx get_ra2 get_arg12 /=.
  split.
    case/indistP: ind_raddr=> /= [lo_raddr _ [<- <-] {raddr2 lraddr2 get_ra2}|].
      constructor=> //=.
      by rewrite flows_join lo_raddr.
    move=> hi1 hi2.
    apply: SIndistHigh=> //=;
    try by rewrite flows_join negb_and (hi1, hi2).
    by apply: indist_stacks_strengthen.
  move: ind_raddr ind_out; rewrite /indist /= !flows_join h_pc /= => ind_raddr.
  by case: orb => //= /eqP [-> ->].
Qed.

Lemma high_high_step rs st1 st2 st1' oe1 :
  s_indist rs st1 st2 ->
  ~~ (taga (pc st1) ⊑ rs) ->
  ~~ (taga (pc st1') ⊑ rs) ->
  step st1 = Some (st1', oe1) ->
  s_indist rs st1' st2
  /\ if oe1 is Some o then ~~ (taga o ⊑ rs) else True.
Proof.
move=> h_indist h_low1 h_low1'; case: h_indist; first by rewrite (negbTE h_low1).
rewrite (lock step).
case: st1 {h_low1} => mem1 reg1 [pc1 rl1] stk1 /= h_rl1.
case: st2=> mem2 reg2 [pc2 rl2] stk2 /= h_rl2 ind_m ind_stk ev.
move: ev h_low1'; rewrite -lock /=.
case get_pc1: (mem1 pc1) => [[i1|a1]|] //=; rewrite /indist ?botP //=.
  (* Instructions *)
  case: i1 get_pc1=> //=.
  - (* Nop *)
    move=> get_pc1 [<- <-] {st1' oe1} /= _.
    by split=> //; apply: SIndistHigh.
  - (* Const *)
    move=> k r get_pc1.
    case upd1: updm=> [reg1'|] //= [<- <-] {st1' oe1} _.
    by split=> //; apply: SIndistHigh.
  - (* Mov *)
    move=> r1 r2 get_pc1.
    case get1: (reg1 r1) => [v1|] //=.
    case upd1: (updm reg1) => [reg1'|] //= [<- <-] {st1' oe1} _.
    by split=> //; apply: SIndistHigh.
  - (* Binop *)
    move=> b r1 r2 r3 get_pc1.
    case get11: (reg1 r1) => [[v11 l11]|] //=.
    case get21: (reg1 r2) => [[v21 l21]|] //=.
    case upd1: updm=> [reg1'|] //= [<- <-] {st1' oe1} _.
    by split=> //; apply: SIndistHigh.
  - (* Load *)
    move=> r1 r2 get_pc1.
    case get_r1: (reg1 r1) => [[v1 l1]|] //=.
    case get_m1: (mem1 v1) => [[|[v1' l1']]|] //=.
    case upd1: updm => [reg1'|] //= [<- <-] {st1' oe1} _.
    by split; first apply: SIndistHigh.
  - (* Store *)
    move=> rptr rv get_pc1.
    case get_rptr1: (reg1 rptr) => [[ptr1 lptr1]|] //=.
    case get_rv1: (reg1 rv) => [[v1 lv1]|] //=.
    case getm_ptr1: (mem1 ptr1)=> [[|[vold1 lvold1]]|] //=.
    case: ifP=> //= check1.
    case upd1: updm => [mem1'|] //= [<- <-] {st1' oe1} _.
    split; [apply: SIndistHigh|]=> //=.
    move=> ptr; move: (ind_m ptr).
    rewrite (getm_upd upd1).
    have [-> {ptr}|//] := ptr =P ptr1.
    rewrite getm_ptr1.
    case getm_ptr2: (mem2 ptr1) => [[|[vold2 lvold2]]|]; rewrite /indist //=.
      by rewrite botP orbT.
    rewrite !flows_join (negbTE h_rl1) !andbF /=.
    have [low_old|] //= := boolP (lvold2 ⊑ rs).
    rewrite orbT /= => /eqP [e1 e2].
    rewrite -{}e2 in low_old.
    move: (flows_trans check1 low_old).
    by rewrite flows_join (negbTE h_rl1) andbF.
  - (* Jump *)
    move=> r get_pc1.
    case get_r1: (reg1 r) => [[v1 l1]|] //= [<- <-] {st1' oe1} _.
    split; [apply: SIndistHigh|]=> //=.
    by rewrite flows_join negb_and (negbTE h_rl1) orbT.
  - (* Bnz *)
    move=> r i get_pc1.
    case get_r1: (reg1 r) => [[v1 l1]|] //= [<- <-] {st1' oe1} _.
    split; [apply: SIndistHigh|]=> //=.
    by rewrite flows_join negb_and (negbTE h_rl1) orbT.
  (* Jal *)
  move=> r get_pc1.
  case get_r1: (reg1 r) => [[v1 l1]|] //=.
  case upd1: updm=> [reg1'|] //= [<- <-] {st1' oe1} _.
  split; [apply: SIndistHigh|]=> //=.
  by rewrite flows_join negb_and (negbTE h_rl1) orbT.
(* System services *)
case: ifP=> [/eqP pc_return|pc_n_return] //=.
  (* Return *)
  case: stk1 ind_stk=> [|cf1 stk1] //= ind_stk.
  case get_ret1: (reg1 syscall_ret) => [[r1 lr1]|] //=.
  case upd_reg1: updm=> [reg1'|] //= [<- <-] {st1' oe1} /= h_rl1'.
  split; [apply: SIndistHigh|]=> //=.
  by move: ind_stk; rewrite /indist_stacks /= h_rl1'.
case: ifP=> [/eqP pc_call|pc_n_call] //=.
  (* Call *)
  case get_ra1: (reg1 ra) => [[caller1 lcaller1]|] //=.
  case get_arg11: (reg1 syscall_arg1) => [[called1 lcalled1]|] //= [<- <-] {st1' oe1}.
  move=> /= h_call.
  split; [apply: SIndistHigh|]=> //=.
  by rewrite /indist_stacks /= !flows_join !negb_and h_rl1 orbT.
case: ifP => [/eqP pc_output|pc_n_output] //.
  (* Output *)
  case get_ra1: (reg1 ra) => [[raddr1 lraddr1]|] //=.
  case get_arg11: (reg1 syscall_arg1) => [[out1 lout1]|] //= [<- <-] {st1' oe1}.
  move=> /= h_rl1'.
  rewrite flows_join negb_and h_rl1.
  by split; first apply: SIndistHigh.
Qed.

Ltac high_low_contradiction :=
  match_inv;
  repeat match goal with
  | low : is_true (_ ⊑ _) |- _ =>
    rewrite /= ?flows_join in low
  end;
  repeat match goal with
  | low : is_true (_ && _) |- _ =>
    case/andP: low => ??
  end;
  try match goal with
  | hi : is_true (~~ ?b), low : is_true ?b |- _ =>
    rewrite low in hi
  end.

Lemma high_low_is_return rs st st' oe :
  ~~ (taga (pc st) ⊑ rs) ->
  taga (pc st') ⊑ rs ->
  step st = Some (st', oe) ->
  [/\ vala (pc st) = return_addr ,
      mem st (vala (pc st)) = None &
      oe = None].
Proof.
case: st=> mem reg [pc rl] stk /= hi low.
case get_pc: (mem pc) => [[i|a]|] //=; rewrite /indist ?botP //=.
  (* Instructions *)
  by move=> ?; high_low_contradiction.
(* System services *)
move=> ?; high_low_contradiction=> //.
by split=> //; apply/eqP.
Qed.

Lemma high_low_step rs st1 st2 st1' st2' oe1 oe2 :
  s_indist rs st1 st2 ->
  ~~ (taga (pc st1) ⊑ rs) ->
  taga (pc st1') ⊑ rs ->
  step st1 = Some (st1', oe1) ->
  taga (pc st2') ⊑ rs ->
  step st2 = Some (st2', oe2) ->
  [/\ s_indist rs st1' st2',
      oe1 = None & oe2 = None].
Proof.
move=> ind hi1 lo1 step1 lo2 step2.
case: ind; first by rewrite (negbTE hi1).
move=> _ hi2.
case: (high_low_is_return hi1 lo1 step1) => e_pc1 get_pc1 _.
case: (high_low_is_return hi2 lo2 step2) => e_pc2 get_pc2 _.
case: st1 hi1 e_pc1 get_pc1 step1=> mem1 reg1 [pc1 rl1] stk1 /= h_rl1 -> ->.
rewrite eqxx => step1.
case: st2 hi2 e_pc2 get_pc2 step2=> mem2 reg2 [pc2 rl2] stk2 /= h_rl2 -> ->.
rewrite eqxx => step2 ind_m.
case: stk1 stk2 step1 step2 lo1 lo2
       => [|[[r1 lr1] reg1'] stk1] [|[[r2 lr2] reg2'] stk2] //=.
case get_ret1: (reg1 syscall_ret) => [[v1 l1]|] //=.
case get_ret2: (reg2 syscall_ret) => [[v2 l2]|] //=.
case upd1: updm=> [reg1''|] //= [<- <-] {st1' oe1}.
case upd2: updm=> [reg2''|] //= [<- <-] {st2' oe2} //= lo1 lo2.
rewrite /indist_stacks /= lo1 lo2 /=.
case=> [[/=]].
rewrite {1 2}/indist /= lo1 /=.
move=> /eqP [er elr].
move: r1 lr1 er elr lo1 {lo2}=> r lr <- <- lo.
move=> ind_reg ind_stk.
split=> //; apply: SIndistLow=> //=.
apply: refine_upd_pointwise2 upd1 upd2=> //.
by rewrite /indist /= !flows_join (negbTE h_rl1) (negbTE h_rl2).
Qed.

Theorem noninterference rs st1 st2 n1 n2 :
  s_indist rs st1 st2 ->
  indist_seq_prefix eq
                    [seq x <- trace n1 st1 | taga x ⊑ rs]
                    [seq x <- trace n2 st2 | taga x ⊑ rs].
Proof.
move: {2}(n1 + n2) (leqnn (n1 + n2)) => n en.
elim: n st1 st2 n1 n2 en => [|n IH] st1 st2 n1 n2.
  rewrite leqn0 addn_eq0.
  by case/andP=> [/eqP -> /eqP ->].
case: n1=> [//=|n1].
case step1: (step st1) => [[st1' oe1]|]; last by rewrite /= step1.
case: n2=> [|n2]; first by case: filter.
case step2: (step st2) => [[st2' oe2]|]; last first.
  by rewrite /= step2; case: filter.
have [lo1|hi1] := boolP (taga (pc st1) ⊑ rs).
  move=> /= en ind.
  move: (low_step ind lo1 step1); rewrite step1 step2.
  case=> [ind' ind_oe].
  rewrite !filter_cat.
  apply: indist_seq_cat_prefix=> //.
    case: oe1 oe2 ind_oe {step1 step2} => [o1|] [o2|] //=;
    rewrite /indist ?botP ?orbT //=.
    have [check|check]:= boolP (_ || _).
      move=> /eqP [eo].
      move: o1 eo check => o <- {o2}.
      rewrite orbb => check.
      by case: ifP.
    by move: check; rewrite negb_or => /andP [/negbTE -> /negbTE ->].
  apply: IH=> //.
  move: en; rewrite addSn ltnS; apply: leq_trans.
  by rewrite addnS leqnSn.
have [lo1'|hi1'] := boolP (taga (pc st1') ⊑ rs).
  have [lo2'|hi2'] := boolP (taga (pc st2') ⊑ rs).
    move=> en ind /=; rewrite step1 step2.
    case: (high_low_step ind hi1 lo1' step1 lo2' step2)
          => {step1 step2} [ind' -> ->] //=.
    apply: IH=> //.
    move: en; rewrite addSn ltnS; apply: leq_trans.
    by rewrite addnS leqnSn.
  move=> en ind.
  have hi2: ~~ (taga (pc st2) ⊑ rs).
    by case: ind; first rewrite (negbTE hi1).
  move/s_indist_sym in ind.
  move: (high_high_step ind hi2 hi2' step2).
  rewrite {1}(lock trace) /= step2.
  case: oe2 {step2} => [o|] //=.
    case=> [ind' /negbTE ->].
    apply/indist_seq_prefix_sym=> //.
    rewrite -lock; apply: IH=> //.
    by move: en; rewrite addnC addSn ltnS.
  case=> [ind' _].
  apply/indist_seq_prefix_sym=> //.
  rewrite -lock; apply: IH=> //.
  by move: en; rewrite addnC addSn ltnS.
move=> en ind.
move: (high_high_step ind hi1 hi1' step1).
rewrite {2}(lock trace) /= step1.
case: oe1 {step1} => [o|] //=.
  case=> [ind' /negbTE ->].
  by rewrite -lock; apply: IH=> //.
case=> [ind' _].
by rewrite -lock; apply: IH=> //.
Qed.

End Noninterference.
