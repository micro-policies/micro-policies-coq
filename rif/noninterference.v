From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype finfun.
From CoqUtils Require Import hseq ord fset partmap word.
From MicroPolicies Require Import
  lib.utils lib.partmap_utils common.types rif.labels rif.abstract.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Indist.

Context {T : eqType} {L : labType}.
Variable t : T -> L.

Local Open Scope label_scope.

Definition indist rs (ra1 ra2 : T) :=
  (t ra1 ⊑ rs) || (t ra2 ⊑ rs) ==> (ra1 == ra2).

CoInductive indist_spec rs ra1 ra2 : Prop :=
| IndistLow of t ra1 ⊑ rs & t ra2 ⊑ rs & ra1 = ra2
| IndistHigh of ~~ (t ra1 ⊑ rs) & ~~ (t ra2 ⊑ rs).

Lemma indistP rs ra1 ra2 :
  reflect (indist_spec rs ra1 ra2) (indist rs ra1 ra2).
Proof.
rewrite /indist; apply/(iffP idP).
  have [hi /eqP <-|lo1] /= := boolP (t ra1 ⊑ rs); first by constructor.
  have [hi /eqP e|lo2 _] /= := boolP (t ra2 ⊑ rs).
    by rewrite e hi in lo1.
  by apply: IndistHigh.
case=> [-> -> -> //=|hi1 hi2].
by rewrite -[X in X ==> _]negbK negb_or hi1 hi2.
Qed.

Lemma indist_refl rl : reflexive (indist rl).
Proof. by move=> ra; rewrite /indist eqxx implybT. Qed.

Lemma indist_sym rl : symmetric (indist rl).
Proof. by move=> ra1 ra2; rewrite /indist orbC eq_sym. Qed.

Lemma indist_trans rl : transitive (indist rl).
Proof.
move=> ra2 ra1 ra3; rewrite /indist => e1 e2.
apply/implyP=> /orP [e|e].
  by move: e1 e2; rewrite e /= => /eqP <-; rewrite e => /eqP ->.
by move: e2 e1; rewrite e orbT /= => /eqP ->; rewrite e orbT /= => /eqP ->.
Qed.

End Indist.

Section Noninterference.

Import DoNotation.

Local Open Scope label_scope.

Variable L : labType.
Variable mt : machine_types.
Variable mops : machine_ops mt.

Local Notation word := (mword mt).
Local Notation atom := (atom word L).
Local Notation state := (state L mt).
Local Notation step := (@step L mt mops).
Local Notation stepn := (@stepn L mt mops).

Implicit Type st : state.

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
| SIndistHigh of ~~ (taga (pc st1) ⊑ rs)
              &  ~~ (taga (pc st2) ⊑ rs).

Ltac match_upd t1 :=
  match goal with
  | ind : pointwise ?P t1 ?t2,
    upd : updm t1 ?x ?v1 = Some ?t1'
    |- context[updm ?t2 ?x ?v2] =>
    have: P v1 v2; last move=> /(refine_upd_pointwiseL ind upd)
  end.

Lemma low_step rs st1 st2 st1' :
  s_indist rs st1 st2 ->
  taga (pc st1) ⊑ rs ->
  step st1 = Some st1' ->
  match step st2 with
  | Some st2' => s_indist rs st1' st2'
  | None => True
  end.
Proof.
move=> h_indist h_low1; case: h_indist; last by rewrite h_low1.
rewrite (lock step).
case: st1 {h_low1} => mem1 reg1 [pc1 rl1] /=.
case: st2=> mem2 reg2 [pc2 rl2] /= h_pc e.
move: pc1 rl1 e h_pc => pc rl [<- <-] h_pc {pc2 rl2} ind_r ind_m.
rewrite -{1}lock /=.
move: (ind_m pc).
case get_pc1: (mem1 pc) => [[i1|a1]|] //=;
case get_pc2: (mem2 pc) => [[i2|a2]|] //=;
rewrite /indist /=.
  (* Instructions *)
  rewrite !botP /=.
  move=> e; move: i1 e get_pc1 get_pc2 => i /eqP [<-] {i2}.
  case: i=> //=.
  - (* Nop *)
    move=> get_pc1 get_pc2 [<-] {st1'}.
    by rewrite -lock /= get_pc2; constructor.
  - (* Const *)
    move=> k r get_pc1 get_pc2.
    case upd1: updm=> [reg1'|] //= [<-] {st1'}.
    rewrite -lock /= get_pc2.
    match_upd reg1; first exact: indist_refl.
    case=> reg2' [upd2 ind_r'].
    by rewrite upd2 /=; constructor.
  - (* Mov *)
    move=> r1 r2 get_pc1 get_pc2.
    move: (ind_r r1).
    case get1: (reg1 r1) => [v1|] //=.
    case get2: (reg2 r1) => [v2|] //= ind_v.
    case upd1: (updm reg1) => [reg1'|] //= [<-] {st1'}.
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
    case upd1: updm=> [reg1'|] //= [<-] {st1'}.
    rewrite -lock /= get_pc2 get12 get22 /=.
    match_upd reg1=> //=.
      move: ind_v1 ind_v2; rewrite /indist /= !flows_join.
      by repeat match goal with
      | |- context[_ ⊑ _] => case: flows=> //=
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
        by rewrite {1}/indist botP orbT implybF.
      move=> ind_v.
      case upd1: updm => [reg1'|] //= [<-] {st1'}.
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
      rewrite upd2 /=.
      by constructor.
    (* Both pointers are high *)
    move=> get_r1 get_r2.
    case getm_v1: (mem1 v1)=> [[|[v1' l1']]|] //=.
    case upd1: updm => [reg1'|] //= [<-] {st1'}.
    rewrite -lock /= get_pc2 get_r2 /=.
    case getm_v2: (mem2 v2)=> [[|[v2' l2']]|] //=.
    match_upd reg1.
      rewrite /indist /= !flows_join.
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
        by rewrite {1}/indist botP orbT -sum_eqE.
      rewrite {1}/indist /= -sum_eqE /=.
      rewrite flows_join; case: ifP=> //= /andP [lo_lptr1 lo_rl1].
      case upd1: updm=> [mem1'|] //= ind_vold [<-] {st1'}.
      rewrite -lock /= get_pc2 get_rptr2 /= getm_ptr2 /= get_rv2 /=.
      rewrite flows_join; case: ifP=> //= /andP [lo_lptr2 lo_rl2].
      match_upd mem1.
        rewrite /indist /= !flows_join h_pc !andbT.
        rewrite -sum_eqE /= -andb_orr; apply/implyP=> /andP [lo_lptr_rs lo_lv_rs].
        by move/implyP/(_ lo_lv_rs)/eqP: ind_v => [-> ->].
      by case=> mem2' [upd2 ind_m']; rewrite upd2 /=; constructor.
    (* Both pointers are high *)
    move=> get_rptr1 get_rptr2.
    case getm_ptr1: (mem1 ptr1)=> [[|[vold1 lvold1]]|] //=.
    rewrite flows_join; case: ifP=> //= /andP [lo_lptr1 lo_rl1].
    case upd1: updm=> [mem1'|] //= [<-] {st1'}.
    rewrite -lock /= get_pc2 /= get_rptr2 /= get_rv2 /=.
    case getm_ptr2: (mem2 ptr2)=> [[|[vold2 lvold2]]|] //=.
    rewrite flows_join; case: ifP=> //= /andP [lo_lptr2 lo_rl2].
    rewrite /updm getm_ptr2 /=; constructor=> // x /=.
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
    case get_r2: (reg2 r) => [[v2 l2]|] //= ind_v [<-] {st1'}.
    rewrite -lock /= get_pc2 get_r2 /=.
    case/indistP: ind_v=> /= [lo1 lo2 [<- <-]|hi1 hi2].
      constructor=> //=.
      by rewrite flows_join lo1.
    by apply: SIndistHigh=> //=;
    rewrite flows_join negb_and ?hi1 ?hi2.
  - (* Bnz *)
    move=> r i get_pc1 get_pc2.
    move: (ind_r r).
    case get_r1: (reg1 r) => [[v1 l1]|] //=.
    case get_r2: (reg2 r) => [[v2 l2]|] //= ind_v [<-] {st1'}.
    rewrite -lock /= get_pc2 get_r2 /=.
    case/indistP: ind_v=> /= [lo1 lo2 [<- <-]|hi1 hi2].
      constructor=> //=.
      by rewrite flows_join lo1.
    by apply: SIndistHigh=> //=;
    rewrite flows_join negb_and ?hi1 ?hi2.
  (* Jal *)
  move=> r get_pc1 get_pc2.
  move: (ind_r r).
  case get_r1: (reg1 r) => [[v1 l1]|] //=.
  case get_r2: (reg2 r) => [[v2 l2]|] //= ind_v.
  case upd1: updm => [reg1'|] //= [<-] {st1'}.
  rewrite -lock /= get_pc2 get_r2 /=.
  match_upd reg1.
    rewrite /indist /= !flows_join !h_pc !andbT.
    case/indistP: ind_v=> [-> -> [_ ->]//=|/= hi1 hi2].
      by rewrite -[X in X ==> _]negbK negb_or hi1 hi2.
  case=> reg2' [upd2 ind_r'].
  rewrite upd2 /=.
  case/indistP: ind_v upd1 upd2=> [/= lo1 lo2 [<- <-]|/= hi1 hi2] upd1 upd2.
    constructor=> //=.
    by rewrite flows_join lo1 /=.
  by apply: SIndistHigh=> //=;
  rewrite flows_join negb_and ?hi1 ?hi2.
(* System services; none for now *)
by rewrite botP.
Qed.

End Noninterference.
