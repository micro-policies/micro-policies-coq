Ltac type_of x := type of x.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
Require Import ssrint ssralg.
Require Import ord word partmap.
Require Import lib.utils lib.partmap_utils common.common symbolic.symbolic.
Require Import memory_safety.abstract memory_safety.symbolic.
Require Import memory_safety.classes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Extending the default ssr done tactic with eassumption *)
Ltac done :=
  trivial; hnf; intros; solve
   [ do ![solve [trivial | apply: sym_equal; trivial]
         | discriminate | contradiction | split | eassumption]
   | case not_locked_false_eq_true; assumption
   | match goal with H : ~ _ |- _ => solve [case H; trivial] end ].

Section refinement.

Open Scope word_scope.

Import Sym.Notations.

Variable block : ordType.

Context {mt : machine_types}
        {cl : Sym.color_class}
        {ops : machine_ops mt}

        {opss : machine_ops_spec ops}.

Context `{syscall_regs mt} `{a_alloc : @Abstract.allocator mt block}
         {a_allocP : Abstract.allocator_spec a_alloc}
        `{@memory_syscall_addrs mt}.

Definition meminj := {partmap Sym.color -> block * mword mt (* base *)}.

Lemma binop_addDl : forall x y z : mword mt,
  binop_denote ADD (x + y) z = x + (binop_denote ADD y z).
Proof. by move => x y z /=; by rewrite addwA. Qed.

Lemma binop_addDr : forall x y z : mword mt,
  binop_denote ADD x (y + z) = y + (binop_denote ADD x z).
Proof.
move => x y z /=.
by rewrite addwA (addwC x) addwA.
Qed.

Lemma binop_subDl : forall x y z : mword mt,
  binop_denote SUB (x + y) z = x + (binop_denote SUB y z).
Proof.
move => x y z /=.
by rewrite !/subw addwA.
Qed.

Lemma binop_sub_add2l : forall x y z : mword mt,
  binop_denote SUB (x + y) (x + z) = (binop_denote SUB y z).
Proof.
move => x y z /=.
rewrite /subw -[- (x + z)]/(- (x + z))%R GRing.opprD addwA.
rewrite (addwC (x + y)) [x + y]/(x + y)%R /=; congr addw.
exact: GRing.addKr.
Qed.

Lemma binop_eq_add2l : forall x y z : mword mt,
  binop_denote EQ (x + y) (x + z) = binop_denote EQ y z.
Proof.
move => x y z /=; congr bool_to_word.
rewrite inj_eq //; exact: GRing.addrI.
Qed.

Lemma leZ_min (w : mword mt) : 0 <= w.
Proof. by []. Qed.

Lemma leZ_max (w : mword mt) : w < 2 ^ word_size mt.
Proof. exact: (valP (w : ordinal _)). Qed.

(* How to make w explicit ??? *)
(* TODO: File a bug report *)
Arguments leZ_min.
Arguments leZ_max.

Notation inbounds base size w :=
  (base <= w < base + size).

Section memory_injections.

Record meminj_spec (amem : Abstract.memory mt block) (mi : meminj) := {
    miIr : forall b col col' base base',
                mi col = Some (b, base) ->
                mi col' = Some (b, base') ->
                col = col'
  }.

(* We could generalize updv to any size-preserving operator *)
Lemma meminj_update mi amem amem' ptr x :
  meminj_spec amem mi ->
  Abstract.updv amem ptr x = Some amem' ->
  meminj_spec amem' mi.
Proof.
move=> miP upd_b.
constructor; first exact: miIr miP.
Qed.

Hint Resolve meminj_update.

Variable amem : Abstract.memory mt block.
Variable mi : meminj.

Definition ohrel (A B : Type) (rAB : A -> B -> Prop) sa sb : Prop :=
  match sa, sb with
    | None,   None   => True
    | Some a, Some b => rAB a b
    | _,      _      => False
  end.

Inductive refine_val : Abstract.value mt block -> mword mt -> Sym.type -> Prop :=
  | RefineData : forall w, refine_val (Abstract.VData _ w) w DATA
  | RefinePtr : forall b base col off, mi col = Some (b,base) ->
                refine_val (Abstract.VPtr (b,off)) (base + off) (PTR col).

Lemma refine_ptr_inv w col b b' off base :
  meminj_spec amem mi ->
  refine_val (Abstract.VPtr (b,off)) w (PTR col) ->
  mi col = Some (b', base) ->
  w = (base + off)%w.
Proof.
move=> miP rpt mi_b.
inversion rpt.
congruence.
Qed.

Definition refine_memory amem (smem : Sym.memory mt) :=
  meminj_spec amem mi /\ forall w1 w2 col ty,
  smem w1 = Some w2@M(col,ty) ->
  if mi col is Some (b,base) then
  if Abstract.getv amem (b, w1 - base) is Some v then
  refine_val v w2 ty else False else False.

Lemma refine_memory_get_int qamem (w1 w2 : mword mt) col pt :
         refine_memory amem qamem -> refine_val (Abstract.VPtr pt) w1 (PTR col) ->
         qamem w1 = Some w2@M(col,DATA) ->
         Abstract.getv amem pt = Some (Abstract.VData _ w2).
Proof.
move=> [miP rmem] rpt get_w1.
move/(_ _ _ _ _ get_w1): rmem.
inversion rpt.
rewrite H4 (addwC base).
rewrite (_ : off + base - base = off); try exact: GRing.addrK.
case: (Abstract.getv amem (b, off)) => // v rvw3.
by inversion rvw3.
Qed.

Lemma getv_mem base off v : Abstract.getv amem (base, off) = Some v ->
  exists fr, amem base = Some fr
  /\ nth (Abstract.VData block 0) fr (ord_of_word off) = v.
Proof.
unfold Abstract.getv; simpl.
destruct (amem base) as [fr|]; try discriminate.
by case: (_ < _) => // - [<-]; eauto.
Qed.

Lemma get_mem_memv base off v fr : amem base = Some fr ->
  nth (Abstract.VData block 0) fr (ord_of_word off) = v ->
  ord_of_word off < size fr ->
  Abstract.getv amem (base,off) = Some v.
Proof.
intros get_base index_off bound.
unfold Abstract.getv.
by rewrite /= get_base bound index_off.
Qed.

Lemma refine_memory_get smem (w1 w2 : mword mt) col pt ty :
         refine_memory amem smem -> refine_val (Abstract.VPtr pt) w1 (PTR col) ->
         smem w1 = Some (w2@M(col,ty)) ->
         exists2 x,
           Abstract.getv amem pt = Some x &
           refine_val x w2 ty.
Proof.
move=> [miP rmem] rpt get_w1.
move/(_ _ _ _ _ get_w1): rmem.
inversion rpt.
rewrite H4 (addwC base).
rewrite (_ : off + base - base = off); last exact: GRing.addrK.
rewrite /Abstract.getv.
case: (amem b) => //= get_off.
by case: (_ < _) => //; eauto.
Qed.

Definition bounded_add (w1 w2 : mword mt) :=
  0 < w2 /\ w1 + w2 < 2 ^ word_size mt.

Inductive block_info_spec (smem : Sym.memory mt) (bi : Sym.block_info mt) : Prop :=
| BlockInfoLive : forall col b, Sym.block_color bi = Some col ->
  bounded_add (Sym.block_base bi) (Sym.block_size bi) ->
  mi col = Some (b, Sym.block_base bi) ->
  (forall off : mword mt, off < Sym.block_size bi ->
     exists v ty, smem (Sym.block_base bi + off) = Some v@M(col,ty)) ->
  block_info_spec smem bi
| BlockInfoFree :
  Sym.block_color bi = None ->
  bounded_add (Sym.block_base bi) (Sym.block_size bi) ->
  (forall off : mword mt, off < Sym.block_size bi ->
    exists v, smem (Sym.block_base bi + off) = Some v@FREE) ->
  block_info_spec smem bi.

Lemma block_info_bounds smem bi :
  block_info_spec smem bi ->
  bounded_add (Sym.block_base bi) (Sym.block_size bi).
Proof.
by case.
Qed.

(* TODO: export from Sym in symbolic.v *)
Canonical Sym.block_info_eqType.

Definition fresh_color col :=
  forall col' b base, mi col' = Some (b,base) ->
  (col' < col)%ord.

Definition overlap (bi1 bi2 : Sym.block_info mt) (w : mword mt) :=
  inbounds (Sym.block_base bi1) (Sym.block_size bi1) w /\
  inbounds (Sym.block_base bi2) (Sym.block_size bi2) w.

Definition cover (smem : Sym.memory mt) (info : list (Sym.block_info mt)) :=
  forall w v, smem w = Some v ->
  exists bi, bi \in info /\ inbounds (Sym.block_base bi) (Sym.block_size bi) w.

Definition refine_internal_state (bl : list block) smem (ist : Sym.color * list (Sym.block_info mt)) :=
  let: (col, info) := ist in
  fresh_color col /\
  (forall col b base, mi col = Some (b,base) -> b \in bl) /\
  (forall i j def w, i < size info -> j < size info ->
     overlap (nth def info i) (nth def info j) w -> i = j)%N /\
  cover smem info /\
  forall bi, bi \in info -> block_info_spec smem bi.

Lemma refine_memory_upd bl smem smem' ist old
                        w1 w2 pt ty ty' n x :
  refine_memory amem smem ->
  refine_internal_state bl smem ist ->
  refine_val (Abstract.VPtr pt) w1 (PTR n) ->
  smem w1 = Some old@M(n, ty') ->
  updm smem w1 w2@M(n, ty) = Some smem' ->
  refine_val x w2 ty ->
    exists amem',
      [/\ Abstract.updv amem pt x = Some amem',
          refine_memory amem' smem' &
          refine_internal_state bl smem' ist].
Proof.
case: ist => nextcol info.
move=> [miP rmem] [freshcol [in_bl [no_overlap [cover_info rist]]]] rpt get_w1 upd_w1.
move=> rx.
have [base hn hw1]: exists2 base,
                    mi n = Some (pt.1, base) &
                    w1 = base + pt.2.
  by inversion rpt; subst; simpl; eauto.
subst w1.
move: (rmem _ _ _ _ get_w1); rewrite hn addwC.
have -> : pt.2 + base - base = pt.2 by exact: GRing.addrK.
rewrite -surjective_pairing.
rewrite /Abstract.updv /Abstract.getv.
case get_pt: (amem pt.1) => [fr|//].
have [gt_pt rold|//] := boolP (pt.2 < _).
eexists; split; first by []; do!split=> //.
- exact: miIr miP.
- move=> w1' x' n' tx'; rewrite (getm_upd upd_w1).
  have [{w1' x' n' tx'}-> [<- <- <-]|neq_w1'] := altP (_ =P _).
    rewrite hn /Abstract.getv.
    have -> /=: base + pt.2 - base = pt.2.
      rewrite addwC; exact: GRing.addrK.
    rewrite getm_set eqxx size_cat /= size_take size_drop gt_pt.
    rewrite addnS -addSn addnC subnK // gt_pt.
    by rewrite nth_cat size_take gt_pt ltnn subnn /=.
  have [{n'}-> /rmem|neq_n] := altP (n' =P n).
    rewrite hn.
    have {neq_w1'} : w1' - base != pt.2.
      apply: contra neq_w1'=> /eqP <-.
      rewrite addwC; apply/eqP/esym.
      exact: GRing.subrK.
    move: {w1'}(w1' - base) => w1' neq_w1'.
    rewrite /Abstract.getv /= get_pt getm_set eqxx.
    rewrite size_cat size_take /= size_drop gt_pt.
    rewrite addnS -addSn addnC subnK //.
    have [lt_w1'|//] := boolP (w1' < _).
    rewrite nth_cat size_take gt_pt.
    case: (ltngtP w1' pt.2)=> [gt_w1'|gt_w1'|/val_inj/val_inj eq_w1'] /=.
    + by rewrite nth_take.
    + have -> /=: (w1' - pt.2)%N = (w1' - pt.2.+1).+1.
        by rewrite subnS prednK // ltn_subRL addn0.
      by rewrite nth_drop addnC subnK.
    by rewrite eq_w1' eqxx in neq_w1'.
  move/rmem; case hn': (mi n') => [[b base']|//].
  rewrite /Abstract.getv (lock subw) /= -lock getm_set.
  case hb: (amem b) => [fr'|] //.
  suff /negbTE -> : b != pt.1 by [].
  apply: contra neq_n => /eqP ?; subst b.
  by rewrite (miIr miP hn hn') eqxx.
- move=> w1' v; rewrite (getm_upd upd_w1).
  have [{w1' v}-> _|_] := altP (_ =P _); by eauto.
case=> bi_base bi_size [bi_col in_bi|in_bi]; last first.
  move/(_ _ in_bi): rist => biP.
  inversion biP => //.
  apply: BlockInfoFree => //=.
  move=> off lt_off.
  case/(_ off lt_off): H3 => v /=.
  have [->|/eqP neq_w1] := altP (bi_base + off =P base + pt.2).
     by rewrite get_w1.
  by rewrite (getm_upd_neq neq_w1 upd_w1); move => ?; exists v.
have [eq_coln|neq_coln] := altP (bi_col =P n).
  rewrite eq_coln in in_bi *.
  move/(_ _ in_bi): rist => biP.
  inversion biP => //.
  case: H1 => eq_col.
  rewrite -eq_col in H3 H4.
  apply: (BlockInfoLive _ H2 H3) => //=.
  move=> off lt_off.
  case/(_ off lt_off): H4 => v [ty''].
  destruct pt as [pt_b pt_off].
  rewrite (refine_ptr_inv miP rpt H3) in get_w1 upd_w1.
  have [->|/eqP neq_off] := altP (off =P pt_off).
    by move=> _; rewrite (getm_upd_eq upd_w1); eexists; eexists.
  have neq_w1 : bi_base + off <> bi_base + pt_off.
    move => eq_off.
    by apply: neq_off; apply: (can_inj (GRing.addKr bi_base)).
  by rewrite (getm_upd_neq neq_w1 upd_w1) => ?; eexists; eexists.
move/(_ _ in_bi): rist => biP.
inversion biP => //=.
case: H1 => eq_col.
rewrite -eq_col in H3 H4.
apply: (BlockInfoLive _ H2 H3) => //.
move=> off lt_off.
case/(_ off lt_off): H4 => v [ty''].
have [->|/eqP neq_w1] := altP (bi_base + off =P base + pt.2).
  by rewrite get_w1 => [[_ eq_coln _]]; rewrite eq_coln eqxx in neq_coln.
by rewrite (getm_upd_neq neq_w1 upd_w1); move => ?; eexists; eexists.
Qed.

Definition mi_malloc b base col : meminj :=
  setm mi col (b,base).

Lemma get_write_block_rec (base : mword mt) (v : atom (mword mt) Sym.tag) : forall n init (w : mword mt) mem',
  Sym.write_block_rec init base v n = Some mem' ->
  n < 2 ^ word_size mt ->
  base + n < 2 ^ word_size mt ->
  mem' w =
  if (base <= w < base + n) then Some v else init w.
Proof.
have max_bound := max_word_bound mt.
elim=> [init w mem' [<-] ? ?|n IHn init w mem'].
  by rewrite addn0; case: leqP.
rewrite [in X in X -> _]/=.
case write_block: (Sym.write_block_rec init base v n)=> // upd.
rewrite /= in upd => Hn Hbn.
move/ltnW in Hn; rewrite addnS in Hbn; move/ltnW in Hbn.
have [->|neq_w] := altP (w =P base + as_word n).
  rewrite (getm_upd_eq upd) valw_add as_wordK // (leqNgt (2 ^ _)) Hbn /=.
  by rewrite mul0n subn0 addnS leqnn leq_addr.
rewrite (getm_upd_neq (elimN eqP neq_w) upd) (IHn init _ _ write_block) //.
rewrite (_ : (w < base + n) = (w < base + n.+1)) //.
apply/(sameP idP)/(iffP idP) => Hw; last by rewrite addnS ltnS ltnW.
move: neq_w; rewrite ltnNge; apply: contra.
rewrite addnS ltnS in Hw => Hw'.
apply/eqP/val_inj/val_inj/anti_leq.
rewrite (lock addw) /= -lock valw_add !as_wordK //.
by rewrite [in X in _ <= X <= _]leqNgt Hbn /= mul0n subn0 Hw Hw'.
Qed.

Lemma get_write_block: forall smem base (sz : mword mt) (v : atom (mword mt) Sym.tag) (w : mword mt) mem',
  Sym.write_block smem base v sz = Some mem' ->
  mem' w = if base <= w < base + sz then Some v else smem w.
Proof.
move=> smem base sz v w mem'.
rewrite /Sym.write_block.
have [bound write_block|//] := boolP (_ <= _).
by rewrite (get_write_block_rec _ write_block).
Qed.

Lemma block_color_uniq (smem : Sym.memory mt) bi info bl nc col b w1 w2 ty :
  refine_memory amem smem ->
  refine_internal_state bl smem (nc, info) ->
  bi \in info ->
  mi col = Some (b, Sym.block_base bi) ->
  Sym.block_color bi = Some col ->
  smem w1 = Some w2@M(col, ty) ->
  inbounds (Sym.block_base bi) (Sym.block_size bi) w1.
Proof.
move=> rmem rist in_bi mi_col color_bi get_w1.
case: rist => _ [_ [no_overlap [cover_info biP]]].
case/cover_info: (get_w1) => bi' [in_bi' bounds_bi'].
have eq_base: Sym.block_base bi' = Sym.block_base bi.
  pose (off := w1 - Sym.block_base bi').
  have hoff : off < Sym.block_size bi'.
    have hw1: Sym.block_base bi' <= w1 by case/andP: bounds_bi'.
    rewrite /off valw_sub // -(leq_add2r (Sym.block_base bi')).
    rewrite [in X in _ <= X]addnC addSn /= subnK //.
    by case/andP: bounds_bi'.
  case/(_ bi' in_bi'): biP.
    move=> col' ? _ [? ?] mi_col' /(_ off) [|v [ty']] //.
    rewrite /off /subw addwA (addwC _ w1) -addwA addwN addwC add0w get_w1 => [[_ eq_col _]].
    by move: mi_col; rewrite eq_col mi_col' => [[]].
  move=> _ [? ?] /(_ off) [|v] //.
  by rewrite /off /subw addwA (addwC _ w1) -addwA addwN addwC add0w get_w1.
have<-//: bi' = bi.
rewrite -(nth_index bi' in_bi') -(nth_index bi' in_bi).
have->//: index bi' info = index bi info.
apply: (no_overlap _ _ bi (Sym.block_base bi)).
+ by rewrite index_mem.
+ by rewrite index_mem.
rewrite !nth_index //; split; rewrite ?eq_base ?leqnn /=.
  case/(_ bi' in_bi')/block_info_bounds: biP => [biP ?].
  by rewrite -[X in X < _]addn0 ltn_add2l.
case/(_ bi in_bi)/block_info_bounds: biP => [biP ?].
by rewrite -[X in X < _]addn0 ltn_add2l.
Qed.

Lemma refine_memory_free (amem' : Abstract.memory mt block) (smem smem' : Sym.memory mt) bl nc info b bi col :
  refine_memory amem smem ->
  refine_internal_state bl smem (nc, info) ->
  bi \in info ->
  Sym.block_color bi = Some col ->
  mi col = Some (b, Sym.block_base bi) ->
  Abstract.free_fun amem b = Some amem' ->
  Sym.write_block smem (Sym.block_base bi) 0@FREE (Sym.block_size bi) = Some smem' ->
  refine_memory amem' smem' /\
  refine_internal_state bl smem'
     (nc,
     set_nth (Sym.def_info mt) info (index bi info)
       {|
       Sym.block_base := Sym.block_base bi;
       Sym.block_size := Sym.block_size bi;
       Sym.block_color := None |}).
Proof.
move=> rmem rist in_bi color_bi mi_col free_b write_block.
have ? := @leZ_min (Sym.block_base bi).
case: (rist) => fresh_color [in_bl [no_overlap [cover_info biP]]].
move/(_ bi in_bi)/block_info_bounds: (biP) => [? ?].
case: (rmem) => miP get_smem; split.
  split; first by constructor; apply miP.
  move=> w1 w2 col' ty.
  rewrite (get_write_block _ write_block).
  case: ifP => // bounds get_w1; move/get_smem: (get_w1).
  case mi_col': (mi col') => // [[b' ?]].
  have neq_b: b != b'.
    apply/eqP => eq_bb'; rewrite eq_bb' in mi_col.
    have eq_col := miIr miP mi_col' mi_col.
    rewrite eq_col in get_w1.
    move/(block_color_uniq rmem rist in_bi mi_col color_bi): get_w1.
    by rewrite bounds.
  rewrite /Abstract.getv.
  by rewrite (Abstract.free_get free_b neq_b).
set newbi := Sym.mkBlockInfo _ _ _.
do !split=> //.
+ move=> i j def w; rewrite size_set_nth (maxn_idPr _) ?index_mem //.
  move=> lt_i lt_j.
  rewrite !(set_nth_default (Sym.def_info mt) def) ?size_set_nth ?(maxn_idPr _) ?index_mem //.
  rewrite !nth_set_nth /=.
  have [->|neq_i] := i =P index bi info;
  have [->|neq_j] := j =P index bi info => //=.
  * rewrite /newbi /overlap /= => [[? ?]].
    apply: (no_overlap _ _ (Sym.def_info mt) w) => //.
      by rewrite index_mem.
    by rewrite nth_index.
  * rewrite /newbi /overlap /= => [[? ?]].
    apply: (no_overlap _ _ (Sym.def_info mt) w) => //.
      by rewrite index_mem.
    by rewrite nth_index.
  exact: no_overlap.
+ move=> w v.
  rewrite (get_write_block _ write_block).
  have [bounds_w|bounds_w]:= boolP (inbounds _ _ _).
    move=> _; exists newbi; split=> //.
    apply/(nthP (Sym.def_info mt)).
    exists (index bi info); first by rewrite size_set_nth (maxn_idPr _) ?index_mem.
    by rewrite nth_set_nth /= eqxx.
  case/cover_info=> bi' [in_bi' bounds_bi'].
  exists bi'; split => //.
  apply/(nthP (Sym.def_info mt)).
  exists (index bi' info); first by rewrite size_set_nth (maxn_idPr _) ?index_mem.
  rewrite nth_set_nth /=.
  have [eq_index|] := index bi' info =P index bi info; last by rewrite nth_index.
  have eq_bi: bi' = bi.
    by rewrite -(nth_index bi in_bi) -(nth_index bi in_bi') eq_index.
  by rewrite eq_bi in bounds_bi'; rewrite bounds_bi' in bounds_w.
move=> bi'.
case/(nthP (Sym.def_info mt))=> i.
rewrite size_set_nth (maxn_idPr _) ?index_mem // => lt_i.
rewrite nth_set_nth /=.
have [_ <-|neq_i <-] := i =P index bi info.
  move/(_ bi in_bi)/block_info_bounds: biP => [? ubound].
  apply: BlockInfoFree=> //.
  move=> off /= bounds_off; exists 0.
  rewrite (get_write_block _ write_block) valw_add (leqNgt (2 ^ _)).
  rewrite (ltn_trans _ ubound) ?ltn_add2l //= mul0n subn0.
  by rewrite leq_addr ltn_add2l bounds_off.
move {bi'}.
set bi' := nth _ _ _.
have ? := @leZ_min (Sym.block_base bi').
move/(_ bi'): biP.
rewrite mem_nth //.
case/(_ erefl)=> [? ? ? [? ubound] ? get_bi'|? [? ubound] get_bi'].
  apply: BlockInfoLive=> //.
  move=> off bounds_off.
  case: {get_bi'} (get_bi' off bounds_off)=> w [ty get_bi'].
  exists w; exists ty.
  rewrite (get_write_block _ write_block).
  have off_in_bounds : inbounds (Sym.block_base bi') (Sym.block_size bi')
                                (Sym.block_base bi' + off)%w.
    rewrite valw_add (leqNgt (2 ^ _)).
    rewrite (ltn_trans _ ubound) ?ltn_add2l //= mul0n subn0.
    by rewrite leq_addr ltn_add2l bounds_off.
  have [off_in_bounds'|//] := boolP (inbounds _ _ _).
  case: neq_i.
  apply: (no_overlap _ _ (Sym.def_info mt) (Sym.block_base bi' + off)) => //.
    by rewrite index_mem.
  by unfold bi' in *; rewrite nth_index // /overlap.
apply: BlockInfoFree=> //.
move=> off bounds_off.
case: {get_bi'} (get_bi' off bounds_off)=> w get_bi'.
exists w.
rewrite (get_write_block _ write_block).
have off_in_bounds : inbounds (Sym.block_base bi') (Sym.block_size bi')
                              (Sym.block_base bi' + off)%w.
  rewrite valw_add (leqNgt (2 ^ _)).
  rewrite (ltn_trans _ ubound) ?ltn_add2l //= mul0n subn0.
  by rewrite leq_addr ltn_add2l bounds_off.
have [off_in_bounds'|//] := boolP (inbounds _ _ _).
case: neq_i.
apply: (no_overlap _ _ (Sym.def_info mt) (Sym.block_base bi' + off)) => //.
  by rewrite index_mem.
by unfold bi' in *; rewrite nth_index // /overlap.
Qed.

Definition refine_reg_val v a :=
 match a with w@V(ty) => refine_val v w ty | _ => False end.

Definition refine_registers (aregs : Abstract.registers mt block)
                            (qaregs : Sym.registers mt) :=
  pointwise refine_reg_val aregs qaregs.

Lemma refine_registers_val aregs qaregs r v : refine_registers aregs qaregs ->
  qaregs r = Some v ->
  exists w ty, v = w@V(ty).
Proof.
intros rregs get_r; specialize (rregs r); revert rregs.
rewrite get_r; destruct (aregs r); try easy.
by destruct v as [w [ty | |]]; try easy; exists w; exists ty.
Qed.

Lemma refine_registers_get aregs qaregs (n : common.reg mt) w ty :
  refine_registers aregs qaregs ->
  qaregs n = Some w@V(ty) ->
  exists x, refine_val x w ty /\ aregs n = Some x.
Proof.
intros rregs qa_get.
generalize (rregs n).
rewrite qa_get.
destruct (aregs n); try easy.
simpl; intros rvx.
by exists v; split.
Qed.

Lemma refine_registers_get_int aregs qaregs (n : common.reg mt) w :
  refine_registers aregs qaregs ->
  qaregs n = Some w@V(DATA) ->
    refine_val (Abstract.VData _ w) w DATA /\
    aregs n = Some (Abstract.VData _ w).
Proof.
intros rregs get_n.
specialize (rregs n).
rewrite get_n in rregs.
destruct (aregs n); try contradiction.
by inversion rregs; split; first by constructor.
Qed.

Lemma refine_registers_get_ptr aregs qaregs (n : common.reg mt) w b :
  refine_registers aregs qaregs ->
  qaregs n = Some w@V(PTR b) ->
  exists pt, refine_val (Abstract.VPtr pt) w (PTR b) /\
    aregs n = Some (Abstract.VPtr pt).
Proof.
intros rregs qa_get.
generalize (rregs n).
rewrite qa_get.
destruct (aregs n); try easy.
simpl; intros rvx.
destruct v as [|pt].
  by inversion rvx.
by exists pt; split.
Qed.

Lemma refine_registers_upd aregs qaregs qaregs' r v w ty :
  refine_registers aregs qaregs ->
  refine_val v w ty ->
  updm qaregs r w@V(ty) = Some qaregs' ->
  exists areg',
    updm aregs r v = Some areg' /\
    refine_registers areg' qaregs'.
Proof.
intros rregs rvw upd_r_qa.
assert (ref_r := rregs r).
destruct (updm_inv upd_r_qa) as [v' get_r_qa].
rewrite get_r_qa in ref_r.
destruct (aregs r) as [w'|] eqn:get_r_a; try contradiction.
destruct (updm_defined v get_r_a) as [aregs' upd_r_a].
exists aregs'; split; try easy.
intros r'.
have [->|/eqP neq_rr'] := altP (r' =P r).
  rewrite (getm_upd_eq upd_r_a).
  by rewrite (getm_upd_eq upd_r_qa).
rewrite (getm_upd_neq neq_rr' upd_r_a).
rewrite (getm_upd_neq neq_rr' upd_r_qa).
by apply rregs.
Qed.

Definition refine_state (ast : Abstract.state mt block) (sst : @Symbolic.state mt (Sym.sym_memory_safety mt)) :=
  let '(Abstract.mkState amem aregs bl apc) := ast in
  match sst with
  | Symbolic.State smem sregs w@V(ty) ist =>
    [/\ refine_memory amem smem,
        refine_registers aregs sregs,
        refine_val apc w ty &
        refine_internal_state bl smem ist]
  | _ => False
  end.

End memory_injections.

Lemma refine_val_malloc mi amem bl sz amem' newb base col v w ty :
  fresh_color mi col ->
  Abstract.malloc_fun amem bl sz = (amem', newb) ->
  refine_val mi v w ty -> refine_val (mi_malloc mi newb base col) v w ty.
Proof.
move=> fresh_col malloc [w'|b base' col' off mi_b]; first by constructor.
constructor.
have neq_col: col' <> col.
  by move=> eq_col; move/fresh_col: mi_b; rewrite eq_col Ord.leqxx.
by rewrite getm_set (introF eqP neq_col).
Qed.


Lemma refine_registers_malloc mi aregs sregs amem amem' bl sz newb base col :
  fresh_color mi col ->
  Abstract.malloc_fun amem bl sz = (amem', newb) ->
  refine_registers mi aregs sregs ->
  refine_registers (mi_malloc mi newb base col) aregs sregs.
Proof.
  intros.
  unfold refine_registers. unfold mi_malloc.
  eapply refine_extend_map with
    (P := refine_reg_val)
    (f := fun mi' col' nb' => mi = mi' /\ col = col' /\ (newb,base) = nb'); auto.
  intros ? ? ? ? ? [E1 [E2 [R]]]. subst k1 km.
  unfold refine_reg_val. destruct v2; destruct tag; auto.
  eapply refine_val_malloc; eauto.
Qed.

Lemma meminj_spec_malloc mi amem smem amem' info bl sz newb base col :
  refine_internal_state mi bl smem (col, info) ->
  Abstract.malloc_fun amem bl sz = (amem', newb) ->
  meminj_spec amem mi ->
  meminj_spec amem' (mi_malloc mi newb base col).
Proof.
move=> [fresh_col [in_bl rist]] malloc miP.
constructor => b col' col'' base' base''.
have [->|/eqP neq_col'] := altP (col' =P col);
have [-> //|/eqP neq_col''] := altP (col'' =P col).
+ rewrite !getm_set eqxx (introF eqP neq_col'') => [[<- _]] /in_bl.
  by rewrite (negbTE (Abstract.malloc_fresh malloc)).
+ rewrite !getm_set eqxx (introF eqP neq_col') => get_col' [eq_b _].
  move/in_bl: get_col'.
  by rewrite -eq_b (negbTE (Abstract.malloc_fresh malloc)).
+ rewrite !getm_set (introF eqP neq_col') (introF eqP neq_col'').
exact: (miIr miP).
Qed.

Lemma refine_memory_malloc mi amem smem amem' info bl sz newb base col smem' :
  refine_memory mi amem smem ->
  refine_internal_state mi bl smem (col, info) ->
  Abstract.malloc_fun amem bl sz = (amem', newb) ->
  Sym.write_block smem base 0@M(col, DATA) sz = Some smem' ->
  refine_memory (mi_malloc mi newb base col) amem' smem'.
Proof.
case=> miP rmem rist malloc.
case: (rist) => [fresh_col [in_bl [no_overlap biP]]].
split; first exact: (meminj_spec_malloc _ rist malloc).
move=> w1 w2 col' ty.
rewrite (get_write_block _ H1) => //.
have [/andP [? ?] [<- <- <-]|_ /rmem get_w1] :=
  boolP (inbounds base sz w1).
  rewrite getm_set eqxx (Abstract.malloc_get malloc); last first.
    rewrite -2!val_ordE (lock subw) /= -lock valw_sub // /Ord.leq /= -ltnNge.
    by rewrite -(ltn_add2r base) subnK // addnC.
  apply: (refine_val_malloc _ fresh_col malloc).
  by constructor.
have neq_col: col' <> col.
  move=> eq_col.
  move: get_w1; rewrite eq_col.
  move: (fresh_col col).
  case: (mi col) => // [[b' base']] /(_ b' base' erefl) lt_col.
  by rewrite Ord.leqxx in lt_col.

move: get_w1.
set mi' := mi_malloc _ _ _ _.
have mi'P := (meminj_spec_malloc base rist malloc miP).
have eq_mi: mi' col' = mi col'.
  by rewrite getm_set (introF eqP neq_col).
rewrite eq_mi; move: eq_mi.
case: (mi col') => // [[b' base']] mi'_col'.
have neq_b': b' <> newb.
  move=> eq_b'; rewrite eq_b' in mi'_col'.
  have mi'_col: mi' col = Some (newb, base).
    by rewrite getm_set eqxx.
  exact/neq_col/(miIr mi'P mi'_col' mi'_col).
rewrite /Abstract.getv (Abstract.malloc_get_neq malloc neq_b').
case: (amem b') => // fr.
rewrite (lock subw) /= -lock.
case: (_ < _) => [rvw2|//].
by apply: (refine_val_malloc _ fresh_col malloc).
Qed.

Lemma refine_internal_state_malloc mi amem amem' bl smem info (sz : mword mt) newb bi color smem' :
  0 < sz <= Sym.block_size bi ->
  Abstract.malloc_fun amem bl sz = (amem', newb) ->
  (color < Sym.max_color)%ord ->
  Sym.block_color bi = None ->
  bi \in info ->
  refine_internal_state mi bl smem (color, info) ->
  Sym.write_block smem (Sym.block_base bi) 0@M(color, DATA) sz = Some smem' ->
  refine_internal_state (mi_malloc mi newb (Sym.block_base bi) color)
    (newb :: bl) smem' (Sym.inc_color color, Sym.update_block_info info bi color sz).
Proof.
move=> /andP [nneg_sz le_sz] malloc lt_color color_bi in_bi.
case=> [fresh_color [in_bl [no_overlap [cover_info biP]]]] write_bi.
have [? ?] := block_info_bounds (biP _ in_bi).
have ? := @leZ_min (Sym.block_base bi).
have ? := @leZ_max (Sym.block_size bi).
(*generalize (@min_word_bound mt) => min_bound.
generalize (max_word_bound mt) => max_bound.*)
split. (* freshness of color *)
  rewrite /refinement.fresh_color.
  move=> col b base.
  have [-> _|neq_col] := col =P color.
    exact/Sym.ltb_inc.
  rewrite getm_set (introF eqP neq_col).
  move/fresh_color => lt_col.
  apply: (@Ord.lt_trans _ color col) => //=.
  exact/Sym.ltb_inc.
split. (* list of block is complete *)
  move=> col b base.
  have [->|neq_col] := col =P color.
    by rewrite getm_set eqxx => [[<- _]]; rewrite inE eqxx.
  by rewrite getm_set (introF eqP neq_col) inE => /in_bl ->; rewrite orbT.
split. (* no overlap *)
  move=> i j def w.
  rewrite /Sym.update_block_info.
  set newbi := Sym.mkBlockInfo _ _ _.
  have [eq_sz|_] := sz =P Sym.block_size bi.
    rewrite !size_set_nth (maxn_idPr _) ?index_mem // => lt_i lt_j.
    rewrite !(set_nth_default newbi) ?size_set_nth ?(maxn_idPr _) ?index_mem //.
    rewrite !nth_set_nth /=.
    have [->|neq_i] := i =P index bi info;
    have [->|neq_j] := j =P index bi info => //=.
    + move=> overlap.
      apply: (no_overlap _ _ newbi w) => //.
        by rewrite index_mem.
      by rewrite nth_index // /refinement.overlap -eq_sz.
    + move=> overlap.
      apply: (no_overlap _ _ newbi w) => //.
        by rewrite index_mem.
      by rewrite nth_index // /refinement.overlap -eq_sz.
    + exact: no_overlap.
  rewrite /= !size_set_nth (maxn_idPr _) ?index_mem // => lt_i lt_j.
  rewrite !(set_nth_default newbi) /= ?size_set_nth ?(maxn_idPr _) ?index_mem //.
  case: i lt_i => [|i] lt_i; case: j lt_j => [|j] lt_j //=;
  rewrite !nth_set_nth /overlap.
  + rewrite (lock addw) (lock subw) /= -!lock.
    have [->|neq_j] := j =P index bi info.
      case=> [/andP [ge_w _] /andP [_ lt_w]].
      rewrite -(leq_add2l (Sym.block_base bi)) in le_sz.
      rewrite valw_add (leqNgt (2 ^ _)) (leq_ltn_trans le_sz) //= in ge_w.
      rewrite mul0n subn0 in ge_w.
      by rewrite ltnNge ge_w in lt_w.
    case=> [/andP [ge_w lt_w] ?].
    rewrite valw_sub // in lt_w.
    move: (le_sz); rewrite -(leq_add2l (Sym.block_base bi)) => le_sz'.
    rewrite valw_add (leqNgt (2 ^ _)) in ge_w lt_w.
    rewrite (leq_ltn_trans le_sz') {le_sz'} //= mul0n subn0 in ge_w lt_w.
    case: neq_j; apply: (no_overlap _ _ newbi w) => //.
      by rewrite index_mem.
    rewrite nth_index // /overlap; split=> //.
    rewrite -addnA (addnC sz) subnK // in lt_w; rewrite {}lt_w andbT.
    by rewrite (@leq_trans (Sym.block_base bi + sz)) // leq_addr.
  + rewrite (lock addw) (lock subw) /= -!lock.
    rewrite valw_add valw_sub // (leqNgt (2 ^ _)) (_: _ < 2 ^ _); last first.
      apply: (@leq_ltn_trans (Sym.block_base bi + Sym.block_size bi)) => //.
      by rewrite leq_add2l.
    rewrite /= mul0n subn0.
    have [->|neq_i] := i =P index bi info.
      by rewrite [in X in _ /\ X]leqNgt => - [/andP [_ ->]].
    case=> [? /andP [ge_w lt_w]].
    case: neq_i; apply: (no_overlap _ _ newbi w) => //.
      by rewrite index_mem.
    rewrite nth_index // /overlap; split=> //.
    rewrite -addnA (addnC sz) subnK // in lt_w.
    rewrite lt_w andbT.
    by eapply leq_trans; eauto using leq_addr.
  + simpl; have [->|neq_i] := i =P index bi info;
    have [->|neq_j] := j =P index bi info => //=.
    * case=> /= [in_newbi in_j].
      congr S.
      apply: (no_overlap _ _ newbi w) => //.
        by rewrite index_mem.
      rewrite nth_index //; split=> //.
      case/andP: in_newbi => [-> gt_w] /=.
      eapply leq_trans; first exact: gt_w.
      by rewrite leq_add2l.
    * case=> /= [in_i in_newbi]; congr S.
      apply: (no_overlap _ _ newbi w) => //.
        by rewrite index_mem.
      rewrite nth_index //; split=> //.
      case/andP: in_newbi => [-> gt_w] /=.
      eapply leq_trans; first exact: gt_w.
      by rewrite leq_add2l.
    * by move/(no_overlap _ _ _ _ lt_i lt_j)->.
split. (* cover *)
  rewrite /Sym.update_block_info.
  set newbi := Sym.mkBlockInfo _ _ _.
  move=> w v.
  rewrite (get_write_block _ write_bi).
  have [eq_sz|_] := sz =P Sym.block_size bi.
    (* first case: sizes are equal, the covering block_infos remain the same *)
    have [bounds_bi|bounds_bi] := boolP (inbounds _ _ _).
      (* area covered by the new block_info *)
      exists newbi; split=> //.
      apply/(nthP newbi).
      exists (index bi info).
        by rewrite size_set_nth (maxn_idPr _) ?index_mem // ltnS ltnW // index_mem.
      by rewrite nth_set_nth /= eqxx.
    (* unchanged block *)
    case/cover_info=> bi' [in_bi' bounds_bi']; exists bi'; split=> //.
    apply/(nthP newbi).
    rewrite size_set_nth (maxn_idPr _) ?index_mem //.
    exists (index bi' info); first by rewrite index_mem.
    rewrite nth_set_nth /=.
    have [eq_index|] := index bi' info =P index bi info; last by rewrite nth_index.
    have eq_bi: bi' = bi.
      by rewrite -(nth_index bi in_bi) -(nth_index bi in_bi') eq_index.
    rewrite eq_bi in bounds_bi'; rewrite eq_sz in bounds_bi.
    by rewrite bounds_bi' in bounds_bi.
  (* second case: different sizes. The old block_info is now covered by two block_infos *)
  set newbi2 := Sym.mkBlockInfo _ _ _.

  have [bounds_bi|bounds_bi] :=
    boolP (inbounds (Sym.block_base bi) (Sym.block_size bi) w).
    (* We are in the old block *)
    have [lt_w_sz|le_sz_w] := boolP (w < Sym.block_base bi + sz).
      (* We are in the lower part of the old block *)
      rewrite andbT.
      have->: Sym.block_base bi <= w by case/andP: bounds_bi.
      move=> _; exists newbi; split.
        apply/(nthP newbi); exists (index bi info).+1.
          by rewrite /= size_set_nth (maxn_idPr _) ?index_mem // ltnS index_mem.
        by rewrite /= nth_set_nth /= eqxx.
      rewrite /newbi /= lt_w_sz andbT.
      by case/andP: bounds_bi.
    (* We are in the higher part of the old block *)
    rewrite andbF; exists newbi2; split.
      by apply/(nthP newbi); exists 0%N.
    rewrite -leqNgt in le_sz_w.
    rewrite /newbi2 (lock addw) (lock subw) /= -!lock.
    rewrite valw_add valw_sub // (leqNgt (2 ^ _)).
    rewrite (_ : Sym.block_base bi + _ < 2 ^ _) /=; last first.
      rewrite -(leq_add2l (Sym.block_base bi)) in le_sz.
      by apply: (leq_ltn_trans le_sz).
    rewrite mul0n subn0 le_sz_w /= -addnA (addnC sz) subnK //.
    by case/andP: bounds_bi.
  (* We are in another block *)
  have /negbTE -> : ~~ inbounds (Sym.block_base bi) sz w.
    move: bounds_bi; apply: contra => /andP [-> bounds_bi] /=.
    apply: (leq_trans bounds_bi).
    by rewrite leq_add2l.
  case/cover_info=> bi' [in_bi' bounds_bi']; exists bi'; split=> //.
  apply/(nthP newbi).
  rewrite /= size_set_nth (maxn_idPr _) ?index_mem //.
  exists (index bi' info).+1; first by rewrite ltnS index_mem.
  rewrite /= nth_set_nth /=.
  have [eq_index|] := index bi' info =P index bi info; last by rewrite nth_index.
  have eq_bi: bi' = bi.
    by rewrite -(nth_index bi in_bi) -(nth_index bi in_bi') eq_index.
  by rewrite eq_bi (negbTE bounds_bi) in bounds_bi'.

rewrite /Sym.update_block_info.
move=> bi'.
have ? := @leZ_min (Sym.block_base bi').
have ? := @leZ_max (Sym.block_size bi').
set mi' := mi_malloc _ _ _ _.
set newbi := Sym.mkBlockInfo _ _ _.
have [eq_sz|neq_sz] := sz =P Sym.block_size bi.
  case/(nthP newbi) => i.
  rewrite size_set_nth (maxn_idPr _) ?index_mem // => lt_i.
  rewrite nth_set_nth /=.
  have [eq_i <-|neq_i] := i =P index bi info.
    (* Showing invariant for the new block *)
    apply: (@BlockInfoLive _ _ _ color newb) => //.
    * by rewrite /bounded_add /= eq_sz.
    * by rewrite getm_set eqxx.
    move=> off /= lt_off.
    rewrite (get_write_block _ write_bi).
    suff ->: inbounds (Sym.block_base bi) sz (Sym.block_base bi + off)%w.
      by eexists; eexists.
    rewrite valw_add (leqNgt (2 ^ _)).
    have -> /= : Sym.block_base bi + off < 2 ^ word_size mt.
      rewrite -(ltn_add2l (Sym.block_base bi)) in lt_off.
      apply: (ltn_trans lt_off).
      by rewrite eq_sz.
    by rewrite subn0 leq_addr ltn_add2l.
  (* Showing that invariant is preserved for other blocks *)
  move=> nth_i; move: (biP bi'); rewrite -nth_i mem_nth // nth_i.
  move/(_ erefl) => bi'P.
  case: bi'P.
    move=> col b color_bi' [? ?] mi_col get_bi'.
    apply: (@BlockInfoLive _ _ _ col b) => //.
      have neq_col: col <> color.
        by move=> eq_col; move/fresh_color: mi_col; rewrite eq_col Ord.leqxx.
      by rewrite getm_set (introF eqP neq_col).
    move=> off lt_off.
    rewrite (get_write_block _ write_bi).
    have [bounds_bi|] := boolP (inbounds _ _ _).
      case: neq_i; apply: (no_overlap _ _ newbi (Sym.block_base bi' + off) lt_i).
        by rewrite index_mem.
      rewrite nth_i nth_index //; split; last by rewrite -eq_sz.
      rewrite valw_add (leqNgt (2 ^ _)).
      move: (lt_off).
      rewrite -(ltn_add2l (Sym.block_base bi')) => /ltn_trans -> //.
      by rewrite subn0 leq_addr ltn_add2l.
    by move=> _; apply: get_bi'.
  move=> color_bi' [? ?] get_bi'.
  apply: BlockInfoFree => //.
  move=> off bounds_off.
  rewrite (get_write_block _ write_bi).
  have [bounds_bi|] := boolP (inbounds _ _ _).
    case: neq_i; apply: (no_overlap _ _ newbi (Sym.block_base bi' + off) lt_i).
      by rewrite index_mem.
    rewrite nth_i nth_index //; split; last by rewrite -eq_sz.
    rewrite valw_add (leqNgt (2 ^ _)).
    move: (bounds_off).
    rewrite -(ltn_add2l (Sym.block_base bi')) => /ltn_trans -> //.
    by rewrite subn0 leq_addr ltn_add2l.
  by move=> _; apply: get_bi'.
have lt_sz: sz < Sym.block_size bi.
  by rewrite ltn_neqAle (introN eqP neq_sz).
case/(nthP newbi) => i.
rewrite /= size_set_nth (maxn_idPr _) ?index_mem // => lt_i.
case: i lt_i => [|i] lt_i /=.
  move=> <-.
  constructor=> //.
    rewrite /bounded_add (lock addw) (lock subw) /= -!lock.
    rewrite valw_sub // ltn_subRL addn0; split=> //.
    rewrite valw_add (leqNgt (2 ^ _)).
    move: (lt_sz).
    rewrite -(ltn_add2l (Sym.block_base bi)) => /ltn_trans -> //.
    by rewrite subn0 -addnA (addnC sz) subnK.
  move=> off bounds_off.
  rewrite (get_write_block _ write_bi).
  rewrite (lock subw) /= -lock valw_sub // ltn_subRL in bounds_off.
  rewrite (lock addw) (lock subw) /= -!lock.
  have [bounds_bi|_] := boolP (inbounds _ _ _).
    rewrite !valw_add !(leqNgt (2 ^ _)) in bounds_bi.
    have bsz : Sym.block_base bi + sz < 2 ^ word_size mt.
      rewrite -(leq_add2l (Sym.block_base bi)) in le_sz.
      by apply: (leq_ltn_trans le_sz).
    rewrite {}bsz subn0 in bounds_bi.
    rewrite -(leq_add2l (Sym.block_base bi)) addnS addnA in bounds_off.
    rewrite (ltn_trans bounds_off) // subn0 in bounds_bi.
    suff : Sym.block_base bi + sz < Sym.block_base bi + sz by rewrite ltnn.
    case/andP: bounds_bi => [_].
    by apply: leq_ltn_trans; apply: leq_addr.
  have [|_ _ get_bi] := biP bi in_bi; first by rewrite color_bi.
  rewrite -addwA.
  apply: get_bi.
  rewrite valw_add (leqNgt (2 ^ _)) (ltn_trans bounds_off) //.
  by rewrite subn0.
rewrite !nth_set_nth /=.
have [eq_i <-|neq_i] := i =P index bi info.
  apply: (@BlockInfoLive _ _ _ color newb) => //.
  * rewrite /= /bounded_add; split=> //.
    rewrite -(leq_add2l (Sym.block_base bi)) in le_sz.
    by rewrite (leq_ltn_trans le_sz).
  * by rewrite getm_set eqxx.
  move=> off /= lt_off.
  rewrite (get_write_block _ write_bi).
  suff ->: inbounds (Sym.block_base bi) sz (Sym.block_base bi + off)%w
    by eexists; eexists.
  rewrite valw_add (leqNgt (2 ^ _)).
  move: (ltn_trans lt_off lt_sz).
  rewrite -(ltn_add2l (Sym.block_base bi)) => /ltn_trans -> //.
  by rewrite subn0 leq_addr ltn_add2l.
move=> nth_i; move: (biP bi'); rewrite -nth_i mem_nth // nth_i.
case=> //.
  move=> col b color_bi' [? ?] mi_col get_bi'.
  apply: (@BlockInfoLive _ _ _ col b) => //.
    have neq_col: col <> color.
      by move=> eq_col; move/fresh_color: mi_col; rewrite eq_col Ord.leqxx.
    by rewrite getm_set (introF eqP neq_col).
  move=> off lt_off.
  rewrite (get_write_block _ write_bi).
  have [/andP [lbbi ubbi]|] := boolP (inbounds _ _ _).
    case: neq_i; apply: (no_overlap _ _ newbi (Sym.block_base bi' + off) lt_i).
      by rewrite index_mem.
    rewrite nth_i nth_index //; split.
      rewrite valw_add (leqNgt (2 ^ _)).
      rewrite (_ : _ < _ = true) ?subn0 ?leq_addr ?ltn_add2l //.
      rewrite -(ltn_add2l (Sym.block_base bi')) in lt_off.
      by rewrite (ltn_trans lt_off).
    by rewrite lbbi (ltn_trans ubbi) // ltn_add2l.
  by move=> _; apply: get_bi'.
move=> color_bi' [? ?] get_bi'.
apply: BlockInfoFree => //.
move=> off bounds_off.
rewrite (get_write_block _ write_bi).
have [/andP [lbbi ubbi]|] := boolP (inbounds _ _ _).
  case: neq_i; apply: (no_overlap _ _ newbi (Sym.block_base bi' + off) lt_i).
    by rewrite index_mem.
  rewrite nth_i nth_index //; split.
    rewrite valw_add (leqNgt (2 ^ _)).
    rewrite (_ : _ < _ = true) ?subn0 ?leq_addr ?ltn_add2l //.
    rewrite -(ltn_add2l (Sym.block_base bi')) in bounds_off.
    by rewrite (ltn_trans bounds_off).
  by rewrite lbbi (ltn_trans ubbi) // ltn_add2l.
by move=> _; apply: get_bi'.
Qed.

Hint Constructors refine_val refine_val.
Hint Resolve get_mem_memv.
Hint Resolve meminj_update.

Lemma refine_pc_inv mi col apcb apci pc :
  refine_val mi (Abstract.VPtr (apcb, apci)) pc (PTR col) ->
  exists base, mi col = Some (apcb,base) /\ (base + apci)%w = pc.
Proof.
intros rpc; inversion rpc.
by exists base; split.
Qed.

Ltac subst_beq :=
  match goal with
  | EQ : (?x == ?y) = true |- _ => (move/eqP: EQ => EQ; subst) || fail 2
  end.

Definition lift_binop (f : binop) (x y : atom (mword mt) Sym.tag) :=
  match f with
  | ADD => match x, y with
           | w1@V(DATA), w2@V(DATA) => Some (binop_denote f w1 w2, DATA)
           | w1@V(PTR b), w2@V(DATA) => Some (binop_denote f w1 w2, PTR b)
           | w1@V(DATA), w2@V(PTR b) => Some (binop_denote f w1 w2, PTR b)
           | _, _ => None
           end
  | SUB => match x, y with
           | w1@V(DATA), w2@V(DATA) => Some (binop_denote f w1 w2, DATA)
           | w1@V(PTR b), w2@V(DATA) => Some (binop_denote f w1 w2, PTR b)
           | w1@V(PTR b1), w2@V(PTR b2) =>
             if b1 == b2 then Some (binop_denote f w1 w2, DATA)
             else None
           | _, _ => None
           end
  | EQ => match x, y with
          | w1@V(DATA), w2@V(DATA) => Some (binop_denote f w1 w2, DATA)
          | w1@V(PTR b1), w2@V(PTR b2) =>
            if b1 == b2 then Some (binop_denote f w1 w2, DATA)
            else None
          | _, _ => None
          end
  | _ => match x, y with
         | w1@V(DATA), w2@V(DATA) => Some (binop_denote f w1 w2, DATA)
         | _, _ => None
         end
  end.

Lemma refine_binop mi amem f v1 w1 ty1 v2 w2 ty2 w3 ty3 :
  meminj_spec amem mi ->
  refine_val mi v1 w1 ty1 -> refine_val mi v2 w2 ty2 ->
  lift_binop f w1@V(ty1) w2@V(ty2) = Some (w3,ty3) ->
  exists v3, Abstract.lift_binop f v1 v2 = Some v3 /\ refine_val mi v3 w3 ty3.
Proof.
Opaque binop_denote. (* Only for now... *)
destruct f; intros miP [x1 | b1 base1 nonce1 off1 mi_b1]
  [x2 | b2 base2 nonce2 off2 mi_b2] hyp; try discriminate hyp;
try (injection hyp; intros <- <-; eexists; split; [reflexivity|]); try constructor.
- by rewrite binop_addDr; constructor.
- by rewrite binop_addDl;  constructor.
- by rewrite binop_subDl; constructor.
- eexists.
  revert hyp. simpl.
  have [nonces_eq|nonces_neq] := altP (nonce1 =P nonce2).
  +  subst. intro hyp. inv hyp.
     rewrite mi_b2 in mi_b1; subst.  inv mi_b1.
     split. rewrite eq_refl. auto.
     rewrite binop_sub_add2l. constructor.
  +  intro X; inv X.
- eexists.
  revert hyp. simpl.
  have [nonces_eq|nonces_neq] := altP (nonce1 =P nonce2).
  + subst. intro hyp; inv hyp.
    rewrite mi_b2 in mi_b1; subst. inv mi_b1.
    split. rewrite eq_refl. auto.
    rewrite binop_eq_add2l. constructor.
  + intro X; inv X.
Transparent binop_denote.
Qed.

Ltac solve_pc rpci :=
  by eexists; eexists; split;
  [econstructor (by eauto) |
  split; try eassumption;
  simpl; rewrite <-rpci, <-addwA; econstructor].

Lemma backward_simulation ast mi sym_st sym_st' :
  refine_state mi ast sym_st ->
  Sym.step sym_st sym_st' ->
  exists ast' mi', Abstract.step ast ast' /\ refine_state mi' ast' sym_st'.
Proof.
case: ast => a_mem a_regs bl a_pc.
case: sym_st => sym_mem sym_regs sym_pc // sym_ist rst.
case: sym_st' => sym_mem' sym_regs' [spcv' spcl'] sym_ist' sym_step.
inv sym_step;
case: ST => *; subst;
destruct tpc as [[|]| |] => //;
case: rst => rmem rregs rpc rist;
destruct a_pc as [|[pc_b pc_off]]; try (by inversion rpc);
try subst mvec;
try rewrite /Symbolic.next_state_pc /Symbolic.next_state_reg /Symbolic.next_state_reg_and_pc /Symbolic.next_state /= /= in NEXT;
match_inv;
repeat subst_beq;
have [miP get_amem] := rmem;
try have [rpcb [mi_apcb rpci]] := refine_pc_inv rpc;

try match goal with
| GETCALL : Symbolic.get_syscall _ _ = Some _,
  CALL : Symbolic.run_syscall _ _ = Some _,
  PC : getm _ ?pc = None |- _ =>
  (move: GETCALL CALL;
  case: extra rist => color info rist;
  rewrite /Symbolic.get_syscall /Symbolic.run_syscall /=;
  match goal with
  | rpc : refine_val _ _ ?pc (PTR ?s) |- _ =>
    (have->: s = pc by inversion rpc);
    repeat case: ifP=> [/eqP <- /= [<-] /= | ? //];
    rewrite /Sym.malloc_fun /Sym.sizeof_fun /Sym.free_fun /Sym.basep_fun /Sym.eqp_fun /Sym.ptr_fun /= => CALL;
    match_inv
  | rpc : refine_val _ (Abstract.VData _ ?s) ?pc _ |- _ =>
    (have->: s = pc by inversion rpc);
    repeat case: ifP=> [/eqP <- /= [<-] /= | ? //];
    rewrite /Sym.malloc_fun /Sym.sizeof_fun /Sym.free_fun /Sym.basep_fun /Sym.eqp_fun /Sym.ptr_fun /= => CALL;
    match_inv
  end) || let op := current_instr_opcode in fail 5 "system_calls"
end;

repeat match goal with
  | GET : getm ?reg ?r = Some ?v@V(?ty),
    rregs : refine_registers _ _ ?reg |- _ =>
    match ty with
    | DATA => eapply (refine_registers_get_int rregs) in GET; destruct GET as [? ?]
    | PTR _ =>
      (eapply (refine_registers_get_ptr rregs) in GET; destruct GET as ((? & ?) & ? & ?))
        || let op := current_instr_opcode in fail 5 "refine_registers_get_ptr" op GET
    | _ =>
    (eapply (refine_registers_get rregs) in GET; destruct GET as (? & ? & ?))
        || let op := current_instr_opcode in
            fail 5 "refine_registers_get" op GET
    end
  end;

match goal with
| GET : getm ?mem ?w1 = Some _@M(?w2,?ty),
  UPD : updm ?mem ?w1 _@_ = Some _,
  rmem : refine_memory _ _ ?mem |- _ =>
    move: (GET) => GET2;
    eapply (refine_memory_get rmem) in GET; [|by eauto]; destruct GET as [? ? ?]
  | |- _ => idtac
end;

match goal with
| UPD : updm ?mem ?w1 ?v@_ = Some _,
  rmem : refine_memory _ _ ?mem,
  rv : refine_val mi ?x ?v _,
  GET : getm ?mem ?w1 = Some _ |- _ =>
    eapply (refine_memory_upd rmem) in UPD;
    [|by eauto|by eauto|by eauto|by eauto];
    destruct UPD as [? [? ? ?]];
    clear GET
  | |- _ => idtac
end;

repeat match goal with
  | GET : getm ?mem ?w1 = Some ?v@M(_,?ty),
    rmem : refine_memory _ _ ?mem |- _ =>
    match ty with
    | DATA => (eapply (refine_memory_get_int rmem) in GET; [|by eauto])
                    || fail 5 "refine_memory_get_int"
    | _ =>
    (eapply (refine_memory_get rmem) in GET; [|by eauto]; destruct GET as [? ? ?]) || let op := current_instr_opcode in
            fail 5 "refine_memory_get" op GET
    end
  end;

try match goal with
| _ : context[binop_denote ?op ?w1 ?w2], rw1 : refine_val mi _ ?w1 _, rw2 : refine_val mi _ ?w2 _ |- _ =>
  (have := refine_binop (f := op) miP rw1 rw2;
  rewrite /= ?eqxx => /(_ _ _ erefl) [? [? ?]]) ||
  let op := current_instr_opcode in
  fail 3 "refine_binop" op
end;

match goal with
  | UPD : updm ?reg ?r ?v = Some _,
    rreg : refine_registers _ _ ?reg |- _ =>
    (eapply (refine_registers_upd rregs) in UPD; [|by eauto]; destruct UPD as (? & ? & ?)) (* || let op := current_instr_opcode in fail 3 "refine_registers_upd" op UPD *)
  | |- _ => idtac
  end;

repeat match goal with
  | def := _ |- _ => rewrite /def
end;

try solve_pc rpci.

(* Jal *)
simpl in E.
eapply (refine_registers_upd rregs) in E; last first.
by rewrite <-rpci, <-addwA; econstructor.
destruct E as (? & ? & ?).
by solve_pc rpci.

(* Syscall *)

(* Malloc *)
  move: b Heqo E0 E1 E2 => bi Heqo E0 E1 E2.
  case: (rist)=> fresh_color [in_bl [no_overlap [cover]]].
  move/(_ bi _).
  have: bi \in [seq x <- info
              | (val <= Sym.block_size x)%ord
              & Sym.block_color x == None].
    case: [seq x <- info
              | (val <= Sym.block_size x)%ord
              & Sym.block_color x == None] Heqo => //= ? ? [->].
    by rewrite inE eqxx.
  rewrite mem_filter => /andP [/andP [lt_val /eqP color_bi in_bi]].
  rewrite in_bi => /(_ erefl) biP.
  case: biP Heqo E0 color_bi in_bi lt_val; first by move=> *; congruence.
  move=> _ [? ?] FREE Heqo E0 color_bi in_bi lt_val.


  case malloc: (Abstract.malloc_fun a_mem bl val) => [amem' newb].
  pose mi' := mi_malloc mi newb (Sym.block_base bi) color.
  have rnewb: refine_val mi' (Abstract.VPtr (newb, 0)) (Sym.block_base bi) (PTR color).
    rewrite -[Sym.block_base bi]addw0; constructor.
    by rewrite /mi' /mi_malloc getm_set eqxx.

  move/(refine_registers_malloc (Sym.block_base bi) fresh_color malloc): rregs => rregs.
  eapply (refine_registers_upd rregs rnewb) in E2.
  destruct E2 as (? & ? & ?).

  eexists; exists (mi_malloc mi newb (Sym.block_base bi) color); split.
  eapply Abstract.step_malloc.
  by eauto.
  by eauto.
  by eauto.
  by eauto.

  split; try eassumption.
  exact: (refine_memory_malloc rmem rist malloc).
  exact: (refine_val_malloc _ fresh_color malloc).
  have int_val : 0 < val <= Sym.block_size bi by apply/andP; split; eauto.
  exact: (refine_internal_state_malloc int_val malloc).

(* Free *)

  have ? := @leZ_max (Sym.block_size x).
  case: (rist)=> fresh_color [in_bl [no_overlap [cover]]].
  move/(_ x _).
  have: x \in [seq x0 <- info | Sym.block_color x0 == Some s].
    case: [seq x0 <- info | Sym.block_color x0 == Some s] E => //= ? ? [->].
    by rewrite inE eqxx.
  rewrite mem_filter => /andP [/eqP color_x in_x].
  rewrite in_x => /(_ erefl) biP.
  case: biP E E0 E1 color_x in_x => [|->] //.
  move=> col b color_bi [? ?] mi_col get_x E E0 E1 color_x in_x.
  case/andP: E1 => lb_val ub_val.
  rewrite (lock addw) /= -!val_ordE /= /Ord.leq /= -lock in ub_val.
  rewrite valw_add' // -ltnNge in ub_val.
  have /andP [E1 E2]:
    Sym.block_base x <= val < Sym.block_base x + Sym.block_size x.
    by apply/andP.
  have [fr get_b]: exists fr, a_mem b = Some fr.
    case/(_ (val - Sym.block_base x)): get_x => [|w' [ty]].
      by rewrite valw_sub // -(ltn_add2r (Sym.block_base x)) subnK // addnC.
    case: rmem => _ rmem.
    move/rmem.
    rewrite mi_col /Abstract.getv /=.
    by case: (a_mem b) => // fr _; exists fr.
  have eq_col: col = s by congruence.
  have eq_s4b: s2 = b.
    inversion H3.
    by rewrite eq_col H8 in mi_col; injection mi_col.

  case: (Abstract.free_Some get_b)=> ? free_b.

  eexists; eexists; split.
  eapply Abstract.step_free.
  by eauto.
  by rewrite eq_s4b.
  by eauto.

  case: (refine_memory_free rmem rist in_x color_bi mi_col free_b E0) => rmem' rist'.
  by split; eassumption.

(* Base *)
  case: (rist)=> fresh_color [in_bl [no_overlap [cover]]].
  move/(_ x _).
  have: x \in [seq x0 <- info | Sym.block_color x0 == Some s].
    case: [seq x0 <- info | Sym.block_color x0 == Some s] E=> //= ? ? [->].
    by rewrite inE eqxx.
  rewrite mem_filter => /andP [/eqP color_x ->] /(_ erefl) biP.
  case: biP E E0 color_x => [|-> //].
  move=> col b color_x [? ?] mi_col get_x ? E0 ?.
  have eq_col: col = s by congruence.
  have eq_s4b: s2 = b.
    inversion H3.
    by rewrite eq_col H8 in mi_col; injection mi_col.

rewrite -eq_col -[Sym.block_base x]addw0 in E0.
  eapply (refine_registers_upd rregs) in E0; last exact: (RefinePtr _ mi_col).
  case: E0=> ? [upd_ret ?].

  eexists; eexists; split.
  eapply Abstract.step_base.
  by eauto.
  by rewrite eq_s4b.
  by eauto.

  by split; eassumption.

(* Eq *)

  (* match_inv doesn't seem to be handling the commutative cut *)
  case: ptr1 CALL E0 => // arg1v [[|arg1b]||] // CALL E0.
  match_inv.

  case/(refine_registers_get rregs): CALL=> arg1 [rarg1 ?].
  case/(refine_registers_get rregs): E=> arg2 [rarg2 ?].
  case/(refine_registers_get_ptr rregs): E1=> ? [? ?].
  eapply (refine_registers_upd rregs) in E0; last by eauto.
  case: E0=> ? [upd_ret ?].

  eexists; eexists; split.
  eapply Abstract.step_eq.
  by eauto.
  by eauto.
  rewrite /Abstract.value_eq.
  move: upd_ret.
  inversion rarg1.
  inversion rarg2.

  have [eq_arg1b|neq_arg1b] := altP (arg1b =P s).
    move: H4 H8; rewrite eq_arg1b => -> [-> ->].
    have -> /= : (base0 + off == base0 + off0) = (off == off0).
      by apply/inj_eq/GRing.addrI.
    rewrite [in bool_to_word _]eqE /= eqxx /=.
    by case: (_ == _).
  rewrite [in bool_to_word _]eqE /=.
  have/negbTE->//: b != b0.
    apply/eqP=> eq_b; rewrite eq_b in H4 H8.
    by rewrite (miIr miP H4 H8) eqxx in neq_arg1b.
  by eauto.

  by split; eassumption.

move: CALL.
rewrite /= /Symbolic.run_syscall /=.
case: (Symbolic.entry_tag sc) => // b [] //.
by case: ifP.
Qed.

End refinement.
