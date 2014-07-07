Require Import ZArith.
Ltac type_of x := type of x.

Require Import lib.Coqlib.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import lib.utils lib.partial_maps common.common symbolic.symbolic.
Require Import memory_safety.abstract memory_safety.symbolic.
Require Import memory_safety.classes.

Require Import ordered.

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

Open Scope Z_scope.

Notation "x <? y <? z" := ((x <? y) && (y <? z))
  (at level 70, y at next level, no associativity) : Z_scope.
Notation "x <? y <=? z" := ((x <? y) && (y <=? z))
  (at level 70, y at next level, no associativity) : Z_scope.
Notation "x <=? y <? z" := ((x <=? y) && (y <? z))
  (at level 70, y at next level, no associativity) : Z_scope.
Notation "x <=? y <=? z" := ((x <=? y) && (y <=? z))
  (at level 70, y at next level, no associativity) : Z_scope.

Section refinement.


Open Scope word_scope.

Import Sym.Notations.

Variable block : eqType.

Context {mt : machine_types}
        {ops : machine_ops mt}
        {opss : machine_ops_spec ops}
        {ap : Abstract.abstract_params block}
        {aps : Abstract.params_spec ap}.
(*
        {a_alloc : @Abstract.allocator _ block ap}
        {qa_alloc : @Sym.allocator _ qap}
        {a_allocP : Abstract.allocator_spec a_alloc}.
*)

Context `{syscall_regs mt} `{a_alloc : @Abstract.allocator mt block ap}
         {a_allocP : Abstract.allocator_spec a_alloc}
        `{@memory_syscall_addrs mt}.

Notation meminj := (@word_map mt (block * (word mt) (* base *))).

Lemma binop_addDl : forall x y z,
  binop_denote ADD (x + y) z = x + (binop_denote ADD y z).
Proof.
  move => x y z /=.
  by rewrite addwA.
Qed.

Lemma binop_addDr : forall x y z,
  binop_denote ADD x (y + z) = y + (binop_denote ADD x z).
Proof.
  move => x y z /=.
  rewrite addwA.
  rewrite (addwC x y).
  by rewrite addwA.
Qed.

Lemma binop_subDl : forall x y z,
  binop_denote SUB (x + y) z = x + (binop_denote SUB y z).
Proof.
  move => x y z /=.
  by rewrite addwA.
Qed.

Lemma binop_sub_add2l : forall x y z,
  binop_denote SUB (x + y) (x + z) = (binop_denote SUB y z).
Proof.
  move => x y z /=.
  have ->: (opp_word (x + z) = opp_word x - z).
  { rewrite <- (add0w (opp_word x + _)).
    rewrite <- (addNw (x + z)) at 1.
    rewrite (addwC (opp_word x) (opp_word z)).
    do ! rewrite <- addwA.
    rewrite (addwA z _ (opp_word x)).
    by rewrite addwN add0w addwN addw0. }
  rewrite (addwC x y).
  rewrite addwA.
  rewrite <- (addwA y x _).
  by rewrite addwN addw0.
Qed.

Lemma binop_eq_add2l : forall x y z,
  binop_denote EQ (x + y) (x + z) = binop_denote EQ y z.
Proof.
  move => x y z /=.
  f_equal.
  have [->|/eqP NEQ] := altP (y =P z); first by rewrite eqxx.
  have [EQ|//] := altP (x + y =P x + z).
  contradict NEQ.
  rewrite <- add0w. rewrite <- (addNw x).
  rewrite <- addwA. rewrite EQ. rewrite addwA.
  rewrite addNw. apply add0w.
Qed.

Lemma leZ_min w : word_to_Z min_word <= word_to_Z w.
Proof.
rewrite /Z.le -word_to_Z_compare.
exact: lew_min.
Qed.

Lemma leZ_max w : word_to_Z w <= word_to_Z max_word.
Proof.
rewrite /Z.le -word_to_Z_compare.
exact: lew_max.
Qed.

(* How to make w explicit ??? *)
(* TODO: File a bug report *)
Arguments leZ_min.
Arguments leZ_max.

Lemma ltwSw : forall w,
  (w < max_word -> w < w + 1)%ordered.
Admitted.

Section memory_injections.

(*
Definition size amem pt :=
  match PartMaps.get amem pt with
  | None => 0%Z
  | Some fr => Z.of_nat (length fr)
  end.
*)

(* if b is allocated, mi b returns Some (w1,w2) where
     - w1 is the address of b's first memory location
     - w2 is b's pointer nonce
  *)
Record meminj_spec (amem : Abstract.memory mt) (mi : meminj) := {
    miIr : forall b col col' base base',
                PartMaps.get mi col = Some (b, base) ->
                PartMaps.get mi col' = Some (b, base') ->
                col = col'

    (* Blocks are non overlapping: *)
(*
    mi_disjoints : forall b b' base base' nonce nonce' off off' fr fr',
      mi b = Some (base,nonce) ->
      mi b' = Some (base',nonce') ->
      PartMaps.get amem b = Some fr ->
      PartMaps.get amem b' = Some fr' ->
      base + off = base' + off' ->
      word_to_Z off < Z.of_nat (length fr) ->
      word_to_Z off' < Z.of_nat (length fr') ->
      b = b'
*)
  }.

(* We could generalize update_list_Z to any size-preserving operator *)
Lemma meminj_update mi amem amem' b off fr fr' x :
  meminj_spec amem mi ->
  PartMaps.get amem b = Some fr ->
  update_list_Z off x fr = Some fr' ->
  PartMaps.upd amem b fr' = Some amem' ->
  meminj_spec amem' mi.
Proof.
move=> miP get_b upd_off upd_b.
constructor; first exact: miIr miP.
(*
move=> b1 b1' base base' nonce nonce' off1 off1' fr1 fr1'.
have [->|/eqP neq_b1b] := altP (b1 =P b);
have [->//|/eqP neq_b1'b] := altP (b1' =P b);
rewrite ?(PartMaps.get_upd_eq upd_b) !(PartMaps.get_upd_neq _ upd_b) //.
+ move=> mi_b1 mi_b1' [<-]; rewrite (length_update_list_Z upd_off).
  exact: (mi_disjoints miP mi_b1 mi_b1').
  move=> mi_b1 mi_b1' get_b1 [<-]; rewrite (length_update_list_Z upd_off).
  exact: (mi_disjoints miP mi_b1 mi_b1').
+ exact: mi_disjoints.
*)
Qed.

Hint Resolve meminj_update.

Variable amem : Abstract.memory mt.
Variable mi : meminj.

Definition ohrel (A B : Type) (rAB : A -> B -> Prop) sa sb : Prop :=
  match sa, sb with
    | None,   None   => True
    | Some a, Some b => rAB a b
    | _,      _      => False
  end.

Inductive refine_val : Abstract.value mt block -> word mt -> Sym.type mt -> Prop :=
  | RefineData : forall w, refine_val (Abstract.VData _ w) w DATA
  | RefinePtr : forall b base col off, PartMaps.get mi col = Some (b,base) ->
                refine_val (Abstract.VPtr (b,off)) (base + off) (PTR col).

Lemma refine_ptr_inv w col b b' off base :
  meminj_spec amem mi ->
  refine_val (Abstract.VPtr (b,off)) w (PTR col) ->
  PartMaps.get mi col = Some (b', base) ->
  w = (base + off)%w.
Proof.
move=> miP rpt mi_b.
inversion rpt.
congruence.
Qed.

Definition refine_memory amem (smem : Sym.memory mt) :=
  meminj_spec amem mi /\ forall w1 w2 col ty,
  PartMaps.get smem w1 = Some w2@M(col,ty) ->
  if PartMaps.get mi col is Some (b,base) then
  if Abstract.getv amem (b, w1 - base) is Some v then
  refine_val v w2 ty else False else False.

Lemma refine_memory_get_int qamem (w1 w2 w3 : word mt) pt :
         refine_memory amem qamem -> refine_val (Abstract.VPtr pt) w1 (PTR w2) ->
         PartMaps.get qamem w1 = Some w3@M(w2,DATA) ->
         Abstract.getv amem pt = Some (Abstract.VData _ w3).
Proof.
move=> [miP rmem] rpt get_w1.
move/(_ _ _ _ _ get_w1): rmem.
inversion rpt.
rewrite H4.
rewrite [base+off]addwC addwK.
case: (Abstract.getv amem (b, off)) => // v rvw3.
by inversion rvw3.
Qed.

Lemma getv_mem base off v : Abstract.getv amem (base, off) = Some v ->
  exists fr, PartMaps.get amem base = Some fr
  /\ index_list_Z (word_to_Z off) fr = Some v.
Proof.
unfold Abstract.getv; simpl.
destruct (PartMaps.get amem base) as [fr|]; try discriminate.
by intros index_fr; exists fr; split.
Qed.

Lemma get_mem_memv base off v fr : PartMaps.get amem base = Some fr ->
  index_list_Z (word_to_Z off) fr = Some v ->
  Abstract.getv amem (base,off) = Some v.
Proof.
intros get_base index_off.
unfold Abstract.getv.
by simpl; rewrite get_base.
Qed.

Lemma refine_memory_get smem (w1 w2 w3 : word mt) pt ty :
         refine_memory amem smem -> refine_val (Abstract.VPtr pt) w1 (PTR w2) ->
         PartMaps.get smem w1 = Some (w3@M(w2,ty)) ->
         exists fr x, PartMaps.get amem (fst pt) = Some fr
         /\ index_list_Z (word_to_Z (snd pt)) fr = Some x
         /\ refine_val x w3 ty.
Proof.
move=> [miP rmem] rpt get_w1.
move/(_ _ _ _ _ get_w1): rmem.
inversion rpt.
rewrite H4.
rewrite [base+off]addwC addwK.
rewrite /Abstract.getv.
case: (PartMaps.get amem b) => // fr get_off.
exists fr; move: get_off.
case: (index_list_Z (word_to_Z off) fr) => // v rvw3.
by exists v.
Qed.

Definition bounded_add w1 w2 :=
  word_to_Z min_word <= word_to_Z w1 + word_to_Z w2 <= word_to_Z max_word.

Inductive block_info_spec (smem : Sym.memory mt) (bi : Sym.block_info mt) : Prop :=
| BlockInfoLive : forall col b, Sym.block_color bi = Some col ->
  bounded_add (Sym.block_base bi) (Sym.block_size bi) ->
  PartMaps.get mi col = Some (b, Sym.block_base bi) ->
  (forall off, 0 <= word_to_Z off < word_to_Z (Sym.block_size bi) ->
     exists v ty, PartMaps.get smem (Sym.block_base bi + off) = Some v@M(col,ty)) ->
  block_info_spec smem bi
| BlockInfoFree :
  Sym.block_color bi = None ->
  bounded_add (Sym.block_base bi) (Sym.block_size bi) ->
  (forall off, 0 <= word_to_Z off < word_to_Z (Sym.block_size bi) ->
    exists v, PartMaps.get smem (Sym.block_base bi + off) = Some v@FREE) ->
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
  forall col' b base, PartMaps.get mi col' = Some (b,base) ->
  (col' < col)%ordered.

Definition overlap (bi1 bi2 : Sym.block_info mt) (w : word mt) :=
  word_to_Z (Sym.block_base bi1) <= word_to_Z w < word_to_Z (Sym.block_base bi1) + word_to_Z (Sym.block_size bi1) /\
  word_to_Z (Sym.block_base bi2) <= word_to_Z w < word_to_Z (Sym.block_base bi2) + word_to_Z (Sym.block_size bi2).

Definition refine_internal_state (bl : list block) smem (ist : word mt * list (Sym.block_info mt)) :=
  let: (col, info) := ist in
  fresh_color col /\
  (forall col b base, PartMaps.get mi col = Some (b,base) -> b \in bl) /\
  (forall i j def w, i < size info -> j < size info ->
     overlap (nth def info i) (nth def info j) w -> i = j)%N /\
  forall bi, bi \in info -> block_info_spec smem bi.

Lemma refine_memory_upd bl smem smem' ist old
                        w1 w2 pt ty ty' n fr fr' x :
  refine_memory amem smem ->
  refine_internal_state bl smem ist ->
  refine_val (Abstract.VPtr pt) w1 (PTR n) ->
  PartMaps.get smem w1 = Some old@M(n, ty') ->
  PartMaps.upd smem w1 w2@M(n, ty) = Some smem' ->
  PartMaps.get amem pt.1 = Some fr ->
  update_list_Z (word_to_Z pt.2) x fr = Some fr' ->
  refine_val x w2 ty ->
    exists amem', [/\ PartMaps.upd amem pt.1 fr' = Some amem',
      refine_memory amem' smem' & refine_internal_state bl smem' ist].
Proof.
case: ist => nextcol infos.
move=> [miP rmem] [freshcol [in_bl [no_overlap rist]]] rpt get_w1 upd_w1.
move=> get_pt update_pt rx.
destruct (PartMaps.upd_defined fr' get_pt) as [amem' upd_pt].
exists amem'; split => //; last first.
  split => //; split => //; split => //.
  case=> bi_base bi_size [bi_col in_bi|in_bi]; last first.
    move/(_ _ in_bi): rist => biP.
    inversion biP => //.
    apply: BlockInfoFree => //=.
    move=> off lt_off.
    case/(_ off lt_off): H3 => v /=.
    have [->|/eqP neq_w1] := altP (bi_base + off =P w1).
       by rewrite get_w1.
    by rewrite (PartMaps.get_upd_neq neq_w1 upd_w1); move => ?; exists v.
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
      by move=> _; rewrite (PartMaps.get_upd_eq upd_w1); eexists; eexists.
    have neq_w1 : bi_base + off <> bi_base + pt_off.
      by move/addwI.
    by rewrite (PartMaps.get_upd_neq neq_w1 upd_w1) => ?; eexists; eexists.
  move/(_ _ in_bi): rist => biP.
  inversion biP => //=.
  case: H1 => eq_col.
  rewrite -eq_col in H3 H4.
  apply: (BlockInfoLive _ H2 H3) => //.
  move=> off lt_off.
  case/(_ off lt_off): H4 => v [ty''].
  have [->|/eqP neq_w1] := altP (bi_base + off =P w1).
    by rewrite get_w1 => [[_ eq_coln _]]; rewrite eq_coln eqxx in neq_coln.
  by rewrite (PartMaps.get_upd_neq neq_w1 upd_w1); move => ?; eexists; eexists.
split; first by constructor; case: miP.
move=> w0 w3 col ?.
have [->|/eqP neq_w0w1] := altP (w0 =P w1).
  rewrite (PartMaps.get_upd_eq upd_w1) => [[<- <- <-]].
  inversion rpt.
  rewrite H4 [base+off]addwC addwK H1.
  rewrite /Abstract.getv.
  rewrite (PartMaps.get_upd_eq upd_pt).
  by rewrite (update_list_Z_spec update_pt).
rewrite (PartMaps.get_upd_neq neq_w0w1 upd_w1).
move=> get_w0.
move/(_ _ _ _ _ get_w0): rmem.
inversion rpt.
rewrite -H1 /= in get_pt upd_pt update_pt.
have [->|neq_coln] := altP (col =P n).
  rewrite H4 /Abstract.getv /=.
  rewrite get_pt (PartMaps.get_upd_eq upd_pt).
  have neq_off: word_to_Z (w0 - base) <> word_to_Z off.
    move/word_to_Z_inj => eq_off.
    by rewrite -eq_off addwC addwNK in H3.
  by rewrite (update_list_Z_spec2 update_pt neq_off).
case mi_col: (PartMaps.get mi col) => [[b' base']|] //.
rewrite /Abstract.getv /=.
have neq_b: b' <> b.
  move=> eq_bb'.
  rewrite eq_bb' in mi_col.
  by rewrite (miIr miP mi_col H4) eqxx in neq_coln.
by rewrite (PartMaps.get_upd_neq neq_b upd_pt).
Qed.

Definition mi_malloc b base col : meminj :=
  PartMaps.set mi col (b,base).

Lemma get_write_block_rec:  forall base v n init w, 
(*  word_to_Z base + Z.of_nat n <= word_to_Z max_word -> *)
  PartMaps.get (Sym.write_block_rec init base v n) w =
  if (word_to_Z base <=? word_to_Z w <? word_to_Z base + (Z.of_nat n))%Z then Some v else PartMaps.get init w.
Proof.
  induction n; intros. 
  - simpl. 
    have [inb|_] := boolP (base <=? w <? base + 0)%ordered.
    replace (base + 0) with base in inb by (rewrite addw0; auto). admit. (* inb is imposible *)
    auto. 
  - admit.
admit.
Qed.

Lemma get_write_block: forall smem base sz v w mem',
(*  (0 <= sz)%ordered ->*)
  Sym.write_block smem base v sz = Some mem' ->                          
  PartMaps.get mem' w = if (word_to_Z base <=? word_to_Z w <? word_to_Z base + word_to_Z sz)%Z then Some v else PartMaps.get smem w.
Proof.
(*
  unfold Sym.write_block.
  intros. revert H2. 
  assert (0 <= word_to_Z sz). 
    apply word_to_Z_le in H1.
    rewrite Z_to_wordK in H1.  auto. split. apply min_word_bound. pose proof max_word_bound. omega. 
  have [rep|nrep] := boolP (word_to_Z base + word_to_Z sz <=? word_to_Z max_word).
  intro. inversion H3; subst; clear H3. 
  erewrite get_write_block_rec. rewrite Z2Nat.id; auto. rewrite word_to_ZK;  auto.
  rewrite Z2Nat.id; auto.
  intro X; inversion X.
*)
admit.
Qed. 

Lemma refine_memory_free (amem' : Abstract.memory mt) (smem smem' : Sym.memory mt) bl nc info b bi col :
  refine_memory amem smem ->
  refine_internal_state bl smem (nc, info) ->
  bi \in info ->
  Sym.block_color bi = Some col ->
  PartMaps.get mi col = Some (b, Sym.block_base bi) ->
  Abstract.free_fun amem b = Some amem' ->
  Sym.write_block smem (Sym.block_base bi) 0@FREE (Sym.block_size bi) = Some smem' ->
  refine_memory amem' smem' /\
  refine_internal_state bl smem'
     (nc,
     set_nth (@Sym.def_info mt ops) info (index bi info)
       {|
       Sym.block_base := Sym.block_base bi;
       Sym.block_size := Sym.block_size bi;
       Sym.block_color := None |}).
Proof.
move=> [miP rmem] rist in_bi color_bi mi_col free_b write_block; split.
  split; first by constructor; apply miP.
  move=> w1 w2 col' ty.
  rewrite (get_write_block _ write_block) => //.
  case: ifP => // _.
  admit.
  admit.
Qed.

(*
  PartMaps.get amem b = Some amem' ->
  refine_memory mi amem'
     (nat_rect (fun _ : nat => Sym.memory mt) mem
        (fun (n : nat) (acc : Sym.memory mt) =>
         match
           PartMaps.upd acc (Sym.block_base x + Z_to_word (Z.of_nat n))
             0@(Sym.TagFree mt)
         with
         | Some mem0 => mem0
         | None => acc
         end) (Z.to_nat (word_to_Z (Sym.block_size x))))


                        w1 w2 pt ty n fr fr' x :
  refine_memory amem smem ->
  refine_internal_state amem smem ist ->
  refine_val (Abstract.VPtr pt) w1 (PTR n) ->
  PartMaps.upd smem w1 w2@M(n, ty) = Some smem' ->
  PartMaps.get amem (fst pt) = Some fr ->
  update_list_Z (word_to_Z (snd pt)) x fr = Some fr' ->
  refine_val x w2 ty ->
    exists amem', [/\ PartMaps.upd amem (fst pt) fr' = Some amem',
      refine_memory amem' smem' & refine_internal_state amem' smem' ist].
*)

Definition refine_reg_val v a :=
 match a with w@V(ty) => refine_val v w ty | _ => False end.

Definition refine_registers (aregs : Abstract.registers mt)
                            (qaregs : Sym.registers mt) :=
  PartMaps.pointwise refine_reg_val aregs qaregs.

Lemma refine_registers_val aregs qaregs r v : refine_registers aregs qaregs ->
  PartMaps.get qaregs r = Some v ->
  exists w ty, v = w@V(ty).
Proof.
intros rregs get_r; specialize (rregs r); revert rregs.
rewrite get_r; destruct (PartMaps.get aregs r); try easy.
by destruct v as [w [ty | |]]; try easy; exists w; exists ty.
Qed.

Lemma refine_registers_get aregs qaregs (n : common.reg mt) w ty :
  refine_registers aregs qaregs ->
  PartMaps.get qaregs n = Some w@V(ty) ->
  exists x, refine_val x w ty /\ PartMaps.get aregs n = Some x.
Proof.
intros rregs qa_get.
generalize (rregs n).
rewrite qa_get.
destruct (PartMaps.get aregs n); try easy.
simpl; intros rvx.
by exists v; split.
Qed.

Lemma refine_registers_get_int aregs qaregs (n : common.reg mt) w :
  refine_registers aregs qaregs ->
  PartMaps.get qaregs n = Some w@V(DATA) ->
    refine_val (Abstract.VData _ w) w DATA /\
    PartMaps.get aregs n = Some (Abstract.VData _ w).
Proof.
intros rregs get_n.
specialize (rregs n).
rewrite get_n in rregs.
destruct (PartMaps.get aregs n); try contradiction.
by inversion rregs; split; first by constructor.
Qed.

Lemma refine_registers_get_ptr aregs qaregs (n : common.reg mt) w b :
  refine_registers aregs qaregs ->
  PartMaps.get qaregs n = Some w@V(PTR b) ->
  exists pt, refine_val (Abstract.VPtr pt) w (PTR b) /\
    PartMaps.get aregs n = Some (Abstract.VPtr pt).
Proof.
intros rregs qa_get.
generalize (rregs n).
rewrite qa_get.
destruct (PartMaps.get aregs n); try easy.
simpl; intros rvx.
destruct v as [|pt].
  by inversion rvx.
by exists pt; split.
Qed.

Lemma refine_registers_upd aregs qaregs qaregs' r v w ty :
  refine_registers aregs qaregs ->
  refine_val v w ty ->
  PartMaps.upd qaregs r w@V(ty) = Some qaregs' ->
  exists areg',
    PartMaps.upd aregs r v = Some areg' /\
    refine_registers areg' qaregs'.
Proof.
intros rregs rvw upd_r_qa.
assert (ref_r := rregs r).
destruct (PartMaps.upd_inv upd_r_qa) as [v' get_r_qa].
rewrite get_r_qa in ref_r.
destruct (PartMaps.get aregs r) as [w'|] eqn:get_r_a; try contradiction.
destruct (PartMaps.upd_defined v get_r_a) as [aregs' upd_r_a].
exists aregs'; split; try easy.
intros r'.
have [->|/eqP neq_rr'] := altP (r' =P r).
  rewrite (PartMaps.get_upd_eq upd_r_a).
  by rewrite (PartMaps.get_upd_eq upd_r_qa).
rewrite (PartMaps.get_upd_neq neq_rr' upd_r_a).
rewrite (PartMaps.get_upd_neq neq_rr' upd_r_qa).
by apply rregs.
Qed.

Definition refine_state (ast : Abstract.state mt) (sst : @Symbolic.state mt (Sym.sym_memory_safety mt)) :=
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
  by move=> eq_col; move/fresh_col: mi_b; rewrite eq_col; apply: lt_irrefl.
by rewrite (PartMaps.get_set_neq _ _ neq_col).
Qed.


Lemma refine_registers_malloc mi aregs sregs amem amem' bl sz newb base col :
  fresh_color mi col -> 
  Abstract.malloc_fun amem bl sz = (amem', newb) ->
  refine_registers mi aregs sregs ->
  refine_registers (mi_malloc mi newb base col) aregs sregs.
Proof.
  intros.
  unfold refine_registers. unfold mi_malloc.
  eapply PartMaps.refine_extend_map with 
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
+ rewrite (PartMaps.get_set_neq _ _ neq_col'').
  rewrite PartMaps.get_set_eq => [[<- _]] /in_bl.
  by rewrite (negbTE (Abstract.malloc_fresh malloc)).
+ rewrite (PartMaps.get_set_neq _ _ neq_col').
  rewrite PartMaps.get_set_eq => get_col' [eq_b _].
  move/in_bl: get_col'.
  by rewrite -eq_b (negbTE (Abstract.malloc_fresh malloc)).
+ rewrite (PartMaps.get_set_neq _ _ neq_col') (PartMaps.get_set_neq _ _ neq_col'').
exact: (miIr miP).
Qed.

Lemma refine_memory_malloc mi amem smem amem' info bl sz newb base col smem' :
  refine_memory mi amem smem ->
  (0 <= sz)%ordered -> 
  refine_internal_state mi bl smem (col, info) ->
  Abstract.malloc_fun amem bl sz = (amem', newb) ->
  Sym.write_block smem base 0@M(col, DATA) sz = Some smem' -> 
  refine_memory (mi_malloc mi newb base col) amem' smem'.
Proof.
case=> miP rmem sznneg rist malloc.
case: (rist) => [fresh_col [in_bl [no_overlap biP]]].

split; first exact: (meminj_spec_malloc _ rist malloc).
move=> w1 w2 col' ty.
rewrite (get_write_block _ H1).
have [/andP [/Z.leb_le ? /Z.ltb_lt ?] [<- <- <-]|_ /rmem get_w1] :=
  boolP (word_to_Z base <=? word_to_Z w1 <? word_to_Z base + word_to_Z sz)%Z.
  rewrite PartMaps.get_set_eq (Abstract.malloc_get malloc); last first.
  have ? := @leZ_max sz.
  generalize min_word_bound => min_bound.
  by apply/word_to_Z_lt; rewrite subwE; omega.
  apply: (refine_val_malloc _ fresh_col malloc).
  by constructor.
have neq_col: col' <> col.
  move=> eq_col.
  move: get_w1; rewrite eq_col.
  move: (fresh_col col).
  case: (PartMaps.get mi col) => // [[b' base']] /(_ b' base' erefl) lt_col.
  by apply lt_irrefl in lt_col.

move: get_w1.
set mi' := mi_malloc _ _ _ _.
have mi'P := (meminj_spec_malloc base rist malloc miP).
have eq_mi: PartMaps.get mi' col' = PartMaps.get mi col'.
  by rewrite (PartMaps.get_set_neq _ _ neq_col).
rewrite eq_mi; move: eq_mi.
case: (PartMaps.get mi col') => // [[b' base']] mi'_col'.
have neq_b': b' <> newb.
  move=> eq_b'; rewrite eq_b' in mi'_col'.
  have mi'_col: PartMaps.get mi' col = Some (newb, base).
    by rewrite PartMaps.get_set_eq.
  exact/neq_col/(miIr mi'P mi'_col' mi'_col).
rewrite /Abstract.getv (Abstract.malloc_get_neq malloc neq_b').
case: (PartMaps.get amem b') => // fr.
case: (index_list_Z (word_to_Z (w1 - base'))) => // v.
by move=> rvw2; apply: (refine_val_malloc _ fresh_col malloc).
Qed.

Lemma refine_internal_state_malloc mi amem amem' bl smem info sz newb bi color smem' :
  (0 <= word_to_Z sz <= word_to_Z (Sym.block_size bi)) ->
  Abstract.malloc_fun amem bl sz = (amem', newb) ->
  (color < max_word)%ordered ->
  Sym.block_color bi = None ->
  bi \in info ->
  refine_internal_state mi bl smem (color, info) ->
  Sym.write_block smem (Sym.block_base bi) 0@M(color, DATA) sz = Some smem' -> 
  refine_internal_state (mi_malloc mi newb (Sym.block_base bi) color)
    (newb :: bl) smem' (color + 1, Sym.update_block_info info bi color sz).
Proof.
move=> [nneg_sz le_sz] malloc lt_color color_bi in_bi.
case=> [fresh_color [in_bl [no_overlap biP]]] write_bi.
have [? ?] := block_info_bounds (biP _ in_bi).
have ? := @leZ_min (Sym.block_base bi).
have ? := @leZ_max (Sym.block_size bi).
generalize min_word_bound => min_bound.
generalize max_word_bound => max_bound.
split. (* freshness of color *)
  rewrite /refinement.fresh_color.
  move=> col b base.
  have [-> _|neq_col] := col =P color.
    exact: ltwSw.
  rewrite (PartMaps.get_set_neq _ _ neq_col).
  move/fresh_color => lt_col.
  apply: (lt_trans col color) => //.
  exact: ltwSw.
split. (* list of block is complete *)
  move=> col b base.
  have [->|neq_col] := col =P color.
    by rewrite PartMaps.get_set_eq => [[<- _]]; rewrite inE eqxx.
  by rewrite (PartMaps.get_set_neq _ _ neq_col) inE => /in_bl ->; rewrite orbT.
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
  rewrite !nth_set_nth /=.
  + have [->|neq_j] := j =P index bi info.
      rewrite /overlap /=.
      case=> [[ge_w _] [_ lt_w]].
      rewrite addwE in ge_w; omega.
    case=> /= [[ge_w lt_w] ?].
    rewrite addwE in ge_w; last omega.
    case: neq_j; apply: (no_overlap _ _ newbi w) => //.
      by rewrite index_mem.
    rewrite nth_index // /overlap; split=> //.
    by rewrite addwE ?subwE in lt_w; omega.
  + have [->|neq_i] := i =P index bi info.
      rewrite /overlap /=.
      case=> [[_ lt_w] [ge_w _]].
      by rewrite addwE in ge_w; omega.
    case=> /= [? [ge_w lt_w]].
    case: neq_i; apply: (no_overlap _ _ newbi w) => //.
      by rewrite index_mem.
    rewrite nth_index // /overlap; split=> //.
    rewrite addwE in ge_w; last omega.
    by rewrite addwE ?subwE in lt_w; omega.
  + have [->|neq_i] := i =P index bi info;
    have [->|neq_j] := j =P index bi info => //=.
    * case=> /= [in_newbi in_j].
      congr S.
      apply: (no_overlap _ _ newbi w) => //.
        by rewrite index_mem.
      rewrite nth_index //; split=> //; omega.
    * case=> /= [in_i in_newbi]; congr S.
      apply: (no_overlap _ _ newbi w) => //.
        by rewrite index_mem.
      rewrite nth_index //; split=> //; omega.
    * by move/(no_overlap _ _ _ _ lt_i lt_j)->.
rewrite /Sym.update_block_info.
move=> bi'.
have ? := @leZ_min (Sym.block_base bi').
have ? := @leZ_max (Sym.block_size bi').
set mi' := mi_malloc _ _ _ _.
set newbi := Sym.mkBlockInfo _ _ _.
have [eq_sz|_] := sz =P Sym.block_size bi.
  case/(nthP newbi) => i.
  rewrite size_set_nth (maxn_idPr _) ?index_mem // => lt_i.
  rewrite nth_set_nth /=.
  have [eq_i <-|neq_i] := i =P index bi info.
    (* Showing invariant for the new block *)
    apply: (@BlockInfoLive _ _ _ color newb) => //.
    * by rewrite /bounded_add /=; omega.
    * by rewrite PartMaps.get_set_eq.
    * move=> off /= lt_off.
    rewrite (get_write_block _ write_bi) => //.
  have [/Z.leb_le -> /Z.ltb_lt -> /=]:
    word_to_Z (Sym.block_base bi) <=
         word_to_Z (Sym.block_base bi + off) <
         (word_to_Z (Sym.block_base bi) + word_to_Z sz)%Z.
    by split; rewrite addwE; omega.
  by eexists; eexists.
  (* Showing that invariant is preserved for other blocks *)
  move=> nth_i; move: (biP bi'); rewrite -nth_i mem_nth // nth_i.
  move/(_ erefl) => bi'P.
  case: bi'P.
    move=> col b color_bi' [? ?] mi_col get_bi'.
    apply: (@BlockInfoLive _ _ _ col b) => //.
      have neq_col: col <> color.
        by move=> eq_col; move/fresh_color: mi_col; rewrite eq_col; apply: lt_irrefl.
      by rewrite (PartMaps.get_set_neq _ _ neq_col).
    move=> off lt_off.
    rewrite (get_write_block _ write_bi) => //.
    have [/andP [/Z.leb_le ? /Z.ltb_lt ?]|] :=
      boolP (word_to_Z (Sym.block_base bi) <=?
             word_to_Z (Sym.block_base bi' + off) <?
             word_to_Z (Sym.block_base bi) + word_to_Z sz).
      case: neq_i; apply: (no_overlap _ _ newbi (Sym.block_base bi' + off) lt_i).
        by rewrite index_mem.
      rewrite nth_i nth_index //; split.
        by rewrite addwE; omega.
      rewrite -eq_sz.
      omega.
    by move=> _; apply: get_bi'.
  move=> color_bi' [? ?] get_bi'.
  apply: BlockInfoFree => //.
  move=> off bounds_off.
  rewrite (get_write_block _ write_bi) //.
  have [/andP [/Z.leb_le ? /Z.ltb_lt ?]|] :=
      boolP (word_to_Z (Sym.block_base bi) <=?
             word_to_Z (Sym.block_base bi' + off) <?
             word_to_Z (Sym.block_base bi) + word_to_Z sz).
    case: neq_i; apply: (no_overlap _ _ newbi (Sym.block_base bi' + off) lt_i).
      by rewrite index_mem.
    rewrite nth_i nth_index //; split.
      by rewrite addwE; omega.
    rewrite -eq_sz.
    omega.
  by move=> _; apply: get_bi'.
case/(nthP newbi) => i.
rewrite /= size_set_nth (maxn_idPr _) ?index_mem // => lt_i.
case: i lt_i => [|i] lt_i /=.
  move=> <-.
  constructor=> //=.
  rewrite /bounded_add /= addwE ?subwE; omega.
  move=> off bounds_off.
  rewrite (get_write_block _ write_bi) //.
  rewrite subwE in bounds_off; last omega.
  have [/andP [/Z.leb_le le_bi /Z.ltb_lt le_biD]|_] :=
      boolP (word_to_Z (Sym.block_base bi) <=?
             word_to_Z (Sym.block_base bi + sz + off) <?
             word_to_Z (Sym.block_base bi) + word_to_Z sz).  
    by rewrite !addwE in le_bi le_biD; omega.
  have [|_ _ get_bi] := biP bi in_bi; first by rewrite color_bi.
  rewrite -addwA.
  apply: get_bi.
  by rewrite addwE; omega.
rewrite !nth_set_nth /=.
have [eq_i <-|neq_i] := i =P index bi info.
  apply: (@BlockInfoLive _ _ _ color newb) => //.
  * by rewrite /= /bounded_add; omega.
  * by rewrite PartMaps.get_set_eq.
  * move=> off /= lt_off.
  rewrite (get_write_block _ write_bi) => //.
  have [/Z.leb_le -> /Z.ltb_lt -> /=]:
    word_to_Z (Sym.block_base bi) <=
         word_to_Z (Sym.block_base bi + off) <
         (word_to_Z (Sym.block_base bi) + word_to_Z sz)%Z.
    by split; rewrite addwE; omega.
  by eexists; eexists.
move=> nth_i; move: (biP bi'); rewrite -nth_i mem_nth // nth_i.
case=> //.
  move=> col b color_bi' [? ?] mi_col get_bi'.
  apply: (@BlockInfoLive _ _ _ col b) => //.
    have neq_col: col <> color.
      by move=> eq_col; move/fresh_color: mi_col; rewrite eq_col; apply: lt_irrefl.
    by rewrite (PartMaps.get_set_neq _ _ neq_col).
  move=> off lt_off.
  rewrite (get_write_block _ write_bi) => //.
  have [/andP [/Z.leb_le ? /Z.ltb_lt ?]|] :=
      boolP (word_to_Z (Sym.block_base bi) <=?
             word_to_Z (Sym.block_base bi' + off) <?
             word_to_Z (Sym.block_base bi) + word_to_Z sz).
    case: neq_i; apply: (no_overlap _ _ newbi (Sym.block_base bi' + off) lt_i).
      by rewrite index_mem.
    rewrite nth_i nth_index //; split.
      by rewrite addwE; omega.
    omega.
  by move=> _; apply: get_bi'.
move=> color_bi' [? ?] get_bi'.
apply: BlockInfoFree => //.
move=> off bounds_off.
rewrite (get_write_block _ write_bi) //.
have [/andP [/Z.leb_le ? /Z.ltb_lt ?]|] :=
      boolP (word_to_Z (Sym.block_base bi) <=?
             word_to_Z (Sym.block_base bi' + off) <?
             word_to_Z (Sym.block_base bi) + word_to_Z sz).
  case: neq_i; apply: (no_overlap _ _ newbi (Sym.block_base bi' + off) lt_i).
    by rewrite index_mem.
  rewrite nth_i nth_index //; split.
    by rewrite addwE; omega.
  omega.
by move=> _; apply: get_bi'.
Qed.

Hint Constructors refine_val refine_val.
Hint Resolve get_mem_memv.
Hint Resolve meminj_update.

Lemma refine_pc_inv mi col apcb apci pc :
  refine_val mi (Abstract.VPtr (apcb, apci)) pc (PTR col) ->
  exists base, PartMaps.get mi col = Some (apcb,base) /\ (base + apci)%w = pc.
Proof.
intros rpc; inversion rpc.
by exists base; split.
Qed.

Ltac subst_beq :=
  match goal with
  | EQ : (?x == ?y) = true |- _ => (move/eqP: EQ => EQ; subst) || fail 2
  end.

Definition lift_binop (f : binop) (x y : atom (word mt) (Sym.tag mt)) :=
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
  refine_state mi ast sym_st -> (* refine_internal_state sym_st -> *)
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
try rewrite /Symbolic.next_state_pc /Symbolic.next_state_reg /Symbolic.next_state_reg_and_pc /Symbolic.next_state /= /Sym.mvec_match /= in NEXT;
match_inv;
repeat subst_beq;
have [miP _] := rmem;
try have [rpcb [mi_apcb rpci]] := refine_pc_inv rpc;

try match goal with
| GETCALL : Symbolic.get_syscall _ _ = Some _,
  CALL : Symbolic.run_syscall _ _ = Some _ |- _ =>
  move: GETCALL CALL;
  case: int rist => color info rist;
  rewrite /Symbolic.get_syscall /Symbolic.run_syscall /=;
  (have->: s = pc by inversion rpc);
  repeat case: ifP=> [/eqP <- /= [<-] /= | ? //];
  rewrite /Sym.malloc_fun /Sym.sizeof_fun /Sym.free_fun /Sym.basep_fun /Sym.eqp_fun /Sym.ptr_fun /= => CALL;
  match_inv
end;


repeat match goal with
  | GET : PartMaps.get ?reg ?r = Some ?v@V(?ty),
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
| GET : PartMaps.get ?mem ?w1 = Some _@M(?w2,?ty),
  UPD : PartMaps.upd ?mem ?w1 _@_ = Some _,
  rmem : refine_memory _ _ ?mem |- _ =>
    move: (GET) => GET2;
    eapply (refine_memory_get rmem) in GET; [|by eauto]; destruct GET as (? & ? & ? & ? & ?)
  | |- _ => idtac
end;

match goal with
| IDX : index_list_Z _ _ = Some _,
  UPD : PartMaps.upd ?mem ?w1 ?v@_ = Some _,
  rmem : refine_memory _ _ ?mem,
  rv : refine_val mi ?x ?v _,
  GET : PartMaps.get ?mem ?w1 = Some _ |- _ =>
    destruct (valid_update IDX x) as (? & ?);
    eapply (refine_memory_upd rmem) in UPD; [|by eauto|by eauto|by eauto|by eauto|by eauto|by eauto]; destruct UPD as (? & ? & ?);
    clear GET
  | |- _ => idtac
end;

repeat match goal with
  | GET : PartMaps.get ?mem ?w1 = Some ?v@M(_,?ty),
    rmem : refine_memory _ _ ?mem |- _ =>
    match ty with
    | DATA => (eapply (refine_memory_get_int rmem) in GET; [|by eauto])
                    || fail 5 "refine_memory_get_int"
    | _ =>
    (eapply (refine_memory_get rmem) in GET; [|by eauto]; destruct GET as (? & ? & ? & ? & ?)) || let op := current_instr_opcode in
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
  | UPD : PartMaps.upd ?reg ?r ?v = Some _,
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

  move: b Heqo E0 E3 => bi Heqo E0 E3. 
  case: (rist)=> fresh_color [in_bl [no_overlap]].
  move/(_ bi _).
  have: bi \in [seq x <- info
              | (val <=? Sym.block_size x)%ordered
              & Sym.block_color x == None].
    case: [seq x <- info
              | (val <=? Sym.block_size x)%ordered
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
    by rewrite /mi' /mi_malloc PartMaps.get_set_eq.

  move/(refine_registers_malloc (Sym.block_base bi) fresh_color malloc): rregs => rregs.
  eapply (refine_registers_upd rregs rnewb) in E3.
  destruct E3 as (? & ? & ?).

  eexists; exists (mi_malloc mi newb (Sym.block_base bi) color); split.
  eapply Abstract.step_malloc.
  by eauto.
  by eauto.
  by eauto.
  by eauto.

  move/ltb_lt: E => E.
  move/leb_le: E2 => E2.
  move/leb_le: lt_val => lt_val.
  split; try eassumption.
  exact: (refine_memory_malloc rmem E2 rist malloc).
  exact: (refine_val_malloc _ fresh_color malloc).
  have in_bounds: 0 <= word_to_Z val <= word_to_Z (Sym.block_size bi).
    split; first by move/word_to_Z_le: E2; rewrite word0.
    exact/word_to_Z_le.

  exact: (refine_internal_state_malloc in_bounds malloc).

(* Free *)
  generalize min_word_bound => min_bound.
  generalize max_word_bound => max_bound.
  have ? := @leZ_max (Sym.block_size x).
  case: (rist)=> fresh_color [in_bl [no_overlap]].
  move/(_ x _).
  have: x \in [seq x0 <- info | Sym.block_color x0 == Some s0].
    case: [seq x0 <- info | Sym.block_color x0 == Some s0] E=> //= ? ? [->].
    by rewrite inE eqxx.
  rewrite mem_filter => /andP [/eqP color_x in_x].
  rewrite in_x => /(_ erefl) biP.
  case: biP E E0 E1 color_x in_x => [|->] //.
  move=> col b color_bi [? ?] mi_col get_x E E0 E1 color_x in_x.
  case/andP: E1 => ? ?.
  have [? ?]: word_to_Z (Sym.block_base x) <= word_to_Z val <
            word_to_Z (Sym.block_base x) + (word_to_Z (Sym.block_size x)).
    split; first exact/word_to_Z_le/leb_le.
    rewrite -addwE; last omega.
    exact/word_to_Z_lt/ltb_lt.

  have [fr get_b]: exists fr, PartMaps.get a_mem b = Some fr.
    case/(_ (val - Sym.block_base x)): get_x => [|w [ty]].
    by rewrite subwE; omega.
    case: rmem => _ rmem.
    move/rmem.
    rewrite mi_col /Abstract.getv /=.
    by case: (PartMaps.get a_mem b) => // fr _; exists fr.
  have eq_col: col = s0 by congruence.
  have eq_s4b: s4 = b.
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

(*
(* Size *)
  move/(_ x _): (rist).
  have: x \in [seq x0 <- info | Sym.block_color x0 == Some s0].
    case: [seq x0 <- info | Sym.block_color x0 == Some s0] E=> //= ? ? [->].
    by rewrite inE eqxx.
  rewrite mem_filter => /andP [/eqP color_x ->] /(_ erefl) biP.
  case: biP E H5 color_x=> [|bi ->] //.
  move=> b col bi ? color_bi mi_b get_b size_fr E H5 color_x.
  have eq_col: col = s0 by congruence.
  rewrite eq_col in mi_b.
  have eq_s4b: s4 = b.
    inversion H3.
    exact: (miIr miP H10 mi_b erefl).

  eexists; eexists; split.
  eapply Abstract.step_size.
  by eauto.
  by rewrite eq_s4b.
  by rewrite -size_fr word_to_ZK.
  by eauto.

  by split; eassumption.


(* Base *)
  move/(_ x _): (rist).
  have: x \in [seq x0 <- info | Sym.block_color x0 == Some s0].
    case: [seq x0 <- info | Sym.block_color x0 == Some s0] E=> //= ? ? [->].
    by rewrite inE eqxx.
  rewrite mem_filter => /andP [/eqP color_x ->] /(_ erefl) biP.
  case: biP E E0 color_x=> [|bi ->] //.
  move=> b col bi ? color_bi mi_b get_b size_fr E E0 color_x.
  have eq_col: col = s0 by congruence.
  rewrite eq_col in mi_b.
  eapply (refine_registers_upd rregs) in E0; last first.
    by rewrite -[Sym.block_base bi]addw0; econstructor.
  case: E0 => ? [? ?].
  have eq_s1b: s4 = b.
    inversion H3.
    exact: (miIr miP H8 mi_b erefl).
  eexists; eexists; split.
  eapply Abstract.step_base.
  by eauto.
  by rewrite eq_s1b.
  by eauto.

  by split; eassumption.
*)

admit.
admit.

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

  have [eq_arg1b|neq_arg1b] := altP (arg1b =P s0).
    move: H4 H8; rewrite eq_arg1b => -> [-> ->].
    by rewrite eqxx (inj_eq (addwI base0)) => upd_ret.
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

(*
Print Assumptions backward_simulation.
*)

End refinement.
