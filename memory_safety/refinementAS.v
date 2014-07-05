Require Import ZArith.
Ltac type_of x := type of x.

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

Section refinement.

Open Scope Z_scope.
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
        `{@memory_syscall_addrs mt}
        {meminj' : Type -> Type}
        {meminj_map : PartMaps.partial_map meminj' (word mt)}
        {meminjs : PartMaps.axioms meminj_map}.

Notation meminj := (meminj' (block * (word mt) (* base *))).

Hypothesis binop_addDl : forall x y z,
  binop_denote ADD (x + y) z = x + (binop_denote ADD y z).

Hypothesis binop_addDr : forall x y z,
  binop_denote ADD x (y + z) = y + (binop_denote ADD x z).

Hypothesis binop_subDl : forall x y z,
  binop_denote SUB (x + y) z = x + (binop_denote SUB y z).

Hypothesis binop_sub_add2l : forall x y z,
  binop_denote SUB (x + y) (x + z) = (binop_denote SUB y z).

Hypothesis binop_eq_add2l : forall x y z,
  binop_denote EQ (x + y) (x + z) = binop_denote EQ y z.

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

Inductive block_info_spec (smem : Sym.memory mt) : Sym.block_info mt -> Prop :=
| BlockInfoLive : forall bi col b base, Sym.block_color bi = Some col ->
  PartMaps.get mi col = Some (b,base) ->
  (forall off, (off < Sym.block_size bi)%ordered ->
     exists v ty, PartMaps.get smem (base+off) = Some v@M(col,ty)) ->
  block_info_spec smem bi
| BlockInfoFree : forall bi,
  Sym.block_color bi = None ->
  (forall off, word_to_Z off < word_to_Z (Sym.block_size bi) ->
    exists v, PartMaps.get smem (Sym.block_base bi + off) = Some v@FREE) ->
  block_info_spec smem bi.

(* TODO: export from Sym in symbolic.v *)
Canonical Sym.block_info_eqType.

Definition fresh_color col :=
  forall col' b base, PartMaps.get mi col' = Some (b,base) ->
  (col' < col)%ordered.

(* We may need:
get mi col != None -> exists bi, bi \in info /\ block_color bi = Some col *)
Definition refine_internal_state (bl : list block) smem (ist : word mt * list (Sym.block_info mt)) :=
  let: (col, info) := ist in
  fresh_color col /\ (forall col b base, PartMaps.get mi col = Some (b,base) -> b \in bl) /\
  forall x, x \in info -> block_info_spec smem x.

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
move=> [miP rmem] [freshcol [in_bl rist]] rpt get_w1 upd_w1 get_pt update_pt rx.
destruct (PartMaps.upd_defined fr' get_pt) as [amem' upd_pt].
exists amem'; split => //; last first.
  split => //; split => //.
  case=> bi_base bi_size [bi_col in_bi|in_bi]; last first.
    move/(_ _ in_bi): rist => biP.
    inversion biP => //.
    apply: BlockInfoFree => //=.
    move=> off lt_off.
    case/(_ off lt_off): H2 => v /=.
    have [->|/eqP neq_w1] := altP (bi_base + off =P w1).
       by rewrite get_w1.
    by rewrite (PartMaps.get_upd_neq neq_w1 upd_w1); move => ?; exists v.
  have [eq_coln|neq_coln] := altP (bi_col =P n).
    rewrite eq_coln in in_bi *.
    move/(_ _ in_bi): rist => biP.
    inversion biP => //.
    case: H1 => eq_col.
    rewrite -eq_col in H2 H3.
    apply: (BlockInfoLive _ H2) => //=.
    move=> off lt_off.
    case/(_ off lt_off): H3 => v [ty''].
    destruct pt as [pt_b pt_off].
    rewrite (refine_ptr_inv miP rpt H2) in get_w1 upd_w1.
    have [->|/eqP neq_off] := altP (off =P pt_off).
      by move=> _; rewrite (PartMaps.get_upd_eq upd_w1); eexists; eexists.
    have neq_w1 : base + off <> base + pt_off.
      by move/addwI.
    by rewrite (PartMaps.get_upd_neq neq_w1 upd_w1) => ?; eexists; eexists.
  move/(_ _ in_bi): rist => biP.
  inversion biP => //=.
  case: H1 => eq_col.
  rewrite -eq_col in H2 H3.
  apply: (BlockInfoLive _ H2) => //.
  move=> off lt_off.
  case/(_ off lt_off): H3 => v [ty''].
  have [->|/eqP neq_w1] := altP (base + off =P w1).
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

(*
Lemma refine_memory_free amem' smem nc info b bi col :
  refine_memory amem smem ->
  refine_internal_state amem smem (nc, info) ->
  bi \in info ->
  mi b = Some (Sym.block_base bi, col) ->
  Sym.block_color bi = Some col ->
  Abstract.free_fun amem b = Some amem' ->
  let smem' :=
    Sym.write_block smem (Sym.block_base bi) 0@FREE
      (Z.to_nat (word_to_Z (Sym.block_size bi)))
  in
  refine_memory amem' smem' /\
  refine_internal_state amem' smem'
     (nc,
     set_nth (Sym.def_info mt) info (index bi info)
       {|
       Sym.block_base := Sym.block_base bi;
       Sym.block_size := Sym.block_size bi;
       Sym.block_color := None |}).
Proof.
admit.
Qed.
*)

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
  Abstract.malloc_fun amem bl sz = (amem', newb) ->
  refine_registers mi aregs sregs ->
  refine_registers (mi_malloc mi newb base col) aregs sregs.
Proof.
admit.
Qed.

Lemma get_write_block smem base sz v w :
  PartMaps.get (Sym.write_block smem base v sz) w =
  if base <=? w <? base + sz then Some v else PartMaps.get smem w.
Proof.
admit.
Qed.

Lemma refine_memory_malloc mi amem smem amem' info bl sz newb base col :
  refine_memory mi amem smem ->
  refine_internal_state mi bl smem (col, info) ->
  Abstract.malloc_fun amem bl sz = (amem', newb) ->
  let smem' := Sym.write_block smem base 0@M(col, DATA) sz
  in
  refine_memory (mi_malloc mi newb base col) amem' smem'.
Proof.
move=> rmem [fresh_col [in_bl rist]] malloc /=.
split.
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
  by case: rmem => miP _; apply: (miIr miP).
move=> w1 w2 col' ty.
have [<-|neq_col] := altP (col =P col').
  rewrite PartMaps.get_set_eq get_write_block.
  have [|_] := boolP (base <=? w1 <? base + sz); last first.
    case: rmem => miP rmem /rmem.
    move: (in_bl col).
    case: (PartMaps.get mi col) => // [[b' base']] /(_ b' base' erefl).
admit.
admit.
    (* by rewrite (negbTE (Abstract.malloc_fresh malloc)).

move/in_bl.

case: ifP; last first.


have [|] := boolP (base <=? w1 <? base + sz).
(ltb_lt base w1).*)
(* if col = col' then base <= w1 <= base + sz *)
admit.
Qed.

Lemma refine_internal_state_malloc mi amem amem' bl smem info sz newb bi color :
  Abstract.malloc_fun amem bl sz = (amem', newb) ->
  refine_internal_state mi bl smem (color, info) ->
  refine_internal_state (mi_malloc mi newb (Sym.block_base bi) color)
    (newb :: bl)
     (Sym.write_block smem (Sym.block_base bi) 0@M(color, DATA) sz)
     (color + 1, Sym.update_block_info info bi color sz).
Proof.
admit.
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

Ltac inv H := (inversion H; subst; clear H). 


Lemma refine_binop mi amem f v1 w1 ty1 v2 w2 ty2 w3 ty3 :
  meminj_spec amem mi ->
  refine_val mi v1 w1 ty1 -> refine_val mi v2 w2 ty2 ->
  lift_binop f w1@V(ty1) w2@V(ty2) = Some (w3,ty3) ->
  exists v3, Abstract.lift_binop f v1 v2 = Some v3 /\ refine_val mi v3 w3 ty3.
Proof.
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
Coqlib.inv sym_step;
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

  move: b Heqo E => bi Heqo E.
  case: (rist)=> fresh_color [in_bl].
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
  case: biP Heqo E color_bi in_bi lt_val; first by move=> *; congruence.
  move=> {bi} bi _ FREE Heqo E color_bi in_bi lt_val.


  case malloc: (Abstract.malloc_fun a_mem bl val) => [amem' newb].
  pose mi' := mi_malloc mi newb (Sym.block_base bi) color.
  have rnewb: refine_val mi' (Abstract.VPtr (newb, 0)) (Sym.block_base bi) (PTR color).
    rewrite -[Sym.block_base bi]addw0; constructor.
    by rewrite /mi' /mi_malloc PartMaps.get_set_eq.

  move/(refine_registers_malloc (Sym.block_base bi) color malloc): rregs => rregs.
  eapply (refine_registers_upd rregs rnewb) in E.
  destruct E as (? & ? & ?).

  eexists; exists (mi_malloc mi newb (Sym.block_base bi) color); split.
  eapply Abstract.step_malloc.
  by eauto.
  by eauto.
  by eauto.
  by eauto.

  split; try eassumption.
  exact: (refine_memory_malloc _ rmem rist malloc).
  exact: (refine_val_malloc _ fresh_color malloc).
  exact: (refine_internal_state_malloc _ malloc).

(* Free *)

(*
  move/(_ x _): (rist).
  have: x \in [seq x0 <- info | Sym.block_color x0 == Some s0].
    case: [seq x0 <- info | Sym.block_color x0 == Some s0] E=> //= ? ? [->].
    by rewrite inE eqxx.
  rewrite mem_filter => /andP [/eqP color_x in_x].
  rewrite in_x => /(_ erefl) biP.
  case: biP E E1 color_x in_x => [|bi ->] //.
  move=> bi col b ? color_bi mi_col size_fr E E1 color_x in_x.
  have eq_col: col = s0 by congruence.
  rewrite eq_col in mi_b.
  have eq_s4b: s4 = b.
    inversion H3.
    exact: (miIr miP H8 mi_b erefl).
  case: (Abstract.free_Some get_b)=> ? free_b.

  eexists; eexists; split.
  eapply Abstract.step_free.
  by eauto.
  by rewrite eq_s4b.
  by eauto.

  case: (refine_memory_free rmem rist in_x mi_b color_x free_b) => rmem' rist'.
  by split; eassumption.

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

End refinement.