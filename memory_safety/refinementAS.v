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
        {ap : Abstract.abstract_params mt block}
        {aps : Abstract.params_spec ap}
        {qap : Sym.abstract_params mt}
        {qaps : Sym.params_spec qap}.
(*
        {a_alloc : @Abstract.allocator _ block ap}
        {qa_alloc : @Sym.allocator _ qap}
        {a_allocP : Abstract.allocator_spec a_alloc}.
*)

Context `{syscall_regs mt} `{@Abstract.allocator mt block ap} `{@memory_syscall_addrs mt}.

Hypothesis binop_addDl : forall x y z,
  binop_denote ADD (x + y) z = x + (binop_denote ADD y z).

Hypothesis binop_addDr : forall x y z,
  binop_denote ADD x (y + z) = y + (binop_denote ADD x z).

Hypothesis binop_subDl : forall x y z,
  binop_denote SUB (x + y) z = x + (binop_denote SUB y z).

Hypothesis binop_subDr : forall x y z,
  binop_denote SUB x (y + z) = - y + (binop_denote SUB x z).

Hypothesis binop_eq_add2l : forall x y z,
  binop_denote EQ (x + y) (x + z) = binop_denote EQ y z.

(* CH: Is this really true??? It's what makes the proof go through *)
(* AAA: It's false if addition overflows. E.g. if working modulo 2, it
   is not the case that (1 + 0 <= 1 + 1) == (0 <= 1) *)

Hypothesis binop_leq_add2l : forall x y z,
  binop_denote LEQ (x + y) (x + z) = binop_denote LEQ y z.

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
Definition meminj := block -> option (word mt * word mt).

Record meminj_spec amem (mi : meminj) := {
    miIr : forall b b' base base' nonce nonce',
                mi b = Some (base, nonce) ->
                mi b' = Some (base', nonce') ->
                nonce = nonce' -> b = b';
    (* Blocks are non overlapping: *)
    mi_disjoints : forall b b' base base' nonce nonce' off off' fr fr',
      mi b = Some (base,nonce) ->
      mi b' = Some (base',nonce') ->
      PartMaps.get amem b = Some fr ->
      PartMaps.get amem b' = Some fr' ->
      base + off = base' + off' ->
      word_to_Z off < Z.of_nat (length fr) ->
      word_to_Z off' < Z.of_nat (length fr') ->
      b = b'
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
move=> b1 b1' base base' nonce nonce' off1 off1' fr1 fr1'.
have [->|/eqP neq_b1b] := altP (b1 =P b);
have [->//|/eqP neq_b1'b] := altP (b1' =P b);
rewrite ?(PartMaps.get_upd_eq upd_b) !(PartMaps.get_upd_neq _ upd_b) //.
+ move=> mi_b1 mi_b1' [<-]; rewrite (length_update_list_Z upd_off).
  exact: (mi_disjoints miP mi_b1 mi_b1').
  move=> mi_b1 mi_b1' get_b1 [<-]; rewrite (length_update_list_Z upd_off).
  exact: (mi_disjoints miP mi_b1 mi_b1').
+ exact: mi_disjoints.
Qed.

Hint Resolve meminj_update.

(*
Definition mi_free (mi : meminj) b : meminj :=
  fun b' => if b == b' then None else mi b'.

Lemma mi_freeP amem mi b :
  meminj_spec amem mi ->
  meminj_spec (Abstract.free_fun amem b) (mi_free mi b).
Proof.
admit.
Qed.
*)

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
  | RefinePtr : forall b base nonce off, mi b = Some (base,nonce) ->
                refine_val (Abstract.VPtr (b,off)) (base + off) (PTR nonce).

(*
Lemma refine_binop f v1 w1 ty1 v2 w2 ty2 w3 ty3 :
  meminj_spec amem mi ->
  refine_val v1 w1 ty1 -> refine_val v2 w2 ty2 ->
  Sym.lift_binop f w1@V(ty1) w2@V(ty2) = Some (w3,ty3) ->
  exists v3, Abstract.lift_binop f v1 v2 = Some v3 /\ refine_val v3 w3 ty3.
Proof.
destruct f; intros miP [x1 | b1 base1 nonce1 off1 mi_b1]
  [x2 | b2 base2 nonce2 off2 mi_b2] hyp; try discriminate hyp;
try (injection hyp; intros <- <-; eexists; split; [reflexivity|]); try constructor.
+ by rewrite binop_addDr; constructor.
+ by rewrite binop_addDl; constructor.
+ by rewrite binop_subDl; constructor.
+ simpl in *.
  move: hyp.
  have [eq_nonce hyp|//] := altP (nonce1 =P nonce2).
  injection hyp; intros <- <-.
  eexists.
  move: (mi_b1) => mi_b1'.
  rewrite {mi_b1'}(miIr miP mi_b1' mi_b2) // in mi_b1 *.
  rewrite eqxx.
      split; try reflexivity.
      (* This has a silly behavior:
         apply eqb_true_iff in eq_nonce.
      *)
      assert (eq_base : base1 = base2).
        congruence.
      rewrite eq_base.
      rewrite binop_subDl binop_subDr.
      rewrite addwA subww add0w.
      constructor.
+ simpl in *.
  case: eqP => [eq_b|neq_b].
    rewrite eq_b mi_b2 in mi_b1.
    injection mi_b1 as <- <-.
    rewrite eqxx in hyp; injection hyp as <- <-.
    eexists; split; try reflexivity.
    by rewrite binop_eq_add2l; constructor.
  move: hyp.
  have [eq_nonce hyp|neq_nonce hyp] := altP (nonce1 =P nonce2).
<<<<<<< Updated upstream
    rewrite (miIr mi_b1 mi_b2 eq_nonce) in neq_b; congruence. congruence.
=======
    rewrite (miIr miP mi_b1 mi_b2 eq_nonce) in neq_b; congruence.
  injection hyp as <- <-.
  eexists; split; try reflexivity.
by constructor.

+ (* CH: minless copy paste from above *)
  simpl in *.
  case: eqP => [eq_b|neq_b].
    rewrite eq_b mi_b2 in mi_b1.
    injection mi_b1 as <- <-.
    rewrite eqxx in hyp; injection hyp as <- <-.
    eexists; split; try reflexivity.
    by rewrite binop_leq_add2l; constructor.
    move: hyp.
  have [eq_nonce hyp|//] := altP (nonce1 =P nonce2).
    rewrite (miIr miP mi_b1 mi_b2 eq_nonce) in neq_b; congruence.
Qed.
*)

Lemma refine_ptr_inv w n b off base nonce :
  refine_val (Abstract.VPtr (b,off)) w (PTR n) ->
  mi b = Some (base, nonce) ->
  w = (base + off)%w.
Proof.
intros rpt mi_b.
inversion rpt.
congruence.
Qed.

Definition refine_memory amem (qamem : Sym.memory mt) :=
  meminj_spec amem mi /\
  forall b base nonce off, mi b = Some (base,nonce) ->
  match Abstract.getv amem (b,off), PartMaps.get qamem (base+off)%w with
  | None, None => True
  | Some v, Some w@M(nonce,ty) => refine_val v w ty
  | _, _ => False
 end.

Lemma refine_memory_get_int qamem (w1 w2 w3 : word mt) pt :
         refine_memory amem qamem -> refine_val (Abstract.VPtr pt) w1 (PTR w2) ->
         PartMaps.get qamem w1 = Some w3@M(w2,DATA) ->
         Abstract.getv amem pt = Some (Abstract.VData _ w3).
Proof.
intros [miP rmem] rpt get_w.
unfold refine_memory in rmem.
destruct pt as [b' off'].
(* Hit the too many names bug here too. *)
inversion rpt as [ | b base nonce off mi_b eq_b eq_w1 eq_nonce (* eq_off *)].
rewrite <-eq_nonce,<-eq_b,<-H2 in *.
move/(_ b base nonce off mi_b): rmem => rmem.
rewrite eq_w1 get_w in rmem.
destruct (Abstract.getv amem (b, off)) eqn:get_b; try contradiction.
by inversion rmem.
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

Lemma refine_memory_get qamem (w1 w2 w3 w4 : word mt) pt ty :
         refine_memory amem qamem -> refine_val (Abstract.VPtr pt) w1 (PTR w2) ->
         PartMaps.get qamem w1 = Some (w3@M(w4,ty)) ->
         exists fr x, PartMaps.get amem (fst pt) = Some fr
         /\ index_list_Z (word_to_Z (snd pt)) fr = Some x
         /\ refine_val x w3 ty.
Proof.
intros [miP rmem] rpt get_w.
destruct pt as [b' off'].
simpl in *.
(* Too many names bug... *)
inversion rpt as [|b base nonce off mi_b eq_b eq_w1 eq_nonce].
rewrite <-eq_nonce,<-eq_b,<-H2 in *.
move/(_ b base nonce off mi_b):rmem => rmem.
rewrite <-eq_w1 in get_w.
rewrite get_w in rmem.
destruct (Abstract.getv amem (b, off)) eqn:get_b; try contradiction.
destruct (getv_mem get_b) as (fr & ? & ?).
exists fr; exists v; repeat split; easy.
Qed.

(*
Lemma size_upd_eq amem' b fr fr' i x :
  PartMaps.get amem b = Some fr ->
  update_list_Z i x fr = Some fr' ->
  PartMaps.upd amem b fr' = Some amem' ->
  size amem' b = size amem b.
Proof.
intros get upd_list upd.
unfold size.
by rewrite (PartMaps.get_upd_eq upd) (length_update_list_Z upd_list) get.
Qed.

Lemma size_upd_neq amem' b b' fr : PartMaps.upd amem b fr = Some amem' ->
  b' <> b ->
  size amem' b' = size amem b'.
Proof.
intros upd neq_bb'.
unfold size.
simpl.
generalize (PartMaps.get_upd_neq neq_bb' upd). simpl.
by rewrite /Abstract.frame /= ; move->.
Qed.

Lemma size_getv b off v :
  Abstract.getv amem (b,off) = Some v ->
  word_to_Z off < size amem b.
Proof.
unfold Abstract.getv, size; simpl.
destruct (PartMaps.get amem b); try discriminate.
intros index_off.
apply index_list_Z_Some in index_off.
by destruct index_off.
Qed.

Lemma size_update b fr base nonce off fr' x :
  PartMaps.get amem b = Some fr ->
  mi b = Some (base, nonce) ->
  update_list_Z off x fr = Some fr' ->
  off < size amem b.
Proof.
unfold size; intros -> mi_b upd_x.
have: 0 <= off < Z.of_nat (length fr).
  by eapply update_list_Z_Some; exists fr'.
by case.
Qed.

*)

Lemma refine_memory_upd qamem qamem'
                        w1 w2 pt ty n fr fr' x :
         refine_memory amem qamem -> refine_val (Abstract.VPtr pt) w1 (PTR n) ->
         PartMaps.upd qamem w1 w2@M(n, ty) = Some qamem' ->
         PartMaps.get amem (fst pt) = Some fr ->
         update_list_Z (word_to_Z (snd pt)) x fr = Some fr' ->
         refine_val x w2 ty ->
         exists amem', PartMaps.upd amem (fst pt) fr' = Some amem'
         /\ refine_memory amem' qamem'.
Proof.
intros [miP rmem] rpt (* in_bounds_pt *) upd_w1 get_pt update_pt rx.
destruct (PartMaps.upd_defined fr' get_pt) as [amem' upd_pt].
exists amem'; split; try assumption; split; first by eauto.
intros b base nonce off mi_b.
unfold Abstract.getv in *.
have [eq_b|neq_b] := altP (b =P pt.1).
  rewrite eq_b.
  simpl; rewrite (PartMaps.get_upd_eq upd_pt).
  have [->|/eqP neq_off] := altP (off =P snd pt).
    rewrite (update_list_Z_spec update_pt).
    assert (eq_w1 : (base + snd pt)%w = w1).
      replace pt with (fst pt, snd pt) in rpt.
        inversion rpt; congruence.
      by destruct pt.
    rewrite eq_w1.
    rewrite (PartMaps.get_upd_eq upd_w1).
    assert (eq_n : n = nonce).
      replace pt with (fst pt, snd pt) in rpt.
        by inversion rpt; congruence.
      by destruct pt.
    congruence.
  assert (neqw_off : word_to_Z off <> word_to_Z (snd pt)).
    by move/word_to_Z_inj.
  rewrite <-(update_list_Z_spec2 update_pt neqw_off).
  specialize (rmem b base nonce off mi_b).
  simpl in rmem.
  rewrite eq_b get_pt in rmem.
  assert (neq_w1 : (base + off)%w <> w1).
    destruct pt as [b' off']; simpl in *.
    rewrite eq_b in mi_b.
    rewrite (refine_ptr_inv rpt mi_b).
    by intros eq_w1; apply addwI in eq_w1; congruence.
  by rewrite (PartMaps.get_upd_neq neq_w1 upd_w1).
specialize (rmem b base nonce off mi_b).
move/eqP: neq_b => neq_b.
generalize (PartMaps.get_upd_neq neq_b upd_pt).
unfold Abstract.frame. simpl.
move->.
simpl in *.
(* Why does fold fail?
fold (Abstract.getv amem (b,off)) in *.
*)
(*
change (match PartMaps.get amem b with
           | Some fr0 => index_list_Z (word_to_Z off) fr0
           | None => None
           end)
with (Abstract.getv amem (b,off)) in *.
*)

have [eq_w1|/eqP neq_w1] := altP (base + off =P w1).
  rewrite <-eq_w1 in upd_w1.
  rewrite (PartMaps.get_upd_eq upd_w1).
  destruct (PartMaps.get amem b) eqn:get_b.
    destruct pt as [b' off']; simpl in *; revert eq_w1.
    inversion rpt as [|? ? ? ? mi_pt].
(*
    assert (lt_off' : word_to_Z off' < size amem b').
      by apply (size_update get_pt mi_pt update_pt).
*)
    intros overlap.
    rewrite (mi_disjoints miP mi_b mi_pt get_b get_pt overlap) // in neq_b.

(* We could use a reflection lemma here *)
    generalize (@index_list_Z_Some _ (word_to_Z off) f).
    case: (index_list_Z (word_to_Z off) f) rmem => [v _ /(_ v erefl) [] //|].
    by have [? ->] := PartMaps.upd_inv upd_w1.
  case: (update_list_Z_Some x fr (word_to_Z off')) => _.
  by case=> //; eexists.
destruct (PartMaps.upd_inv upd_w1) as [? get_w1].
  by rewrite get_w1 in rmem.
by rewrite (PartMaps.get_upd_neq neq_w1 upd_w1).
Qed.

Definition refine_registers (aregs : Abstract.registers mt)
                            (qaregs : Sym.registers mt) :=
  forall n, match PartMaps.get aregs n, PartMaps.get qaregs n with
  | None, None => True
  | Some v, Some w@V(ty) => refine_val v w ty
  | _, _ => False
  end.

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
  PartMaps.upd qaregs r w@V(ty) = Some qaregs' ->
  refine_val v w ty ->
  exists areg',
    PartMaps.upd aregs r v = Some areg' /\
    refine_registers areg' qaregs'.
Proof.
intros rregs upd_r_qa rvw.
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

Definition refine_state (ast : Abstract.state mt) (qast : Symbolic.state mt) :=
  let '(Abstract.mkState amem aregs apc) := ast in
  match qast with
  | Symbolic.State qamem qaregs w@V(ty) ist =>
    [/\ refine_memory amem qamem,
        refine_registers aregs qaregs &
        refine_val apc w ty]
  | _ => False
  end.

(*
Definition refine_syscall (asc : Abstract.syscall mt) (qasc : Sym.syscall mt) :=
  Abstract.address asc = Sym.address qasc
  /\ forall ast qast, refine_state ast qast ->
    ohrel refine_state (Abstract.sem asc ast) (Sym.sem qasc qast).

Lemma refine_syscall_sem asc qasc ast qast qast' :
  refine_syscall asc qasc ->
  Sym.sem qasc qast = Some qast' ->
  refine_state ast qast ->
  exists ast', Abstract.sem asc ast = Some ast' /\ refine_state ast' qast'.
Proof.
intros [_ rsc] sem_asc rst.
specialize (rsc ast qast rst); revert rsc.
rewrite sem_asc.
destruct (Abstract.sem asc ast) as [ast'|]; try easy.
by intros rst'; exists ast'; split.
Qed.

Axiom refine_syscalls : forall amem, meminj amem -> list (Abstract.syscall mt) -> list (Sym.syscall mt) -> Prop.
*)

(*
Axiom refine_syscalls_get : forall asc qasc w sc, refine_syscalls mi asc qasc ->
  Sym.get_syscall qasc w = Some sc ->
  exists sc', Abstract.get_syscall asc w = Some sc'
    /\ refine_syscall sc' sc.
*)

End memory_injections.

(*
Lemma refine_val_free mi b x w ty : refine_val mi x w ty ->
  refine_val (mi_free mi b) x w ty.
Proof.
case=> [|b' base nonce off mi_b']; constructor=> //.
rewrite /mi_free.
case: (b == b').



Lemma refine_registers_free mi aregs qaregs b :
  refine_registers mi aregs qaregs -> refine_registers (mi_free mi b) aregs qaregs.
Proof.
move=> rregs r.
move/(_ r): rregs.
case: (PartMaps.get aregs r) => [x|]; case: (PartMaps.get qaregs r) => [a|] //.
*)


Hint Constructors refine_val refine_val.
Hint Resolve get_mem_memv.
Hint Resolve meminj_update.
(*
Hint Resolve mi_freeP.
*)

Lemma refine_pc_inv mi nonce apcb apci pc :
  refine_val mi (Abstract.VPtr (apcb, apci)) pc (PTR nonce) ->
  exists base, mi apcb = Some (base, nonce) /\ (base + apci)%w = pc.
Proof.
intros rpc; inversion rpc.
by exists base; split.
Qed.

(* We prove here the invariants enforced by symbolic rules *)
(*
Lemma pc_noJal st st' mvec pc :
  Symbolic.next_state_pc st mvec pc = Some st' ->
  Symbolic.op mvec != JAL -> Symbolic.tpc mvec != V(DATA).
Proof.
by case: mvec=> op [[|]||].
Qed.

Lemma tiE st st' mvec pc :
  Symbolic.next_state_pc st mvec pc = Some st' ->
  exists b, Symbolic.ti mvec = M(b,DATA).
Proof.
case: mvec=> op tpc ti.
case: op; (do ?case) => ts;
case: tpc => [[|?]|? [|?]|] //;
case: ti => [[|?]|? [|?]|] // _;
by eexists.
Qed.
*)

(* TODO : factor these proofs out *)

Lemma next_state_pcE st st' mvec pc :
  Symbolic.next_state_pc st mvec pc = Some st' ->
  exists b, Symbolic.tpc mvec = V(PTR b) /\ Symbolic.ti mvec = M(b,DATA).
Proof.
case: mvec=> op tpc ti.
case: op; (do ?case) => ts;
case: tpc => [[|?]|? [|?]|] //;
case: ti => [[|?]|? [|?]|] //;
rewrite /Symbolic.next_state_pc /Symbolic.next_state /=;
case: ifP => //= /eqP->;
by eexists.
Qed.

Lemma next_state_regE st st' mvec r w :
  Symbolic.next_state_reg st mvec r w = Some st' ->
  (* PartMaps.get reg r = Some old@told -> *)
  exists b, Symbolic.tpc mvec = V(PTR b) /\ Symbolic.ti mvec = M(b,DATA).
Proof.
case: mvec=> op tpc ti.
case: op; (do ?case) => ts;
case: tpc => [[|?]|? [|?]|] //;
case: ti => [[|?]|? [|?]|] //;
rewrite /Symbolic.next_state_reg /Symbolic.next_state_reg_and_pc /Symbolic.next_state /=;
case: ifP => //= /eqP->;
by eexists.
Qed.

(*
Inductive refine_sym_step_spec : Abstract.state mt -> Symbolic.state mt -> Type :=
  RefineNop ast sst : refine_sym_step_spec ast sst.

Lemma refine_sym_stepP mi ast sst sst' : refine_state mi ast sst ->
  Sym.step sst sst' -> refine_sym_step_spec ast sst.
Proof.
*)

(*
Lemma analyze_cache mvec op :
  cache_correct cache ->
  Concrete.cache_lookup _ cache masks cmvec = Some crvec ->
  word_lift (fun t => is_user t) (Concrete.ctpc cmvec) = true ->
  Concrete.cop cmvec = op_to_word op ->
  exists tpc, Concrete.ctpc cmvec = encode (USER tpc) /\
  (match Symbolic.nfields op as fs return (_ -> _ -> Symbolic.mvec_operands (@Symbolic.tag mt ap) fs -> _) -> Prop with
   | Some fs => fun mk =>
     exists ti (ts : Vector.t _ (fst fs)) trpc tr,
     Concrete.cti cmvec = encode (USER ti) /\
     crvec = Concrete.mkRVec (encode (USER trpc))
                             (encode (USER tr)) /\
     Symbolic.handler (mk tpc ti ts) = Some (Symbolic.mkRVec trpc tr) /\
     match fst fs as n return Vector.t _ n -> Prop with
     | 0 => fun ts => ts = []
     | 1 => fun ts => exists t1,
                        ts = [t1] /\
                        Concrete.ct1 cmvec = encode (USER t1)
     | 2 => fun ts => exists t1 t2,
                        ts = [t1; t2] /\
                        Concrete.ct1 cmvec = encode (USER t1) /\
                        Concrete.ct2 cmvec = encode (USER t2)
     | 3 => fun ts => exists t1 t2 t3,
                        ts = [t1; t2; t3] /\
                        Concrete.ct1 cmvec = encode (USER t1) /\
                        Concrete.ct2 cmvec = encode (USER t2) /\
                        Concrete.ct3 cmvec = encode (USER t3)
     | _ => fun _ => False
     end ts
   | None => fun _ => False
   end (Symbolic.mkMVec op) \/
   exists t,
     Concrete.cti cmvec = encode (ENTRY t) /\
     crvec = Concrete.mkRVec (encode KERNEL) (encode KERNEL)).
Proof.
  intros CACHE LOOKUP INUSER EQ.
  destruct cmvec as [op' tpc ti t1 t2 t3].
  destruct (CACHE _ crvec INUSER LOOKUP)
    as ([trpc tr] & ? & HIT). subst. simpl in *.
  simpl in HIT.
  destruct (word_to_op op') as [op''|] eqn:E; try discriminate. subst op'.
  rewrite op_to_wordK in E.
  move: E => [E]. subst op''.
  unfold encode_mvec, encode_rvec in *. simpl in *.
  destruct op; simpl in *; match_inv;
  repeat match goal with
  | H : decode ?t = Some _ |- _ =>
    apply encodeK in H; subst t
  end;
  eexists; split; eauto;
  try match goal with
  | rvec : Symbolic.RVec _ |- _ => destruct rvec
  end;
  simpl in *;
  repeat (
    match goal with
    | ts : Vector.t _ 0 |- _ => induction ts using Vector.case0
    | ts : Vector.t _ (S _) |- _ => induction ts using caseS
    | |- context[decode (encode _)] => rewrite decodeK
    end; simpl
  );
  simpl in *; left;
  do 4 eexists; repeat (split; eauto);

  (* match_inv is to brutal with equalities involving dependent types *)
  repeat match goal with
  | H : bind _ ?X = Some _ |- _ =>
    match X with
    | context[match ?a with _ => _ end] =>
      destruct a as [?| |];
      try solve [inversion H];
      simpl in H
    end
  end;
  solve [inv HIT; eauto 7].
Qed.
*)

Ltac subst_beq :=
  match goal with
  | EQ : (?x == ?y) = true |- _ => (move/eqP: EQ => EQ; subst) || fail 2
  end.

Definition lift_binop (f : binop) (x y : atom (word mt) (Sym.label mt)) :=
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
  | LEQ => match x, y with
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
destruct f; intros miP [x1 | b1 base1 nonce1 off1 mi_b1]
  [x2 | b2 base2 nonce2 off2 mi_b2] hyp; try discriminate hyp;
try (injection hyp; intros <- <-; eexists; split; [reflexivity|]); try constructor.
+ by rewrite binop_addDr; constructor.
+ by rewrite binop_addDl; constructor.
+ by rewrite binop_subDl; constructor.
+ simpl in *.
  move: hyp.
  have [eq_nonce hyp|//] := altP (nonce1 =P nonce2).
  injection hyp; intros <- <-.
  eexists.
  move: (mi_b1) => mi_b1'.
  rewrite {mi_b1'}(miIr miP mi_b1' mi_b2) // in mi_b1 *.
  rewrite eqxx.
      split; try reflexivity.
      (* This has a silly behavior:
         apply eqb_true_iff in eq_nonce.
      *)
      assert (eq_base : base1 = base2).
        congruence.
      rewrite eq_base.
      rewrite binop_subDl binop_subDr.
      rewrite addwA subww add0w.
      constructor.
+ simpl in *.
  case: eqP => [eq_b|neq_b].
    rewrite eq_b mi_b2 in mi_b1.
    injection mi_b1 as <- <-.
    rewrite eqxx in hyp; injection hyp as <- <-.
    eexists; split; try reflexivity.
    by rewrite binop_eq_add2l; constructor.
  move: hyp.
  have [eq_nonce hyp|neq_nonce hyp] := altP (nonce1 =P nonce2).
    rewrite (miIr miP mi_b1 mi_b2 eq_nonce) in neq_b; congruence. congruence.
  eexists; split; try reflexivity.
Admitted.

Ltac solve_pc rpci :=
  by eexists; eexists; split;
  [econstructor (by eauto) |
  split; try eassumption;
  simpl; rewrite <-rpci, <-addwA; econstructor].

Lemma backward_simulation ast mi sym_st sym_st' :
  refine_state mi ast sym_st -> Sym.step sym_st sym_st' ->
  exists ast' mi', Abstract.step ast ast' /\ refine_state mi' ast' sym_st'.
Proof.
case: ast => a_mem a_regs a_pc.
case: sym_st => sym_mem sym_regs sym_pc // sym_ist rst.
case: sym_st' => sym_mem' sym_regs' sym_pc' sym_ist' sym_step.
Coqlib.inv sym_step;
case: ST => *; subst;
destruct tpc as [[|]| |] => //;
case: rst => rmem rregs rpc;
destruct a_pc as [|[pc_b pc_off]]; try (by inversion rpc);
try subst mvec;
try rewrite /Symbolic.next_state_pc /Symbolic.next_state_reg /Symbolic.next_state_reg_and_pc /Symbolic.next_state /= /Sym.mvec_match /= in NEXT;
match_inv;
repeat subst_beq;
have [miP _] := rmem;
have [rpcb [mi_apcb rpci]] := refine_pc_inv rpc;

repeat match goal with
  | GET : PartMaps.get ?reg ?r = Some ?v@V(?ty) |- _ =>
  match type_of reg with
  | Symbolic.registers _ =>
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
  end
  end;


repeat match goal with
  | GET : PartMaps.get ?mem ?w1 = Some ?v@M(_,?ty) |- _ =>
  match type_of mem with
  | Symbolic.memory _ =>
    match ty with
    | DATA => (eapply (refine_memory_get_int rmem) in GET; [|by eauto])
                    || fail 5 "refine_memory_get_int"
    | _ =>
    (eapply (refine_memory_get rmem) in GET; [|by eauto]; destruct GET as (? & ? & ? & ? & ?)) || let op := current_instr_opcode in
            fail 5 "refine_memory_get" op GET
    end
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
  | UPD : PartMaps.upd ?reg ?r ?v = Some _ |- _ =>
  match type_of reg with
  | Symbolic.registers _ =>
    (eapply (refine_registers_upd rregs) in UPD; [|by eauto]; destruct UPD as (? & ? & ?)) (* || let op := current_instr_opcode in fail 3 "refine_registers_upd" op UPD *)
  end
  | |- _ => idtac
  end;

match goal with
| IDX : index_list_Z _ _ = Some _,
  UPD : PartMaps.upd ?mem ?w1 ?v@_ = Some _,
  rv : refine_val mi ?x ?v _ |- _ =>
    match type_of mem with
    | Symbolic.memory _ =>
    destruct (valid_update IDX x) as (? & ?);
    eapply (refine_memory_upd rmem) in UPD; [|by eauto|by eauto|by eauto|by eauto]; destruct UPD as (? & ? & ?)
    end
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
admit.

Qed.

End refinement.