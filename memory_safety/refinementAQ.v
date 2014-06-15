(* Why is common in concrete? *)
(* BCP: I wondered this too! *)
Require Import ZArith.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import utils concrete.common memory_safety.abstract memory_safety.quasiabstract.
Require Import memory_safety.classes.

Require Import EquivDec.

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

Import QuasiAbstract.Notations.
(* BCP: Why do we have something called QuasiAbstract in this
   development? *)

Variable block : eqType.

Context {mt : machine_types}
        {ops : machine_ops mt}
        {opss : machine_ops_spec ops}
        {ap : Abstract.abstract_params mt block}
        {aps : Abstract.params_spec ap}
        {qap : QuasiAbstract.abstract_params mt}
        {qaps : QuasiAbstract.params_spec qap}
        {a_alloc : @Abstract.allocator _ block ap}
        {qa_alloc : @QuasiAbstract.allocator _ qap}.

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
Hypothesis binop_leq_add2l : forall x y z,
  binop_denote LEQ (x + y) (x + z) = binop_denote LEQ y z.

Section memory_injections.

Definition size amem pt :=
  match PartMaps.get amem pt with
  | None => 0%Z
  | Some fr => Z.of_nat (length fr)
  end.

Record meminj amem := Meminj {
  (* if b is allocated, mi b returns Some (w1,w2) where
     - w1 is the address of b's first memory location
     - w2 is b's pointer nonce
  *)
    mi :> block -> option (word mt * word mt);
    miIr : forall b b' base base' nonce nonce',
                mi b = Some (base, nonce) ->
                mi b' = Some (base', nonce') ->
                nonce = nonce' -> b = b';
    (* Blocks are non overlapping: *)
    mi_disjoints : forall b b' base base' nonce nonce' off off',
      mi b = Some (base,nonce) ->
      mi b' = Some (base',nonce') ->
      base + off = base' + off' ->
      word_to_Z off < size amem b -> word_to_Z off' < size amem b' ->
      b = b'
  }.

Variable amem : Abstract.memory mt.
Variable mi : meminj amem.

Definition ohrel (A B : Type) (rAB : A -> B -> Prop) sa sb : Prop :=
  match sa, sb with
    | None,   None   => True
    | Some a, Some b => rAB a b
    | _,      _      => False
  end.

Inductive refine_val : Abstract.value mt block -> word mt -> QuasiAbstract.type mt -> Prop :=
  | RefineInt : forall w, refine_val (Abstract.ValInt _ w) w INT
  | RefinePtr : forall b base nonce off, mi b = Some (base,nonce) ->
                refine_val (Abstract.ValPtr (b,off)) (base + off) (PTR nonce).

Lemma refine_binop f v1 w1 ty1 v2 w2 ty2 w3 ty3 : refine_val v1 w1 ty1 ->
  refine_val v2 w2 ty2 ->
  QuasiAbstract.lift_binop f w1@V(ty1) w2@V(ty2) = Some (w3,ty3) ->
  exists v3, Abstract.lift_binop f v1 v2 = Some v3 /\ refine_val v3 w3 ty3.
Proof.
destruct f; intros [x1 | b1 base1 nonce1 off1 mi_b1]
  [x2 | b2 base2 nonce2 off2 mi_b2] hyp; try discriminate hyp;
try (injection hyp; intros <- <-; eexists; split; [reflexivity|]); try constructor.
+ by rewrite binop_addDr; constructor.
+ by rewrite binop_addDl; constructor.
+ by rewrite binop_subDl; constructor.
+ simpl in *.
(* We hit here a bug in destruct (and probably pattern) *)
(* ssreflect's case tactic works fine... *)
(* I will refactor this part, by case analysis on equalities on blocks first *)
  destruct (@SetoidDec.equiv_decb (QuasiAbstract.block mt)
         (SetoidDec.eq_setoid (QuasiAbstract.block mt))
         (@eq_word mt ops) nonce1 nonce2) eqn:eq_nonce; try discriminate.
  injection hyp; intros <- <-.
  eexists.
  move: (mi_b1) => mi_b1'.
  rewrite {mi_b1'}(miIr mi_b1' mi_b2) // in mi_b1 *.
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
    by apply eqb_true_iff.
+ simpl in *.
  case: eqP => [eq_b|neq_b].
    rewrite eq_b mi_b2 in mi_b1.
    injection mi_b1 as <- <-.
    rewrite eqb_refl in hyp; injection hyp as <- <-.
    eexists; split; try reflexivity.
    by rewrite binop_eq_add2l; constructor.
  destruct (@SetoidDec.equiv_decb (QuasiAbstract.block mt)
       (SetoidDec.eq_setoid (QuasiAbstract.block mt))
       (@eq_word mt ops) nonce1 nonce2) eqn:eq_nonce.
  (* again, I would like to do
     apply eqb_true_iff in eq_nonce.
  *)
    assert (eq_nonce' : nonce1 = nonce2).
      by apply eqb_true_iff.
    rewrite (miIr mi_b1 mi_b2 eq_nonce') in neq_b; congruence.
  injection hyp as <- <-.
  eexists; split; try reflexivity.
by constructor.
+ (* CH: minless copy paste from above *)
  simpl in *.
  case: eqP => [eq_b|neq_b].
    rewrite eq_b mi_b2 in mi_b1.
    injection mi_b1 as <- <-.
    rewrite eqb_refl in hyp; injection hyp as <- <-.
    eexists; split; try reflexivity.
    by rewrite binop_leq_add2l; constructor.
  destruct (@SetoidDec.equiv_decb (QuasiAbstract.block mt)
       (SetoidDec.eq_setoid (QuasiAbstract.block mt))
       (@eq_word mt ops) nonce1 nonce2) eqn:eq_nonce.
  (* again, I would like to do
     apply eqb_true_iff in eq_nonce.
  *)
    assert (eq_nonce' : nonce1 = nonce2).
      by apply eqb_true_iff.
    rewrite (miIr mi_b1 mi_b2 eq_nonce') in neq_b; congruence.
  discriminate hyp. (* CH: not sure what I'm doing :) *)
Qed.

Lemma refine_ptr_inv w n b off base nonce :
  refine_val (Abstract.ValPtr (b,off)) w (PTR n) ->
  mi b = Some (base, nonce) ->
  w = (base + off)%w.
Proof.
intros rpt mi_b.
inversion rpt.
congruence.
Qed.

Definition refine_memory (amem : Abstract.memory mt) (qamem : QuasiAbstract.memory mt) :=
  forall b base nonce off, mi b = Some (base,nonce) ->
  match Abstract.getv amem (b,off), PartMaps.get qamem (base+off)%w with
  | None, None => True
  | Some v, Some w@M(nonce,ty) => refine_val v w ty
  | _, _ => False
 end.

Lemma refine_memory_get_int qamem (w1 w2 w3 : word mt) pt :
         refine_memory amem qamem -> refine_val (Abstract.ValPtr pt) w1 (PTR w2) ->
         PartMaps.get qamem w1 = Some w3@M(w2,INT) ->
         Abstract.getv amem pt = Some (Abstract.ValInt _ w3).
Proof.
intros rmem rpt get_w.
unfold refine_memory in rmem.
destruct pt as [b' off'].
(* Hit the too many names bug here too. *)
inversion rpt as [ | b base nonce off mi_b eq_b eq_w1 eq_nonce (* eq_off *)].
rewrite <-eq_nonce,<-eq_b,<-H2 in *.
specialize (rmem b base nonce off mi_b).
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
         refine_memory amem qamem -> refine_val (Abstract.ValPtr pt) w1 (PTR w2) ->
         PartMaps.get qamem w1 = Some (w3@M(w4,ty)) ->
         exists fr x, PartMaps.get amem (fst pt) = Some fr
         /\ index_list_Z (word_to_Z (snd pt)) fr = Some x
         /\ refine_val x w3 ty.
Proof.
intros rmem rpt get_w.
destruct pt as [b' off'].
simpl in *.
(* Too many names bug... *)
inversion rpt as [|b base nonce off mi_b eq_b eq_w1 eq_nonce].
rewrite <-eq_nonce,<-eq_b,<-H2 in *.
specialize (rmem b base nonce off mi_b).
rewrite <-eq_w1 in get_w.
rewrite get_w in rmem.
destruct (Abstract.getv amem (b, off)) eqn:get_b; try contradiction.
destruct (getv_mem get_b) as (fr & ? & ?).
exists fr; exists v; repeat split; easy.
Qed.

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

Lemma refine_memory_upd qamem qamem' w1 w2 pt ty n fr fr' x :
         refine_memory amem qamem -> refine_val (Abstract.ValPtr pt) w1 (PTR n) ->
         PartMaps.upd qamem w1 w2@M(n, ty) = Some qamem' ->
         PartMaps.get amem (fst pt) = Some fr ->
         update_list_Z (word_to_Z (snd pt)) x fr = Some fr' ->
         refine_val x w2 ty ->
         exists amem', PartMaps.upd amem (fst pt) fr' = Some amem'
         /\ refine_memory amem' qamem'.
Proof.
intros rmem rpt (* in_bounds_pt *) upd_w1 get_pt update_pt rx.
destruct (PartMaps.upd_defined fr' get_pt) as [amem' upd_pt].
exists amem'; split; try assumption.
intros b base nonce off mi_b.
have [eq_b|neq_b] := altP (b =P pt.1).
  rewrite eq_b.
  unfold Abstract.getv.
  simpl; rewrite (PartMaps.get_upd_eq upd_pt).
  destruct (eq_word off (snd pt)) as [eq_off|neq_off].
    rewrite eq_off. (* Why doesn't a -> intro pattern work above *)
    rewrite (update_list_Z_spec update_pt).
    assert (eq_w1 : (base + snd pt)%w = w1).
      replace pt with (fst pt, snd pt) in rpt.
        by inversion rpt; congruence.
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
  unfold Abstract.getv in rmem.
  simpl in rmem.
  rewrite eq_b get_pt in rmem.
  assert (neq_w1 : (base + off)%w <> w1).
    destruct pt as [b' off']; simpl in *.
    rewrite eq_b in mi_b.
    rewrite (refine_ptr_inv rpt mi_b).
    by intros eq_w1; apply addwI in eq_w1; congruence.
  by rewrite (PartMaps.get_upd_neq neq_w1 upd_w1).
specialize (rmem b base nonce off mi_b).
unfold Abstract.getv in *.
(* grr... *)
move/eqP: neq_b => neq_b.
generalize (PartMaps.get_upd_neq neq_b upd_pt).
unfold Abstract.frame. simpl.
move->.
simpl in *.
(* Why does fold fail?
fold (Abstract.getv amem (b,off)) in *.
*)
change (match PartMaps.get amem b with
           | Some fr0 => index_list_Z (word_to_Z off) fr0
           | None => None
           end)
with (Abstract.getv amem (b,off)) in *.

destruct (eq_word (base + off) w1) as [eq_w1|neq_w1].
  rewrite <-eq_w1 in upd_w1.
  rewrite (PartMaps.get_upd_eq upd_w1).
  destruct (Abstract.getv amem (b, off)) eqn:get_b.
    assert (lt_off := size_getv get_b).
    destruct pt as [b' off']; simpl in *; revert eq_w1.
    inversion rpt as [|? ? ? ? mi_pt].
    assert (lt_off' : word_to_Z off' < size amem b').
      by apply (size_update get_pt mi_pt update_pt).
    intros overlap.
    assert (eq_b' := mi_disjoints mi_b mi_pt overlap lt_off lt_off').
    congruence.
  destruct (PartMaps.upd_inv upd_w1) as [? get_w1].
  by rewrite get_w1 in rmem.
by rewrite (PartMaps.get_upd_neq neq_w1 upd_w1).
Qed.

Definition refine_registers (aregs : Abstract.registers mt)
                            (qaregs : QuasiAbstract.registers mt) :=
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
by destruct v as [w [ty|]]; try easy; exists w; exists ty.
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
  PartMaps.get qaregs n = Some w@V(INT) ->
  PartMaps.get aregs n = Some (Abstract.ValInt _ w).
Proof.
intros rregs get_n.
specialize (rregs n).
rewrite get_n in rregs.
destruct (PartMaps.get aregs n); try contradiction.
by inversion rregs.
Qed.

Lemma refine_registers_get_ptr aregs qaregs (n : common.reg mt) w b :
  refine_registers aregs qaregs ->
  PartMaps.get qaregs n = Some w@V(PTR b) ->
  exists pt, refine_val (Abstract.ValPtr pt) w (PTR b) /\
    PartMaps.get aregs n = Some (Abstract.ValPtr pt).
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
destruct (eq_reg r' r) as [->|neq_rr'].
  rewrite (PartMaps.get_upd_eq upd_r_a).
  by rewrite (PartMaps.get_upd_eq upd_r_qa).
rewrite (PartMaps.get_upd_neq neq_rr' upd_r_a).
rewrite (PartMaps.get_upd_neq neq_rr' upd_r_qa).
by apply rregs.
Qed.

Definition refine_state (ast : Abstract.state mt) (qast : QuasiAbstract.state mt) :=
  let '(Abstract.mkState amem aregs apc) := ast in
  match qast with
  | QuasiAbstract.mkState qamem qaregs w@V(ty) =>
    refine_memory amem qamem
      /\ refine_registers aregs qaregs
      /\ refine_val (Abstract.ValPtr apc) w ty
  | _ => False
  end.

(*
Definition refine_syscall (asc : Abstract.syscall mt) (qasc : QuasiAbstract.syscall mt) :=
  Abstract.address asc = QuasiAbstract.address qasc
  /\ forall ast qast, refine_state ast qast ->
    ohrel refine_state (Abstract.sem asc ast) (QuasiAbstract.sem qasc qast).

Lemma refine_syscall_sem asc qasc ast qast qast' :
  refine_syscall asc qasc ->
  QuasiAbstract.sem qasc qast = Some qast' ->
  refine_state ast qast ->
  exists ast', Abstract.sem asc ast = Some ast' /\ refine_state ast' qast'.
Proof.
intros [_ rsc] sem_asc rst.
specialize (rsc ast qast rst); revert rsc.
rewrite sem_asc.
destruct (Abstract.sem asc ast) as [ast'|]; try easy.
by intros rst'; exists ast'; split.
Qed.

Axiom refine_syscalls : forall amem, meminj amem -> list (Abstract.syscall mt) -> list (QuasiAbstract.syscall mt) -> Prop.
*)

(*
Axiom refine_syscalls_get : forall asc qasc w sc, refine_syscalls mi asc qasc ->
  QuasiAbstract.get_syscall qasc w = Some sc ->
  exists sc', Abstract.get_syscall asc w = Some sc'
    /\ refine_syscall sc' sc.
*)

End memory_injections.

Hint Constructors refine_val refine_val.
Hint Resolve get_mem_memv.

Lemma refine_pc_inv amem (mi : meminj amem) nonce apcb apci pc :
  refine_val mi (Abstract.ValPtr (apcb, apci)) pc (PTR nonce) ->
  exists base, mi apcb = Some (base, nonce) /\ (base + apci)%w = pc.
Proof.
intros rpc; inversion rpc.
by exists base; split.
Qed.

Lemma backward_simulation ast (mi : meminj (Abstract.mem ast)) qast qast' qasc :
  refine_state mi ast qast -> (* refine_syscalls mi asc qasc -> *) QuasiAbstract.step qasc qast qast' ->
  exists ast', Abstract.step ast ast' /\ refine_state mi ast' qast'.
Proof.
destruct ast as [amem aregs [apcb apci]].
intros rst step_qabs.
destruct step_qabs; generalize rst; intros (rmem & rregs & rpc);
assert (rpc_inv := refine_pc_inv rpc); destruct rpc_inv as (rpcb & mi_apcb & rpci);
repeat match goal with
  | R1W : PartMaps.get ?reg ?r = Some ?v |- _ =>
    match v with
    | _@V(INT) => eapply (refine_registers_get_int rregs) in R1W
    | _@V(PTR _) => eapply (refine_registers_get_ptr rregs) in R1W; destruct R1W as ((? & ?) & ? & ?)
    | _ => eapply (refine_registers_get rregs) in R1W; destruct R1W as (? & ? & ?)
    end
  end;
repeat match goal with
  MEM1 : PartMaps.get ?mem ?w1 = Some ?v |- _ =>
    match v with
    | _@M(_,INT) => eapply (refine_memory_get_int rmem) in MEM1; [|by eauto]
    | _ => eapply (refine_memory_get rmem) in MEM1; [|by eauto]; destruct MEM1 as (? & ? & ? & ? & ?)
    end
  end;
try match goal with
  | BINOP : QuasiAbstract.lift_binop ?f ?v1 ?v2 = Some _ |- _ =>
    eapply refine_binop in BINOP; [|by eauto|by eauto]; destruct BINOP as (? & ? & ?)
  end;
try match goal with
  | UPD : PartMaps.upd ?reg ?r ?v = Some _ |- _ =>
    eapply (refine_registers_upd rregs) in UPD; [|by eauto]; destruct UPD as (? & ? & ?)
  | |- _ => idtac
  end;
try match goal with
  | UPD : PartMaps.upd ?mem ?w1 ?v = Some _ |- _ =>
    eapply (refine_memory_upd rmem) in UPD; [|by eauto|by eauto|by eauto|by eauto]; destruct UPD as (? & ? & ?)
  end;
try match goal with
  | GETCALL : QuasiAbstract.get_syscall ?qasc ?w = Some _,
    CALL : QuasiAbstract.sem ?sc ?st = Some _ |- _ =>
    eapply (refine_syscalls_get rsc) in GETCALL; destruct GETCALL as (? & ? & ?);
    eapply refine_syscall_sem in CALL; [|by eauto|by eauto]; destruct CALL as (? & ? & ?)
  end;
repeat try match goal with
  | def := _ |- _ => unfold def
  end; try (eexists; split;
[econstructor (by eauto)
| repeat (try split; try eassumption);
by simpl; rewrite <-rpci, <-addwA; econstructor; eassumption]).

(* STORE *)
destruct (valid_update H7 x) as (? & ?).
eapply (refine_memory_upd rmem) in UPD; [|by eauto|by eauto|by eauto|by eauto]; destruct UPD as (? & ? & ?).
eexists; split;
[econstructor (by eauto)
| repeat (try split; try eassumption);
by simpl; rewrite <-rpci, <-addwA; econstructor; eassumption].

(* The side condition failed to be discharged *)
eapply (refine_registers_upd rregs) in UPD.
destruct UPD as (? & ? & ?).
by eexists; split; econstructor (by eauto).
by rewrite -rpci -addwA; constructor.

(* TODO: deal only with alloc and free syscalls *)
admit.
Qed.

(*
Lemma forward_simulation ast ast' qast asc qasc :
  refine_state ast qast -> refine_syscalls asc qasc -> Abstract.step asc ast ast' ->
  exists qast', QuasiAbstract.step qasc qast qast' /\ refine_state ast' qast'.
Proof.
destruct ast as [[[amem aregs] apc] abl].
destruct qast as [[qamem qaregs] [qapcv qapclbl]].
intros rst rsc step_abs.
destruct step_abs; eexists; esplit.
*)

End refinement.