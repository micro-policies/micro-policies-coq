(* Why is common in concrete? *)
Require Import ZArith.

Require Import utils concrete.common memory_safety.abstract memory_safety.quasiabstract.

Require Import EquivDec.

Set Implicit Arguments.

Section refinement.

Import QuasiAbstract.Notations.

Context {mt : machine_types}
        {ops : machine_ops mt}
        {opss : machine_ops_spec ops}
        {ap : Abstract.abstract_params mt}
        {aps : Abstract.params_spec ap}
        {qap : QuasiAbstract.abstract_params mt}
        {qaps : QuasiAbstract.params_spec qap}
        {a_alloc : @Abstract.allocator _ ap}
        {qa_alloc : @QuasiAbstract.allocator _ qap}.

Section memory_injections.

Record meminj := Meminj {
  (* if b is allocated, mi b returns Some (w1,w2) where
     - w1 is the address of b's first memory location
     - w2 is b's pointer nonce
  *)
    mi :> Abstract.block -> option (word mt * word mt);
    mi_inj : forall x y, mi x = mi y -> x = y
  }.

Variable mi : meminj.

Definition ohrel (A B : Type) (rAB : A -> B -> Prop) sa sb : Prop :=
  match sa, sb with
    | None,   None   => True
    | Some a, Some b => rAB a b
    | _,      _      => False
  end.

(*
Inductive refine_val : Abstract.value mt -> QuasiAbstract.atom mt -> Prop :=
  | RefineInt : forall w, refine_val (Abstract.ValInt mt w) w@V(INT)
  | RefinePtr : forall b w i, mi b = Some w ->
                refine_val (Abstract.ValPtr (b,i)) (add_word w i)@V(PTR w).
*)

Inductive refine_val : Abstract.value mt -> word mt -> QuasiAbstract.type mt -> Prop :=
  | RefineInt : forall w, refine_val (Abstract.ValInt mt w) w INT
  | RefinePtr : forall b base nonce off, mi b = Some (base,nonce) ->
                refine_val (Abstract.ValPtr (b,off)) (add_word base off) (PTR nonce).

Lemma refine_val_injl x x' w ty : refine_val x w ty -> refine_val x' w ty -> x = x'.
Proof.
admit.
(*
intros [w|b w i mi_b].
  generalize (eq_refl w@V(INT)).
  generalize w@V(INT) at 1 3.
  intros a eq_a rx'a.
  now destruct rx'a; congruence.
generalize (eq_refl (w + i)%word@V(PTR w)).
generalize (w + i)%word@V(PTR w) at 1 3.
intros a eq_a rx'a.
destruct rx'a; try congruence.
injection eq_a as -> eq_sum.
rewrite (@mi_inj mi b b0); try congruence.
*)
(* Need a bit of arithmetic on words *)
Qed.

Lemma refine_binop f v1 w1 ty1 v2 w2 ty2 w3 ty3 : refine_val v1 w1 ty1 ->
  refine_val v2 w2 ty2 ->
  QuasiAbstract.lift_binop f w1@V(ty1) w2@V(ty2) = Some (w3,ty3) ->
  exists v3, Abstract.lift_binop f v1 v2 = Some v3 /\ refine_val v3 w3 ty3.
Proof.
(*
destruct f; intros [w1 | b1 w1 i1 mi_b1] [w2 | b2 w2 i2 mi_b2] H; try discriminate H.
injection H; intros <-; now eexists; split; [reflexivity|constructor].
injection H; intros <-.
eexists; split.
reflexivity.
*)
(* This depends on the actual binop_denote implem *)
(* eapply RefinePtr. *)
Admitted.

Lemma refine_ptr_rev b base nonce w : mi b = Some (base,nonce) ->
  refine_val (Abstract.ValPtr (b, w - base)%w) w (PTR nonce).
Proof.
intros ?.
assert (addwK : add_word base (w - base)%w = w).
  admit.
rewrite <-addwK at 2.
now constructor.
Qed.

Definition refine_memory (amem : Abstract.memory mt) (qamem : QuasiAbstract.memory mt) :=
  forall b base nonce off, mi b = Some (base,nonce) ->
  exists v w ty, Abstract.get_memv amem (b,off) = Some v
    /\ QuasiAbstract.get_mem qamem (base+off)%w = Some w@M(nonce,ty)
    /\ refine_val v w ty.

Lemma refine_memory_get amem qamem (b : Abstract.block) (base nonce off : word mt) 
           (x : Abstract.value mt) w ty :
         refine_memory amem qamem ->
         mi b = Some (base,nonce) ->
         QuasiAbstract.get_mem qamem (base + off)%w = Some w@M(nonce,ty) ->
         refine_val x w ty ->
         Abstract.get_memv amem (b, off) = Some x.
Proof.
intros rmem ? ? ?.
unfold refine_memory in rmem.
admit.
(* now rewrite <-rmem; eassumption. *)
Qed.

Lemma refine_memory_get_int amem qamem (w1 w2 w3 : word mt) pt :
         refine_memory amem qamem -> refine_val (Abstract.ValPtr pt) w1 (PTR w2) ->
         QuasiAbstract.get_mem qamem w1 = Some w3@M(w2,INT) ->
         Abstract.get_memv amem pt = Some (Abstract.ValInt _ w3).
           (* /\ refine_val w2 (Abstract.ValInt _ w3) w3@M(w2,INT). *)
Proof.
intros rmem rpt get_w.
unfold refine_memory in rmem.
inversion rpt as [ | b base nonce off mi_b eq_pt eq_w1].
rewrite <-H in *.
(* Why does this fail? : "Too many names"
inversion rpt as [|b w' i mi_b eq_pt eq_w eq_ty].
*)
destruct (rmem b base nonce off mi_b) as (v & w & ty & get_b & get_base & rvw).
rewrite eq_w1, get_w in get_base.
rewrite get_b.
injection get_base.
destruct rvw; try discriminate.
now intros _ ->.
Qed.

(* Why is amem not made implicit automatically ? *)
Lemma get_memv_mem amem base off v : Abstract.get_memv amem (base, off) = Some v ->
  exists fr, Abstract.get_mem amem base = Some fr
  /\ index_list_Z (word_to_Z off) fr = Some v.
Proof.
unfold Abstract.get_memv; simpl.
destruct (Abstract.get_mem amem base) as [fr|]; try discriminate.
now intros index_fr; exists fr; split.
Qed.

Lemma get_mem_memv amem base off v fr : Abstract.get_mem amem base = Some fr ->
  index_list_Z (word_to_Z off) fr = Some v ->
  Abstract.get_memv amem (base,off) = Some v.
Proof.
intros get_base index_off.
unfold Abstract.get_memv.
now simpl; rewrite get_base.
Qed.

Lemma refine_memory_get' amem qamem (w1 w2 w3 w4 : word mt) pt ty :
         refine_memory amem qamem -> refine_val (Abstract.ValPtr pt) w1 (PTR w2) ->
         QuasiAbstract.get_mem qamem w1 = Some (w3@M(w4,ty)) ->
         exists fr x, Abstract.get_mem amem (fst pt) = Some fr
         /\ index_list_Z (word_to_Z (snd pt)) fr = Some x 
         /\ refine_val x w3 ty.
Proof.
intros rmem rpt get_w.
unfold refine_memory in rmem.
inversion rpt as [|b base nonce off mi_b eq_pt eq_w1].
rewrite <-H in *.
(* Why does this fail? : "Too many names"
inversion rpt as [|b w' i mi_b eq_pt eq_w eq_ty].
*)
destruct (rmem b base nonce off mi_b) as (v & w & ty' & get_b & get_base & rvw).
destruct (get_memv_mem _ _ _ get_b) as (fr & ? & ?).
rewrite eq_w1, get_w in get_base.
injection get_base.
intros -> _ ->.
exists fr; exists v; repeat split; easy.
Qed.

Lemma refine_memory_upd amem qamem qamem' w1 w2 pt ty n fr fr' x :
         refine_memory amem qamem -> refine_val (Abstract.ValPtr pt) w1 (PTR n) ->
         QuasiAbstract.upd_mem qamem w1 w2@M(n, ty) = Some qamem' ->
         Abstract.get_mem amem (fst pt) = Some fr ->
         update_list_Z (word_to_Z (snd pt)) x fr = Some fr' ->
         refine_val x w2 ty ->
         exists amem', Abstract.upd_mem amem (fst pt) fr' = Some amem'
         /\ refine_memory amem' qamem'.
Proof.
intros rmem rpt upd_w1 get_pt update_pt rx.
destruct (PartMaps.upd_defined fr' get_pt) as [amem' upd_pt].
exists amem'; split; try assumption.
intros b base nonce off mi_b.
destruct (b =? fst pt)%Z eqn:eq_b.
  apply Z.eqb_eq in eq_b.
  rewrite eq_b.
  unfold Abstract.get_memv.
  simpl; rewrite (PartMaps.get_upd_eq upd_pt).
  destruct (eq_word off (snd pt)) as [->|neq_off].
    { exists x; exists w2; exists ty; repeat split; try assumption.
      + now rewrite (update_list_Z_spec update_pt).
      + assert (eq_w1 : (base + snd pt)%w = w1).
          replace pt with (fst pt, snd pt) in rpt.
            now inversion rpt; congruence.
          now destruct pt.
        rewrite eq_w1.
        rewrite (PartMaps.get_upd_eq upd_w1).
        assert (eq_n : n = nonce).
          replace pt with (fst pt, snd pt) in rpt.
            now inversion rpt; congruence.
          now destruct pt.
        congruence. }
  rewrite <-(update_list_Z_spec2 update_pt).
    { destruct (rmem b base nonce off mi_b) as (v & w & ty' & get_b & ? & ?).
      exists v; exists w; exists ty'; repeat split; try assumption.
      + unfold Abstract.get_memv in get_b. 
        simpl in get_b.
        now rewrite eq_b, get_pt in get_b.
      + assert (neq_w1 : (base + off)%w <> w1).
          admit.
        now rewrite (PartMaps.get_upd_neq neq_w1 upd_w1).
    }
  (* TODO: generic lemmas on injectivity and cancellation *)
  admit.
destruct (rmem b base nonce off mi_b) as (v & w & ty' & get_b & ? & ?).
exists v; exists w; exists ty'; repeat split; try assumption.
  unfold Abstract.get_memv in *.
  assert (neq_b : b <> fst pt).
    admit.
  rewrite (PartMaps.get_upd_neq neq_b upd_pt).
  simpl in *.
  destruct (Abstract.get_mem amem b); try discriminate.
  now rewrite get_b.
assert (neq_w1 : (base + off)%w <> w1).
  admit.
now rewrite (PartMaps.get_upd_neq neq_w1 upd_w1).
Qed.

Definition refine_registers (aregs : Abstract.registers mt)
                            (qaregs : QuasiAbstract.registers mt) :=
  forall n, match Abstract.get_reg aregs n, QuasiAbstract.get_reg qaregs n with
  | None, None => True
  | Some v, Some w@V(ty) => refine_val v w ty
  | _, _ => False
  end.

Lemma refine_registers_val aregs qaregs r v : refine_registers aregs qaregs ->
  QuasiAbstract.get_reg qaregs r = Some v ->
  exists w ty, v = w@V(ty).
Proof.
intros rregs get_r; specialize (rregs r); revert rregs.
rewrite get_r; destruct (Abstract.get_reg aregs r); try easy.
now destruct v as [w [ty|]]; try easy; exists w; exists ty.
Qed.

Lemma refine_registers_get aregs qaregs (n : common.reg mt) (x : Abstract.value mt) w ty :
  refine_registers aregs qaregs ->
  QuasiAbstract.get_reg qaregs n = Some w@V(ty) ->
  refine_val x w ty ->
  Abstract.get_reg aregs n = Some x.
Proof.
intros rregs qa_get rxx'.
generalize (rregs n).
rewrite qa_get.
destruct (Abstract.get_reg aregs n); try easy.
simpl; intros rvx.
now rewrite (refine_val_injl rxx' rvx).
Qed.

Lemma refine_registers_get' aregs qaregs (n : common.reg mt) w ty :
  refine_registers aregs qaregs ->
  QuasiAbstract.get_reg qaregs n = Some w@V(ty) ->
  exists x, refine_val x w ty /\ Abstract.get_reg aregs n = Some x.
Proof.
intros rregs qa_get.
generalize (rregs n).
rewrite qa_get.
destruct (Abstract.get_reg aregs n); try easy.
simpl; intros rvx.
now exists v; split.
Qed.

Lemma refine_registers_get_int aregs qaregs (n : common.reg mt) w :
  refine_registers aregs qaregs ->
  QuasiAbstract.get_reg qaregs n = Some w@V(INT) ->
  Abstract.get_reg aregs n = Some (Abstract.ValInt _ w).
Proof.
admit.
Qed.

Lemma refine_registers_get_ptr aregs qaregs (n : common.reg mt) w b :
  refine_registers aregs qaregs ->
  QuasiAbstract.get_reg qaregs n = Some w@V(PTR b) ->
  exists pt, refine_val (Abstract.ValPtr pt) w (PTR b) /\
    Abstract.get_reg aregs n = Some (Abstract.ValPtr pt).
Proof.
intros rregs qa_get.
generalize (rregs n).
rewrite qa_get.
destruct (Abstract.get_reg aregs n); try easy.
simpl; intros rvx.
destruct v as [|pt].
  now inversion rvx.
now exists pt; split.
Qed.

Lemma refine_registers_upd aregs qaregs qaregs' r v w ty :
  refine_registers aregs qaregs ->
  QuasiAbstract.upd_reg qaregs r w@V(ty) = Some qaregs' ->
  refine_val v w ty ->
  exists areg',
    Abstract.upd_reg aregs r v = Some areg' /\
    refine_registers areg' qaregs'.
admit.
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
now intros rst'; exists ast'; split.
Qed.

Axiom refine_syscalls : meminj -> list (Abstract.syscall mt) -> list (QuasiAbstract.syscall mt) -> Prop.

Axiom refine_syscalls_get : forall asc qasc w sc, refine_syscalls mi asc qasc ->
  QuasiAbstract.get_syscall qasc w = Some sc ->
  exists sc', Abstract.get_syscall asc w = Some sc'
    /\ refine_syscall sc' sc.

End memory_injections.

Hint Constructors refine_val refine_val.
Hint Resolve refine_ptr_rev.
Hint Resolve get_mem_memv.

(*
Hint Resolve refine_memory_get_int.
*)

(* Should the blocks of the abstract machine be words or integers? *) (* In the
second case, the axiom below should be refined. using a bound on the memory
size. *)

Lemma refine_pc_inv mi nonce apcb apci pc :
  refine_val mi (Abstract.ValPtr (apcb, apci)) pc (PTR nonce) ->
  exists base, mi apcb = Some (base, nonce) /\ (base + apci)%w = pc.
Proof.
intros H; inversion H.
now exists base; split.
Qed.

(*
Lemma refine_registers_upd areg creg r val w :
  refine_registers areg creg ->
  Concrete.get_reg creg r = val@(tag_to_word USER) ->
  exists areg',
    Abstract.upd_reg areg r w = Some areg' /\
    refine_registers areg' (Concrete.upd_reg creg r w@(tag_to_word USER)).
*)

(*
Context `{!Abstract.allocator (t := mt)}.
Context `{!QuasiAbstract.allocator (t := mt)}.
*)

(*
generalize (valid_update _ _ H4).
*)

(*
Hint Extern 1 (update_list_Z ?i ?v ?fr = Some _) =>
  match goal with
  | INDEX : index_list_Z i fr = Some _ |- _ =>
    destruct (valid_update _ _ INDEX fr) as (? & ?)
  end.
*)

Lemma backward_simulation mi ast qast qast' asc qasc :
  refine_state mi ast qast -> refine_syscalls mi asc qasc -> QuasiAbstract.step qasc qast qast' ->
  exists mi' ast', Abstract.step asc ast ast' /\ refine_state mi' ast' qast'.
Proof.
destruct ast as [amem aregs [apcb apci]].
intros rst rsc step_qabs.
destruct step_qabs; generalize rst; intros [rmem [rregs rpc]];
assert (rpc_inv := refine_pc_inv rpc); destruct rpc_inv as [rpcb [mi_apcb rpci]];
repeat match goal with
  | R1W : QuasiAbstract.get_reg ?reg ?r = Some ?v |- _ =>
    match v with
    | _@V(INT) => eapply (refine_registers_get_int _ rregs) in R1W
    | _@V(PTR _) => eapply (refine_registers_get_ptr _ rregs) in R1W; destruct R1W as ((? & ?) & ? & ?)
    | _ => eapply (refine_registers_get' _ rregs) in R1W; destruct R1W as (? & ? & ?)
    end
  end;
repeat match goal with
  MEM1 : QuasiAbstract.get_mem ?mem ?w1 = Some ?v |- _ =>
    match v with
    | _@M(_,INT) => eapply (refine_memory_get_int rmem) in MEM1; [|now eauto]
    | _ => eapply (refine_memory_get' rmem) in MEM1; [|now eauto]; destruct MEM1 as (? & ? & ? & ? & ?)
    end
  end;
try match goal with
  | BINOP : QuasiAbstract.lift_binop ?f ?v1 ?v2 = Some _ |- _ =>
    eapply refine_binop in BINOP; [|now eauto|now eauto]; destruct BINOP as (? & ? & ?)
  end;
try match goal with
  | UPD : QuasiAbstract.upd_reg ?reg ?r ?v = Some _ |- _ =>
    eapply (refine_registers_upd _ rregs) in UPD; [|now eauto]; destruct UPD as (? & ? & ?)
  end;
try match goal with
  | UPD : QuasiAbstract.upd_mem ?mem ?w1 ?v = Some _ |- _ =>
    eapply (refine_memory_upd rmem) in UPD; [|now eauto|now eauto|now eauto|now eauto]; destruct UPD as (? & ? & ?)
  end;
try match goal with
  | GETCALL : QuasiAbstract.get_syscall ?qasc ?w = Some _,
    CALL : QuasiAbstract.sem ?sc ?st = Some _ |- _ =>
    eapply (refine_syscalls_get _ rsc) in GETCALL; destruct GETCALL as (? & ? & ?);
    eapply refine_syscall_sem in CALL; [|now eauto|now eauto]; destruct CALL as (? & ? & ?)
  end;
repeat try match goal with
  | def := _ |- _ => unfold def
  end; try (eexists; eexists; split;
[econstructor (now eauto)
| repeat (try split; try eassumption);
now simpl; rewrite <-rpci, <-addwA; constructor]).

destruct (valid_update H4 x) as (? & ?).
eapply (refine_memory_upd rmem) in UPD; [|now eauto|now eauto|now eauto|now eauto]; destruct UPD as (? & ? & ?).
eexists; eexists; split;
[econstructor (now eauto)
| repeat (try split; try eassumption);
now simpl; rewrite <-rpci, <-addwA; constructor].

(* The side failed to be discharged *)
eapply (refine_registers_upd _ rregs) in UPD.
 destruct UPD as (? & ? & ?).

Focus 2.
rewrite <-rpci, <-addwA.
constructor.
now eauto.

eexists; eexists; split;
[econstructor (now eauto)
| repeat (try split; try eassumption);
now simpl; rewrite <-rpci, <-addwA; constructor].
Qed.

Print Assumptions backward_simulation.


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