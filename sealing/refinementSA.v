Require Import List. Import ListNotations.
Require Import Coq.Classes.SetoidDec.
Require Import utils common symbolic.symbolic.
Require Import symbolic_sealing sealing.classes sealing.abstract.

Section RefinementSA.

Import PartMaps.

Context {t : machine_types}
        {ops : machine_ops t}
        {opss : machine_ops_spec ops}

        {sk : sealing_key}
        {sko : sealing_key_ops}

        {scr : @syscall_regs t}
        {ssa : @sealing_syscall_addrs t}

        {smemory : Type}
        {sm : partial_map smemory (word t) (atom (word t) SymSeal.stag)}
        {smemspec : axioms sm}

        {sregisters : Type}
        {sr : partial_map sregisters (reg t) (atom (word t) SymSeal.stag)}
        {sregspec : axioms sr}

        {amemory : Type}
        {am : partial_map amemory (word t) (AbsSeal.value t)}
        {amemspec : axioms am}

        {aregisters : Type}
        {ar : partial_map aregisters (reg t) (AbsSeal.value t)}
        {aregspec : axioms ar}.

(* At the moment we're considering (morally) the same key generation
   at both levels and the identity mapping on keys. We could consider
   relaxing this in the future, and go in the direction of Maxime's
   "memory injections", just that extended to dynamic allocation. The
   main problem with this extension is that key generation (and
   allocation) is allowed to fail, and if the key generators at
   different levels fail at different times both directions of the
   refinement proof will break. Some possible solutions:

   0. What I started doing here: use (morally) the same generator at
      both levels; this is simple, but weak (it requires abstract
      allocation to be fully concrete). It also seems hard to adapt to
      Maxime's setting in which _different_ things need to be
      generated at the different levels, especially if the abstract
      block type is to be kept abstract. This also requires that a lot
      of information from the lower levels of abstraction is exposed
      to the higher levels in order to implement the same
      generator. This is quite natural for key generation (where
      remembering all past keys also helps make correctness more
      obvious), but a lot more of a pain for allocation.

   1. Assume that the generators at the two levels have the same
      failure behavior. This assumption should be enough to show
      refinement. Is this the _minimal_ assumption needed to make the
      proof go through? How easy/hard would be to justify it? It would
      be a huge leap of faith to do so without proof: this is
      basically refinement preservation for the allocation system call
      and for one the high-level allocator might not even have enough
      information to do the same as the lower one. It seems anyway a
      weaker condition than 0. It would still require exposing /
      duplicating low-level details at the higher levels of
      abstraction in order to satisfy such a condition.

   2. Require that the generators are complete wrt the space of keys
      they draw from, i.e. they are only allowed to return None if all
      possible keys were already generated. This seems to imply 1,
      without implying 0. Unclear how well this would work for
      allocation. For one, this would expose the size of the heap, the
      maximal size of the allocator's data structures, the size of the
      color space, etc. at the abstract level. Alternatives 1 and 2
      seem actually quite similar; 2 is just a specific way of
      achieving 1. Is it the only reasonable way of achieving 1?

   3. For alternatives 0-2 I assumed determinism at all levels and
      targetted two-way refinement. Another alternative would be to
      allow the generation / allocation on the abstract machine to
      fail non-deterministically, at any point. This would sacrifice
      forward simulation in order to prove backwards simulation wrt a
      very abstract machine. In the sealing abstract machine this
      would correspond to wrapping the mkkey_f function in a relation
      with an additional failure rule. It would allow us to
      take the next step and make the actual chosen key also
      non-deterministic (completely dropping mkkey_f). This solution
      might not be so bad, especially if we keep 2-way refinement for
      the concrete-symbolic level, which would put a bound on the
      "amount of forward refinement" we actually lose. We could say
      yes the final statement allows it, but testing at the concrete
      level showed that it we don't have a trivial implementation that
      always fails. *)

(* Could consider writing this in relational style (inductive relation) *)
Definition refine_val_atom (v : AbsSeal.value t)
                           (a : atom (word t) SymSeal.stag) : Prop :=
  match v,a with
  | AbsSeal.VData w    , w'@(SymSeal.DATA)      => w = w'
  | AbsSeal.VKey k     ,  _@(SymSeal.KEY k')    => k = k'
  | AbsSeal.VSealed w k, w'@(SymSeal.SEALED k') => w = w' /\ k = k'
  | _                  , _                      => False
  end.

Definition refine_mem (amem : amemory) (smem : smemory) : Prop :=
  forall w,
    match get amem w, get smem w with
    | None  , None   => True
    | Some v, Some a => refine_val_atom v a
    | _     , _      => False
    end.

Definition refine_reg (areg : aregisters) (sreg : sregisters) : Prop :=
  forall w,
    match get areg w, get sreg w with
    | None  , None   => True
    | Some v, Some a => refine_val_atom v a
    | _     , _      => False
    end.

Definition refine_pc (w : word t) (a : atom (word t) SymSeal.stag) : Prop :=
  match a with
  | w'@SymSeal.DATA => w = w'
  | _               => False
  end.

(* Instantiating mkkey_f at abstract level to something
   corresponding to what's happening at the symbolic level. *)

Variable min_key : key. (* the initial key for the symbolic machine *)
Variable key_lt : key -> key -> bool.

Definition kmax (ks : list key) : key :=
   List.fold_left (fun kmax k => if key_lt kmax k then k else kmax) ks min_key.

Definition inc_key_opt k :=
  if k == max_key then None
                  else Some (inc_key k).

Section WithDoNotation.
Import DoNotation.

Definition mkkey_f (ks : list key) : option (list key * key) :=
  do k <- inc_key_opt (kmax ks);
  Some (k::ks,k).

End WithDoNotation.

Hypothesis inc_max_not_in : forall ks,
  kmax ks =/= max_key ->
   ~ In (inc_key (kmax ks)) ks.

Program Instance gen_key_inst : AbsSeal.key_generator := {
  mkkey_f := mkkey_f
}.
Next Obligation.
  unfold mkkey_f in *. unfold bind in H.
  remember (inc_key_opt (kmax ks)) as o. destruct o as [k'|].
  - inversion H. subst. split; [|split].
    + unfold inc_key_opt in *.
      destruct (equiv_dec (kmax ks) max_key). congruence.
      inversion Heqo. eauto using inc_max_not_in.
    + left; reflexivity.
    + right; assumption.
  - inversion H.
Qed.

Definition refine_ins (keys : list key) (next_key : key) : Prop :=
  match mkkey_f keys with
  | Some (_, k) => k = next_key
  | _           => True (* ??? *)
  end.

Definition astate := @AbsSeal.state t sk amemory aregisters.
Definition sstate := @Symbolic.state t SymSeal.sym_sealing.

Definition refine_state (ast : astate) (sst : sstate) : Prop :=
  let '(AbsSeal.State amem areg apc akeys) := ast in
  let '(Symbolic.State smem sreg spc skey) := sst in
  refine_mem amem smem /\
  refine_reg areg sreg /\
  refine_pc apc spc /\
  refine_ins akeys skey.

Ltac gdep x := generalize dependent x.
Ltac split3 := split; [| split].
Ltac split4 := split; [| split3].

Lemma refine_pc_inv : forall apc spc tpc,
  refine_pc apc spc@tpc ->
  apc = spc.
Proof.
  intros apc spc tpc ref. unfold refine_pc in ref.
  destruct tpc; try contradiction ref; assumption.
Qed.

Lemma refine_get_mem_inv : forall amem smem pc a,
  refine_mem amem smem ->
  get smem pc = Some a ->
  exists v, get amem pc = Some v /\ refine_val_atom v a.
Proof.
  intros amem smem pc a ref sget.
  unfold refine_mem in ref. specialize (ref pc).
  rewrite sget in ref. destruct (get amem pc).
  + eexists; split; now trivial.
  + contradiction ref.
Qed.

Lemma refine_get_reg_inv : forall areg sreg pc a,
  refine_reg areg sreg ->
  get sreg pc = Some a ->
  exists v, get areg pc = Some v /\ refine_val_atom v a.
Admitted. (* same as above *)

Lemma refine_val_data : forall v w,
  refine_val_atom v w@SymSeal.DATA ->
  v = AbsSeal.VData _ w.
Proof.
  intros v w ref. destruct v; simpl in ref; try tauto; subst; reflexivity.
Qed.

Tactic Notation "unfold_next_state_in" ident(H) :=
  try unfold Symbolic.next_state_reg in H;
  try unfold Symbolic.next_state_pc in H;
  try unfold Symbolic.next_state_reg_and_pc in H;
  try unfold Symbolic.next_state in H.

Lemma refine_upd_reg : forall aregs sregs sregs' r a v,
  refine_reg aregs sregs ->
  refine_val_atom v a ->
  upd sregs r a = Some sregs' -> 
  exists aregs', upd aregs r v = Some aregs' /\
                 refine_reg aregs' sregs'.
Proof.
  intros aregs sregs sregs' r a v rr rv up.
  apply (@upd_inv _ _ _ _ sregspec) in up. destruct up as [[w tg] ge].
  eapply (refine_get_reg_inv _ _ _ _ rr) in ge. destruct ge as [v' [ge rva]].
(*
  apply (@upd_defined _ _ _ _ sregspec) with (val':=v) in ge. destruct ge as [aregs' up].
  exists aregs'. split. assumption.
*)
Admitted. (* TODO finish *)

Lemma backward_simulation : forall ast sst sst',
  refine_state ast sst ->
  SymSeal.step sst sst' ->
  exists ast',
    AbsSeal.step ast ast' /\
    refine_state ast' sst'.
Proof.
  intros [amem aregs apc akeys]
         sst sst' ref sstep. gdep ref.
  destruct sstep; destruct sst as [smem sregs spc skey];
    injection ST; do 4 (intro H; symmetry in H; subst); clear ST;
    intros [rmem [rreg [rpc ris]]].
  - (* NOP case *)
    apply refine_pc_inv in rpc; symmetry in rpc; subst.
    apply (refine_get_mem_inv _ _ _ _ rmem) in PC.
      destruct PC as [iv [PC riv]].
    destruct ti; unfold_next_state_in NEXT; simpl in NEXT; try discriminate NEXT.
    injection NEXT; intro H; subst; clear NEXT.
    apply refine_val_data in riv. subst.
    eexists. split.
    + eapply AbsSeal.step_nop. reflexivity.
      unfold AbsSeal.decode. rewrite PC. now apply INST.
      reflexivity.
    + split4; now trivial.
  - (* CONST case *)
    (* copy paste *)
    apply refine_pc_inv in rpc; symmetry in rpc; subst.
    apply (refine_get_mem_inv _ _ _ _ rmem) in PC.
      destruct PC as [iv [PC riv]].
    destruct ti; unfold_next_state_in NEXT; simpl in NEXT; try discriminate NEXT.
    (* new *)
    apply bind_inv in NEXT. destruct NEXT as [sregs' [upd NEXT]].
    (* copy paste *)
    injection NEXT; intro H; subst; clear NEXT.
    apply refine_val_data in riv. subst.
    eexists. split.
    + eapply AbsSeal.step_const. reflexivity.
      unfold AbsSeal.decode. rewrite PC. now apply INST.
Admitted.
(*
    (* should use refine_upd_reg here *)
    + split4; now trivial.
*)

(* also refinement for our 3 system calls ... the abstract ones only
   have a description as step rules *)

End RefinementSA.