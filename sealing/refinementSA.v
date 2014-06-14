Require Import List. Import ListNotations.
Require Import Coq.Classes.SetoidDec.
Require Import utils common symbolic.symbolic.
Require Import symbolic_sealing sealing.classes sealing.abstract.

Section RefinementSA.

Set Implicit Arguments.

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

(* We make no assumption about the pc tag, since it's unused in the policy *)
Definition refine_pc (w : word t) (a : atom (word t) SymSeal.stag) : Prop :=
  w = val a.

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

(* TODO: reduce these to hypotheses about order and inc_key and stuff *)
Hypothesis inc_max_not_in : forall ks,
  kmax ks =/= max_key ->
   ~ In (inc_key (kmax ks)) ks.

Hypothesis kmax_cons_inc_key_kmax : forall ks,
  kmax ks =/= max_key ->
  kmax (inc_key (kmax ks) :: ks) = inc_key (kmax ks).

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
  | _           => False (* ??? *)
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
  destruct tpc; try contradiction ref; now eauto.
Qed.

Lemma refine_get_mem_inv : forall amem smem w a,
  refine_mem amem smem ->
  get smem w = Some a ->
  exists v, get amem w = Some v /\ refine_val_atom v a.
Proof.
  intros amem smem pc a ref sget.
  unfold refine_mem in ref. specialize (ref pc).
  rewrite sget in ref. destruct (get amem pc).
  + eexists; split; now trivial.
  + contradiction ref.
Qed.

Lemma refine_get_reg_inv : forall areg sreg r a,
  refine_reg areg sreg ->
  get sreg r = Some a ->
  exists v, get areg r = Some v /\ refine_val_atom v a.
Admitted. (* same as above *)

Lemma refine_val_data : forall v w,
  refine_val_atom v w@SymSeal.DATA ->
  v = AbsSeal.VData w.
Proof.
  intros v w ref. destruct v; simpl in ref; try tauto; subst; reflexivity.
Qed.

Tactic Notation "unfold_next_state_in" ident(H) :=
  try unfold Symbolic.next_state_reg in H;
  try unfold Symbolic.next_state_pc in H;
  try unfold Symbolic.next_state_reg_and_pc in H;
  try unfold Symbolic.next_state in H.

Lemma refine_upd_reg1 : forall aregs sregs sregs' r a v,
  refine_reg aregs sregs ->
  refine_val_atom v a ->
  upd sregs r a = Some sregs' ->
  exists aregs', upd aregs r v = Some aregs'.
Proof.
  intros aregs sregs sregs' r a v rr rv up. pose proof up as up'.
  apply (@upd_inv _ _ _ _ sregspec) in up. destruct up as [[w tg] ge].
  eapply (refine_get_reg_inv _ rr) in ge. destruct ge as [v' [ge rva]].
  eapply (@upd_defined _ _ _ _ aregspec) in ge. destruct ge as [aregs' up].
  exists aregs'. eassumption.
Qed.

Lemma refine_upd_reg2 : forall aregs aregs' sregs sregs' r a v,
  refine_reg aregs sregs ->
  refine_val_atom v a ->
  upd sregs r a = Some sregs' -> 
  upd aregs r v = Some aregs' ->
  refine_reg aregs' sregs'.
Proof.
  intros aregs aregs' sregs sregs' r a v rr rva u1 u2.
  intro r'. destruct (eq_reg r r') as [[]|].
  - erewrite (@get_upd_eq _ _ _ _ aregspec).
    erewrite (@get_upd_eq _ _ _ _ sregspec).
    eassumption. eassumption. eassumption.
  - erewrite (@get_upd_neq _ _ _ _ sregspec); [| | apply u1].
    erewrite (@get_upd_neq _ _ _ _ aregspec); [| | apply u2].
    apply rr.
    admit. admit. (* silly equality stuff *)
Admitted.

Lemma refine_upd_reg3 : forall aregs sregs sregs' r a v,
  refine_reg aregs sregs ->
  refine_val_atom v a ->
  upd sregs r a = Some sregs' -> 
  exists aregs', upd aregs r v = Some aregs' /\
                 refine_reg aregs' sregs'.
Proof.
  intros aregs sregs sregs' r a v rr rv up.
  destruct (refine_upd_reg1 _ _ _ rr rv up) as [aregs' up'].
  eauto using refine_upd_reg2.
Qed.

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
  - (* NOP *)
    apply refine_pc_inv in rpc; symmetry in rpc; subst.
    apply (refine_get_mem_inv _ rmem) in PC.
      destruct PC as [iv [PC riv]].
    destruct ti; unfold_next_state_in NEXT; simpl in NEXT; try discriminate NEXT.
    injection NEXT; intro H; subst; clear NEXT.
    apply refine_val_data in riv. subst.
    eexists. split.
    + eapply AbsSeal.step_nop; [reflexivity | | reflexivity].
      unfold AbsSeal.decode. rewrite PC. now apply INST.
    + split4; now trivial.
  - (* CONST *)
    (* copy paste *)
    apply refine_pc_inv in rpc; symmetry in rpc; subst.
    apply (refine_get_mem_inv _ rmem) in PC.
      destruct PC as [iv [PC riv]].
    destruct ti; unfold_next_state_in NEXT; simpl in NEXT; try discriminate NEXT.
    (* new *)
    apply bind_inv in NEXT. destruct NEXT as [sregs' [upd NEXT]].
    (* copy paste from above *)
    injection NEXT; intro H; subst; clear NEXT.
    apply refine_val_data in riv. subst.
    (* the rest is quite different *)
    edestruct refine_upd_reg3 as [aregs' [H1 H2]]; [eassumption | | eassumption |].
    instantiate (1:= AbsSeal.VData (imm_to_word n)). reflexivity.
    eexists. split.
    + eapply AbsSeal.step_const; [reflexivity | | | reflexivity]. (* extra goal *)
      unfold AbsSeal.decode. rewrite PC. now apply INST.
      eassumption.
    + split4; now trivial.
  - admit. (* MOV *)
  - admit. (* BINOP *)
  - admit. (* LOAD *)
  - admit. (* STORE *)
  - admit. (* JUMP *)
  - admit. (* BNZ *)
  - (* JAL - not system call *)
    (* copy paste (all cases) *)
    apply refine_pc_inv in rpc; symmetry in rpc; subst.
    apply (refine_get_mem_inv _ rmem) in PC.
      destruct PC as [iv [PC riv]].
    destruct ti; unfold_next_state_in NEXT; simpl in NEXT; try discriminate NEXT.
    (* copy paste, twice (CONST) *)
    apply bind_inv in NEXT. destruct NEXT as [st [stag NEXT]].
    apply bind_inv in NEXT. destruct NEXT as [sregs' [upd' NEXT]].
    (* copy paste (all cases) *)
    injection NEXT; intro H; subst; clear NEXT.
    apply refine_val_data in riv. subst.
    (* new *)
    destruct t1; try discriminate stag. injection stag; intro; subst; clear stag.
    (* new - reading a register *)
    destruct (refine_get_reg_inv _ rreg RW) as [v [g rva]].
    destruct v; try contradiction rva. simpl in rva. subst.
    (* the rest similar to CONST *)
    edestruct refine_upd_reg3 as [aregs' [H1 H2]]; [eassumption | | eassumption |].
    instantiate (1:= AbsSeal.VData (apc + 1)%w). reflexivity.
    eexists. split.
    + eapply AbsSeal.step_jal; [reflexivity | | | | | reflexivity].
      unfold AbsSeal.decode. rewrite PC. now apply INST.
      eassumption.
      simpl in *.
        (* not the right way of doing it *)
        destruct (mkkey_addr ==b w). discriminate NOTCALL.
        destruct (seal_addr ==b w). discriminate NOTCALL.
        destruct (unseal_addr ==b w). discriminate NOTCALL.
        admit. (* follows from NOTCALL, damn it! *)
      eassumption.
    + split4; now trivial.
  - (* JAL - system call *)
    (* copy paste (all cases) -- using ALLOWED instead of NEXT *)
    apply refine_pc_inv in rpc; symmetry in rpc; subst.
    apply (refine_get_mem_inv _ rmem) in PC.
      destruct PC as [iv [PC riv]].
    destruct ti; simpl in ALLOWED; try discriminate ALLOWED.
    (* copy paste (all cases) *)
    apply refine_val_data in riv. subst.
    (* new -- useful only for t1, rvec ignored by semantic bug *)
    destruct t1; try discriminate ALLOWED.
    injection ALLOWED; intro H; subst; clear ALLOWED.
    (* same as for normal JAL - reading a register *)
    destruct (refine_get_reg_inv _ rreg RW) as [v [g rva]].
    destruct v; try contradiction rva. simpl in rva. subst.
    (* done with RW *)
    clear RW.
    (* figuring out which system call it was *)
    simpl in GETCALL.
    destruct (mkkey_addr ==b w);
      [| destruct (seal_addr ==b w);
      [| destruct (unseal_addr ==b w); [| discriminate GETCALL]]];
      injection GETCALL; intro; subst; clear GETCALL.
    + {(* mkkey *)
    assert (mkkey_addr = w) by admit. subst.
    simpl in CALL.
    (* this should be easy, but it's not *)
    destruct (@equiv_dec (@key sk) (eq_setoid (@key sk))
                 (@eq_key sk sko) skey (@max_key sk sko)). discriminate CALL.
    apply bind_inv in CALL. destruct CALL as [sreg' [upd CALL]].
    injection CALL; intro H; subst; clear CALL.
    assert (exists new_keys, mkkey_f akeys = Some (new_keys, skey)) as H.
      simpl. unfold refine_ins in ris.
      destruct (mkkey_f akeys) as [[x1 x2] | ]. subst. eauto. contradiction.
    destruct H as [new_keys ?].
    (* dealing with the result -- similar to CONST *)
    edestruct refine_upd_reg3 as [aregs' [H1 H2]]; [eassumption | | eassumption |].
    instantiate (1:= (AbsSeal.VKey _ skey)). reflexivity.
    eexists. split.
    + eapply AbsSeal.step_mkkey; [reflexivity | | | | | reflexivity].
      unfold AbsSeal.decode. rewrite PC. now apply INST.
      assumption.
      simpl; eassumption.
      eassumption.
    + split4; trivial. reflexivity.
      (* the interesting part: reestablish refinement on keys *)
      unfold refine_ins.
      unfold mkkey_f in H. apply bind_inv in H. destruct H as [new_key [H' H'']].
      injection H''; intros; subst; clear H''.
      unfold inc_key_opt in H'.
      destruct (@equiv_dec (@key sk) (eq_setoid (@key sk))
             (@eq_key sk sko) (kmax akeys) (@max_key sk sko)). discriminate H'.
      injection H'; intros; subst; clear H'.
      unfold mkkey_f, bind.
      rewrite kmax_cons_inc_key_kmax; [| assumption].
      unfold inc_key_opt.
      destruct (@equiv_dec (@key sk) (eq_setoid (@key sk))
               (@eq_key sk sko) (@inc_key sk sko (kmax akeys))
               (@max_key sk sko)). contradiction.
      reflexivity.
    }
    + {(* seal *)
    assert (seal_addr = w) by admit. subst.
    (* break up the effects of the system call *)
    simpl in CALL.
    apply bind_inv in CALL. destruct CALL as [[p tp] [gp CALL]].
    destruct tp; try discriminate CALL.
    apply bind_inv in CALL. destruct CALL as [[? tk] [gk CALL]].
    destruct tk; try discriminate CALL.
    apply bind_inv in CALL. destruct CALL as [sregs' [up CALL]].
    injection CALL; intro H; subst; clear CALL.
    (* 2 register lookups *)
    destruct (refine_get_reg_inv _ rreg gp) as [vp [ggp H]].
    destruct vp; try contradiction H. simpl in H. subst.
    destruct (refine_get_reg_inv _ rreg gk) as [vk [ggk H]].
    destruct vk; try contradiction H. simpl in H. subst.
    (* register update *)
    edestruct refine_upd_reg3 as [aregs' [H1 H2]]; [eassumption | | eassumption |].
    instantiate (1:= AbsSeal.VSealed p k). split; reflexivity. (* extra split *)
    eexists. split.
    + eapply AbsSeal.step_seal; [reflexivity | | | | | | reflexivity].
      unfold AbsSeal.decode. rewrite PC. now apply INST.
      eassumption. eassumption. eassumption. eassumption.
    + split4; now trivial.
    }
    + {(* unseal -- very similar to seal *)
    assert (unseal_addr = w) by admit. subst.
    (* break up the effects of the system call *)
    simpl in CALL.
    apply bind_inv in CALL. destruct CALL as [[p tp] [gp CALL]].
    destruct tp; try discriminate CALL.
    apply bind_inv in CALL. destruct CALL as [[? tk] [gk CALL]].
    destruct tk; try discriminate CALL.
    (* additional: equality check between keys *)
    destruct (@equiv_dec (@key sk) (eq_setoid (@key sk)) (@eq_key sk sko) k k0);
      [| discriminate CALL].
    apply bind_inv in CALL. destruct CALL as [sregs' [up CALL]].
    injection CALL; intro H; subst; clear CALL.
    (* 2 register lookups *)
    destruct (refine_get_reg_inv _ rreg gp) as [vp [ggp H]].
    destruct vp; try contradiction H. simpl in H.
      destruct H; subst. (* extra destruct *)
    destruct (refine_get_reg_inv _ rreg gk) as [vk [ggk H]].
    destruct vk; try contradiction H. simpl in H. subst.
    (* register update *)
    edestruct refine_upd_reg3 as [aregs' [H1 H2]]; [eassumption | | eassumption |].
    instantiate (1:= AbsSeal.VData p). reflexivity.
    eexists. split.
    + eapply AbsSeal.step_unseal; [reflexivity | | | | | | reflexivity].
      unfold AbsSeal.decode. rewrite PC. now apply INST.
      eassumption. eassumption.
      rewrite e. eassumption. eassumption.
    + split4; now trivial.
    }
Admitted.

(* Q: Would we get an easier proof if we defined the refinement
   relation as a function from symbolic to abstract, and use
   computation in the direction of forward refinement? *)

End RefinementSA.
