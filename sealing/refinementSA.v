Require Import List. Import ListNotations.
Require Import Coq.Classes.SetoidDec.
Require Import utils common. Import PartMaps.
Require Import symbolic.symbolic.
Require Import sealing.classes sealing.symbolic sealing.abstract.

(* At the moment we're considering (morally) the same key generation
   partial function at both levels and the identity mapping on keys.
   TODO: We plan to get rid of this assumption by:
   - [DONE] changing the abstract machine to have an infinite set of keys
     that is different to the finite set of keys of the finite one
   - [DONE] make key generation total at the abstract level
   - [STARTED] for backwards refinement use someting similar to Maxime's
     memory injections to relate symbolic and abstract keys
   - give up any hope of forwards refinement?
     + we could consider a weakened version of forwards refinement
       that only holds up to a failed symbolic key generation
*)

Section RefinementSA.

Set Implicit Arguments.

Context {t : machine_types}
        {ops : machine_ops t}
        {opss : machine_ops_spec ops}
        {scr : @syscall_regs t}
        {ssa : @sealing_syscall_addrs t}

        {ssk : Sym.sealing_key}
        {ask : Abs.sealing_key}

        {smemory : Type}
        {sm : partial_map smemory (word t) (atom (word t) Sym.stag)}
        {smemspec : axioms sm}

        {sregisters : Type}
        {sr : partial_map sregisters (reg t) (atom (word t) Sym.stag)}
        {sregspec : axioms sr}

        {amemory : Type}
        {am : partial_map amemory (word t) (Abs.value t)}
        {amemspec : axioms am}

        {aregisters : Type}
        {ar : partial_map aregisters (reg t) (Abs.value t)}
        {aregspec : axioms ar}.

Section WithFixedKeyInjection.

Record key_inj := mkKeyInj {
  (* ki k returns Some sk when k is allocated and sk is the
                               corresponding symbolic key *)
  ki :> Abs.key -> option Sym.key;

  (* still unclear where this is used *)    
  kiIr : forall ak ak' sk sk',
           ki ak = Some sk ->
           ki ak' = Some sk' ->
           sk = sk' ->
           ak = ak'
}.

Variable ki : key_inj.

Definition refine_key (ak : Abs.key) (sk : Sym.key) : Prop :=
  ki ak = Some sk.

Definition refine_val_atom (v : Abs.value t)
                           (a : atom (word t) Sym.stag) : Prop :=
  match v,a with
  | Abs.VData w     , w'@(Sym.DATA)      => w = w'
  | Abs.VKey ak     ,  _@(Sym.KEY sk)    => refine_key ak sk
  | Abs.VSealed w ak, w'@(Sym.SEALED sk) => w = w' /\ refine_key ak sk
  | _                   , _                      => False
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
Definition refine_pc (w : word t) (a : atom (word t) Sym.stag) : Prop :=
  w = val a.

(* XXX: Old, unclear whether we will still need anything like this

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

Lemma mkkey_fresh : forall ks ks' k,
  mkkey_f ks = Some (ks', k) ->
  ~ In k ks /\ In k ks' /\ incl ks ks'.
Proof.
  intros ks ks' k H. unfold mkkey_f in *. unfold bind in H.
  remember (inc_key_opt (kmax ks)) as o. destruct o as [k'|].
  - inversion H. subst. split; [|split].
    + unfold inc_key_opt in *.
      destruct (equiv_dec (kmax ks) max_key). congruence.
      inversion Heqo. eauto using inc_max_not_in.
    + left; reflexivity.
    + right; assumption.
  - inversion H.
Qed.

(* Need to define this instance to use Abs.step *)
Program Instance gen_key_inst : Abs.key_generator := {
  mkkey_f := mkkey_f;
  mkkey_fresh := mkkey_fresh
}.

Definition refine_ins (keys : list key) (next_key : key) : Prop :=
  match mkkey_f keys with
  | Some (_, k) => k = next_key
  | _           => False (* ??? *)
  end.

*)

Definition astate := @Abs.state t ask amemory aregisters.
Definition sstate := @Symbolic.state t Sym.sym_sealing.

Definition refine_state (ast : astate) (sst : sstate) : Prop :=
  let '(Abs.State amem areg apc akeys) := ast in
  let '(Symbolic.State smem sreg spc skey) := sst in
  refine_mem amem smem /\
  refine_reg areg sreg /\
  refine_pc apc spc.
(* /\ refine_ins akeys skey -- just gone? *)

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
  refine_val_atom v w@Sym.DATA ->
  v = Abs.VData w.
Proof.
  intros v w ref. destruct v; simpl in ref; try tauto; subst; reflexivity.
Qed.

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

End WithFixedKeyInjection.

Tactic Notation "unfold_next_state_in" ident(H) :=
  try unfold Symbolic.next_state_reg in H;
  try unfold Symbolic.next_state_pc in H;
  try unfold Symbolic.next_state_reg_and_pc in H;
  try unfold Symbolic.next_state in H.

Lemma backward_simulation : forall (ki : key_inj) ast sst sst',
  refine_state ki ast sst ->
  Sym.step sst sst' ->
  exists ast' ki',
    Abs.step ast ast' /\
    refine_state ki' ast' sst'.
Proof.
  intros ki [amem aregs apc akeys] sst sst' ref sstep. gdep ref.
  destruct sstep; destruct sst as [smem sregs spc skey];
    injection ST; do 4 (intro H; symmetry in H; subst); clear ST;
    intros [rmem [rreg rpc]].
  - (* NOP *)
    apply refine_pc_inv in rpc; symmetry in rpc; subst.
    apply (refine_get_mem_inv _ rmem) in PC.
      destruct PC as [iv [PC riv]].
    destruct ti; unfold_next_state_in NEXT; simpl in NEXT; try discriminate NEXT.
    injection NEXT; intro H; subst; clear NEXT.
    apply refine_val_data in riv. subst.
    eexists. exists ki. split.
    + eapply Abs.step_nop; [reflexivity | | reflexivity].
      unfold Abs.decode. rewrite PC. now apply INST.
    + split3; now trivial.
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
    instantiate (1:= Abs.VData (imm_to_word n)). reflexivity.
    eexists. exists ki. split.
    + eapply Abs.step_const; [reflexivity | | | reflexivity]. (* extra goal *)
      unfold Abs.decode. rewrite PC. now apply INST.
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
    instantiate (1:= Abs.VData (apc + 1)%w). reflexivity.
    eexists. exists ki. split.
    + eapply Abs.step_jal; [reflexivity | | | | | reflexivity].
      unfold Abs.decode. rewrite PC. now apply INST.
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
    destruct (@equiv_dec (@Sym.key ssk) (eq_setoid (@Sym.key ssk))
      (@Sym.eq_key ssk) skey (@Sym.max_key ssk)). discriminate CALL.
    apply bind_inv in CALL. destruct CALL as [sreg' [upd CALL]].
    injection CALL; intro H; subst; clear CALL.
admit. (* TODO: Update this proof to the new setting
    assert (exists new_keys, mkkey_f akeys = Some (new_keys, skey)) as H.
      simpl. unfold refine_ins in ris.
      destruct (mkkey_f akeys) as [[x1 x2] | ]. subst. eauto. contradiction.
    destruct H as [new_keys ?].
    (* dealing with the result -- similar to CONST *)
    edestruct refine_upd_reg3 as [aregs' [H1 H2]]; [eassumption | | eassumption |].
    instantiate (1:= (Abs.VKey _ skey)). reflexivity.
    eexists. split.
    + eapply Abs.step_mkkey; [reflexivity | | | | | reflexivity].
      unfold Abs.decode. rewrite PC. now apply INST.
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
*)
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
    destruct vk; try contradiction H. simpl in H.
    (* register update *)
    edestruct refine_upd_reg3 as [aregs' [H1 H2]]; [eassumption | | eassumption |].
    instantiate (1:= Abs.VSealed p k0). split; now trivial. (* extra split *)
    eexists. exists ki. split.
    + eapply Abs.step_seal; [reflexivity | | | | | | reflexivity].
      unfold Abs.decode. rewrite PC. now apply INST.
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
    destruct (@equiv_dec (@Sym.key ssk) (eq_setoid (@Sym.key ssk))
               (@Sym.eq_key ssk) k k0); [| discriminate CALL].
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
    instantiate (1:= Abs.VData p). reflexivity.
    eexists. exists ki. split.
    + eapply Abs.step_unseal; [reflexivity | | | | | | reflexivity].
      unfold Abs.decode. rewrite PC. now apply INST.
      eassumption. eassumption.
      (* here we use injectivity *)
      repeat match goal with
               | [H : refine_key _ _ _ |- _] =>
                 unfold refine_key in H; try rewrite e in H
             end.
      assert(k1 = k2) by eauto using kiIr. subst. assumption.
      eassumption.
    + split4; now trivial.
    }
Admitted.

(* Q: Would we get an easier proof if we defined the refinement
   relation as a function from symbolic to abstract, and use
   computation in the direction of forward refinement? *)

End RefinementSA.
