Require Import List. Import ListNotations.
Require Import Coq.Classes.SetoidDec.
Require Import ssreflect ssrfun ssrbool eqtype.
Require Import lib.utils lib.ordered common.common. Import PartMaps.
Require Import symbolic.symbolic.
Require Import sealing.classes sealing.symbolic sealing.abstract.

(* Give up any hope of forwards refinement?
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

(* CH: It's silly to have kiIr as a field in this sigma-type-like
   dependent record type: it forces upd_ki to be too dependently
   typed, all I need is a "regular" partial map, the proofs should go
   in the refinement (e.g. could be another conjunct in refine_ins) *)
Record key_inj := mkKeyInj {
  (* ki k returns Some sk when k is allocated and sk is the
                               corresponding symbolic key *)
  ki :> Abs.key -> option Sym.key;

  (* injectivity; this is used in the unsealing case;
     if we were to show fwd refinement we would probably need
     bijectivity (a permutation on keys) *)
  kiIr : forall ak ak' sk sk',
           ki ak = Some sk ->
           ki ak' = Some sk' ->
           sk = sk' ->
           ak = ak'
}.

Definition upd_ki (ki : key_inj) (akey : Abs.key) (skey : Sym.key)
  (H : forall ak, ~ki ak = Some skey) : key_inj.
  refine (mkKeyInj (fun ak => if ak == akey then Some skey else ki ak) _).
  intros ak ak' sk sk'.
  case: eqP => [Heq | Hneq]; case: eqP => [Heq' | Hneq']; try congruence.
  now apply (kiIr ki).
Defined.

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

(* This is surprisingly weak? The rest would be needed for the fwd direction? *)
Definition refine_ins (akeys : list Abs.key) (next_skey : Sym.key) : Prop :=
  (forall ak, ~In ak akeys -> ki ak = None) /\
  (forall ak sk, ki ak = Some sk -> (sk <? next_skey)%ordered).

Definition astate := @Abs.state t ask amemory aregisters.
Definition sstate := @Symbolic.state t Sym.sym_sealing.

Definition refine_state (ast : astate) (sst : sstate) : Prop :=
  let '(Abs.State amem areg apc akeys) := ast in
  let '(Symbolic.State smem sreg spc skey) := sst in
  refine_mem amem smem /\
  refine_reg areg sreg /\
  refine_pc apc spc /\
  refine_ins akeys skey.

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
  intro r'. have [<-|/eqP neq_rr'] := altP (r =P r').
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

Lemma refine_key_upd_ki : forall (ki : key_inj) ak sk akey skey
  (new : forall ak, ~ki ak = Some skey),
  (ki akey = None) ->
  refine_key ki ak sk ->
  refine_key (@upd_ki ki akey skey new) ak sk.
Proof.
  unfold refine_key. intros. simpl.
  case eqP => [heq | hneq]; [congruence | exact].
Qed.

Lemma refine_val_atom_upd_ki : forall (ki : key_inj) v a akey skey
  (new : forall ak, ~ki ak = Some skey),
  (ki akey = None) ->
  refine_val_atom ki v a ->
  refine_val_atom (@upd_ki ki akey skey new) v a.
Proof.
  move => ki v [w tg] akey skey snew anew rva.
  destruct v; destruct tg; simpl in * => //=;
    intuition; eauto using refine_key_upd_ki.
Qed.

Lemma refine_reg_upd_ki : forall (ki : key_inj) aregs sregs akey skey
  (new : forall ak, ~ki ak = Some skey),
  (ki akey = None) ->
  refine_reg ki aregs sregs ->
  refine_reg (@upd_ki ki akey skey new) aregs sregs.
Proof.
  unfold refine_reg.
  move => ki areg sreg akey skey snew anew rreg w. specialize (rreg w).
  destruct (get areg w); destruct (get sreg w) => //.
  by auto using refine_val_atom_upd_ki.
Qed.

Lemma refine_mem_upd_ki : forall (ki : key_inj) amem smem akey skey
  (new : forall ak, ~ki ak = Some skey),
  (ki akey = None) ->
  refine_mem ki amem smem ->
  refine_mem (@upd_ki ki akey skey new) amem smem.
Admitted. (* same as above *)

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
    intros [rmem [rreg [rpc rins]]].
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
        destruct (mkkey_addr == w). discriminate NOTCALL.
        destruct (seal_addr == w). discriminate NOTCALL.
        destruct (unseal_addr == w). discriminate NOTCALL.
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
    destruct (mkkey_addr == w);
      [| destruct (seal_addr == w);
      [| destruct (unseal_addr == w); [| discriminate GETCALL]]];
      injection GETCALL; intro; subst; clear GETCALL.
    + {(* mkkey *)
    assert (mkkey_addr = w) by admit. subst.
    simpl in CALL; move: CALL.
    have [//|/eqP neq_skey CALL] := altP (skey =P Sym.max_key).
    apply bind_inv in CALL. destruct CALL as [sreg' [upd CALL]].
    injection CALL; intro H; subst; clear CALL.
    
    (* need to show freshness for the new symbolic key to preserve injectivity *)
    assert (forall ak : Abs.key, ki ak <> Some skey) as new.
    - destruct rins as [_ rins2].
      intros ? Hc. apply rins2 in Hc. rewrite ltb_irrefl in Hc.
      discriminate Hc.

    pose (@upd_ki ki (Abs.mkkey_f akeys) skey new) as ki'.
    assert (refine_key ki' (Abs.mkkey_f akeys) skey) as rk.
      unfold refine_key. simpl. case eqP; congruence.

    assert(refine_val_atom ki' (Abs.VKey t (Abs.mkkey_f akeys))
              (max_word@(Sym.KEY skey))) as rva by apply rk.

    (* need to show freshness for new abstract key to be able to use
       refine...upd_ki lemmas to port refinements to the extended ki *)
    assert (ki (Abs.mkkey_f akeys) = None).
    - pose proof Abs.mkkey_fresh.
      destruct rins as [rins1 _]. by apply rins1.

    (* dealing with the result -- similar to CONST *)
    edestruct refine_upd_reg3 as [aregs' [G1 G2]]; [| exact rva | eassumption |].
    apply refine_reg_upd_ki; eassumption.

    eexists. exists ki'. split.
    + eapply Abs.step_mkkey; [reflexivity | | | | reflexivity].
      unfold Abs.decode. rewrite PC. now apply INST.
      assumption.
      eassumption.
    + split4; trivial; try reflexivity.
        by eauto using refine_mem_upd_ki.
      split. (* the interesting part: reestablish refinement on keys *)
      - (* abstract keys *)
        intros ak ninak. simpl. case eqP => [heq | hneq].
        + subst. apply False_ind. apply ninak. simpl. tauto.
        + simpl in ninak.
          destruct rins as [rins1 _]. apply rins1.
          intro Hc. apply ninak. right. exact Hc.
      - (* symbolic keys *)
        move => ak sk /=. case eqP => [heq | hneq] hsk.
        + injection hsk => hsk'. clear hsk.
          rewrite hsk'.
          admit.
          (* rewrite hsk' in c. by eauto using Sym.ltb_inc. *)
        + destruct rins as [rins1 rins2]. eapply ltb_trans. eapply rins2.
          eassumption. admit. (* apply Sym.ltb_inc; assumption. *)
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
    instantiate (1:= Abs.VSealed p s0). split; now trivial. (* extra split *)
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
    move: CALL.
    (* additional: equality check between keys *)
    have [eq_s CALL|//] := eqP.
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
      assert(s = s1) by eauto using kiIr. subst. assumption.
      eassumption.
    + split4; now trivial.
    }
Admitted.

(* Q: Would we get an easier proof if we defined the refinement
   relation as a function from symbolic to abstract, and use
   computation in the direction of forward refinement? *)

End RefinementSA.
