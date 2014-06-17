Require Import List. Import ListNotations.
Require Import Coq.Classes.SetoidDec.
Require Import ssreflect ssrfun ssrbool eqtype.
Require Import lib.utils lib.ordered lib.partial_maps. Import PartMaps.
Require Import common.common symbolic.symbolic.
Require Import sealing.classes sealing.symbolic sealing.abstract.

(* Give up any hope of forwards refinement?
     + we could consider a weakened version of forwards refinement
       that only holds up to a failed symbolic key generation
*)

Section RefinementSA.

Set Implicit Arguments.
(*
Unset Strict Implicit.
Unset Printing Implicit Defensive.
*)

Context {t : machine_types}
        {ops : machine_ops t}
        {opss : machine_ops_spec ops}
        {scr : @syscall_regs t}
        {ssa : @sealing_syscall_addrs t}

        {ssk : Sym.sealing_key}
        {ask : Abs.sealing_key}

        (* TODO: play the same trick as for ap/ps below? *)
        {smemory : Type}
        {sm : partial_map smemory (word t) (atom (word t) Sym.stag)}
        {smemspec : axioms sm}

        {sregisters : Type}
        {sr : partial_map sregisters (reg t) (atom (word t) Sym.stag)}
        {sregspec : axioms sr}

        {ap : Abs.abstract_params t}
        {aps : Abs.params_spec ap}.

(* ki k returns Some sk when k is allocated and sk is the
   corresponding symbolic key *)
Definition key_map := Abs.key -> option Sym.key.

(* this is used in the unsealing case; if we were to show fwd
   refinement we would need bijectivity (a permutation on keys) *)
Definition key_map_inj (ki : key_map) := forall ak ak' sk sk',
  ki ak = Some sk ->
  ki ak' = Some sk' ->
  sk = sk' ->
  ak = ak'.

Definition upd_ki (ki : key_map) (akey : Abs.key) (skey : Sym.key) :=
  fun ak => if ak == akey then Some skey else ki ak.

Lemma fresh_up_inj : forall (ki : key_map) akey skey,
  key_map_inj ki ->
  (forall ak, ~ki ak = Some skey) ->
  key_map_inj (upd_ki ki akey skey).
Proof.
  move => ki akey skey kmi nkiamsk ak ak' sk sk'. unfold upd_ki.
  case: eqP => [Heq | Hneq]; case: eqP => [Heq' | Hneq']; try congruence.
  now apply kmi.
Qed.

Section WithFixedKeyMap.

Variable ki : key_map.

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

Definition refine_mem : Abs.memory t -> smemory -> Prop :=
  pointwise refine_val_atom.

Definition refine_reg : Abs.registers t -> sregisters -> Prop :=
  pointwise refine_val_atom.

(* We make no assumption about the pc tag, since it's unused in the policy *)
Definition refine_pc (w : word t) (a : atom (word t) Sym.stag) : Prop :=
  w = val a.

(* This is surprisingly weak? The rest would be needed for the fwd direction? *)
Definition refine_ins (akeys : list Abs.key) (next_skey : Sym.key) : Prop :=
  (forall ak, ~In ak akeys -> ki ak = None) /\
  (forall ak sk, ki ak = Some sk -> (sk <? next_skey)%ordered) /\
  (key_map_inj ki).

Definition astate := @Abs.state t ask ap.
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

Lemma refine_val_data : forall v w,
  refine_val_atom v w@Sym.DATA ->
  v = Abs.VData w.
Proof.
  intros v w ref. destruct v; simpl in ref; try tauto; subst; reflexivity.
Qed.

(* helping the type class resolution a bit seems needed *)
Definition refine_upd_reg3 (aregs : Abs.registers t) (sregs : sregisters) :=
  @refine_upd_pointwise3 _ _ _ _ _ _ _ _ _ refine_val_atom aregs sregs.

End WithFixedKeyMap.

Tactic Notation "unfold_next_state_in" ident(H) :=
  try unfold Symbolic.next_state_reg in H;
  try unfold Symbolic.next_state_pc in H;
  try unfold Symbolic.next_state_reg_and_pc in H;
  try unfold Symbolic.next_state in H.

Lemma refine_key_upd_ki : forall ki ak sk akey skey,
  ki akey = None ->
  refine_key ki ak sk ->
  refine_key (upd_ki ki akey skey) ak sk.
Proof.
  unfold refine_key, upd_ki. intros.
  case eqP; [congruence | exact].
Qed.

Lemma refine_val_atom_upd_ki : forall ki v a akey skey,
  ki akey = None ->
  refine_val_atom ki v a ->
  refine_val_atom (upd_ki ki akey skey) v a.
Proof.
  move => ki v [w tg] akey skey anew rva.
  destruct v; destruct tg; simpl in * => //=;
    intuition; eauto using refine_key_upd_ki.
Qed.

Lemma refine_reg_upd_ki : forall ki aregs sregs akey skey,
  ki akey = None ->
  refine_reg ki aregs sregs ->
  refine_reg (upd_ki ki akey skey) aregs sregs.
Proof.
  unfold refine_reg.
  move => ki areg sreg akey skey anew rreg w. specialize (rreg w).
  destruct (get areg w); destruct (get sreg w) => //.
  by auto using refine_val_atom_upd_ki.
Qed.

Lemma refine_mem_upd_ki : forall ki amem smem akey skey,
  (ki akey = None) ->
  refine_mem ki amem smem ->
  refine_mem (upd_ki ki akey skey) amem smem.
Admitted. (* same as above *)

Lemma backward_simulation : forall ki ast sst sst',
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
    apply (refine_get_pointwise_inv rmem) in PC.
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
    apply (refine_get_pointwise_inv rmem) in PC.
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
    apply (refine_get_pointwise_inv rmem) in PC.
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
    destruct (refine_get_pointwise_inv rreg RW) as [v [g rva]].
    destruct v; try contradiction rva. simpl in rva. subst.
    (* the rest similar to CONST *)
    edestruct refine_upd_reg3 as [aregs' [H1 H2]]; [eassumption | | eassumption |].
    instantiate (1:= Abs.VData (apc + 1)%w). reflexivity.
    eexists. exists ki. split.
    + eapply Abs.step_jal; [reflexivity | | | | eassumption | reflexivity].
      unfold Abs.decode. rewrite PC. now apply INST.
      eassumption.
      simpl in NOTCALL. move : NOTCALL.
        have [// | /eqP neq_mkkey] := altP (mkkey_addr =P w).
        have [// | /eqP neq_seal] := altP (seal_addr =P w).
        have [// | /eqP neq_unseal] := altP (unseal_addr =P w).
        by move => _ [? | [? | [? | ?]]].
    + split4; now trivial.
  - (* JAL - system call *)
    (* copy paste (all cases) -- using ALLOWED instead of NEXT *)
    apply refine_pc_inv in rpc; symmetry in rpc; subst.
    apply (refine_get_pointwise_inv rmem) in PC.
      destruct PC as [iv [PC riv]].
    destruct ti; simpl in ALLOWED; try discriminate ALLOWED.
    (* copy paste (all cases) *)
    apply refine_val_data in riv. subst.
    (* new -- useful only for t1, rvec ignored by semantic bug *)
    destruct t1; try discriminate ALLOWED.
    injection ALLOWED; intro H; subst; clear ALLOWED.
    (* same as for normal JAL - reading a register *)
    destruct (refine_get_pointwise_inv rreg RW) as [v [g rva]].
    destruct v; try contradiction rva. simpl in rva. subst.
    (* done with RW *)
    clear RW.
    (* figuring out which system call it was *)
    simpl in GETCALL. move : GETCALL.
      have [eq_mkkey | neq_mkkey] := altP (mkkey_addr =P w); [|
      have [eq_seal | neq_seal] := altP (seal_addr =P w); [|
      have [eq_unseal | //] := altP (unseal_addr =P w)]];
      move => GETCALL; injection GETCALL; move {GETCALL} => ?; subst.
    + {(* mkkey *)
    simpl in CALL; move: CALL.
    have [//|/eqP neq_skey CALL] := altP (skey =P Sym.max_key).
    apply bind_inv in CALL. destruct CALL as [sreg' [upd CALL]].
    injection CALL; intro H; subst; clear CALL.
    
    assert (refine_key (upd_ki ki (Abs.mkkey_f akeys) skey)
                        (Abs.mkkey_f akeys) skey) as rk.
      unfold refine_key. unfold upd_ki. case eqP; congruence.

    assert(refine_val_atom (upd_ki ki (Abs.mkkey_f akeys) skey)
              (Abs.VKey t (Abs.mkkey_f akeys))
              (max_word@(Sym.KEY skey))) as rva by apply rk.

    (* need to show freshness for new abstract key to be able to use
       refine...upd_ki lemmas to port refinements to the extended ki *)
    assert (ki (Abs.mkkey_f akeys) = None).
    - pose proof Abs.mkkey_fresh.
      destruct rins as [rins1 _]. by apply rins1.

    (* dealing with the result -- similar to CONST *)
    edestruct refine_upd_reg3 as [aregs' [G1 G2]]; [| exact rva | eassumption |].
    apply refine_reg_upd_ki; eassumption.

    eexists. exists (upd_ki ki (Abs.mkkey_f akeys) skey). split.
    + eapply Abs.step_mkkey; [reflexivity | | | | reflexivity].
      unfold Abs.decode. rewrite PC. now apply INST.
      assumption.
      eassumption.
    + split4; trivial; try reflexivity.
        by eauto using refine_mem_upd_ki.
      split3. (* the interesting part: reestablish refinement on keys *)
      - (* abstract keys *)
        intros ak ninak. unfold upd_ki. case eqP => [heq | hneq].
        + subst. apply False_ind. apply ninak. simpl. tauto.
        + simpl in ninak.
          destruct rins as [rins1 _]. apply rins1.
          intro Hc. apply ninak. right. exact Hc.
      - (* symbolic keys *)
        move => ak sk /=. unfold upd_ki. case eqP => [heq | hneq] hsk.
        + injection hsk => hsk'. clear hsk.
          rewrite hsk'.
          by rewrite hsk' in neq_skey; apply Sym.ltb_inc; apply /eqP.
        + destruct rins as [_ [rins2 _]]. eapply ltb_trans. eapply rins2.
          eassumption.
          apply Sym.ltb_inc. by apply /eqP.
      - (* injectivity *)
        apply fresh_up_inj. by destruct rins as [_ [_ rins3]].
        destruct rins as [_ [rins2 _]].
        intros ? Hc. apply rins2 in Hc. rewrite ltb_irrefl in Hc.
        discriminate Hc.
    }
    + {(* seal *)
    (* break up the effects of the system call *)
    simpl in CALL.
    apply bind_inv in CALL. destruct CALL as [[p tp] [gp CALL]].
    destruct tp; try discriminate CALL.
    apply bind_inv in CALL. destruct CALL as [[? tk] [gk CALL]].
    destruct tk; try discriminate CALL.
    apply bind_inv in CALL. destruct CALL as [sregs' [up CALL]].
    injection CALL; intro H; subst; clear CALL.
    (* 2 register lookups *)
    destruct (refine_get_pointwise_inv rreg gp) as [vp [ggp H]].
    destruct vp; try contradiction H. simpl in H. subst.
    destruct (refine_get_pointwise_inv rreg gk) as [vk [ggk H]].
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
    destruct (refine_get_pointwise_inv rreg gp) as [vp [ggp H]].
    destruct vp; try contradiction H. simpl in H.
      destruct H; subst. (* extra destruct *)
    destruct (refine_get_pointwise_inv rreg gk) as [vk [ggk H]].
    destruct vk; try contradiction H. simpl in H. subst.
    (* register update *)
    edestruct refine_upd_reg3 as [aregs' [H1 H2]]; [eassumption | | eassumption |].
    instantiate (1:= Abs.VData p). reflexivity.
    eexists. exists ki. split.
    + eapply Abs.step_unseal; [reflexivity | | | | | | reflexivity].
      unfold Abs.decode. rewrite PC. now apply INST.
      eassumption. eassumption.
      (* here we use injectivity *)
      destruct rins as [_ [_ rins3]].
      repeat match goal with
               | [H : refine_key _ _ _ |- _] =>
                 unfold refine_key in H; try rewrite e in H
             end.
      assert(s = s1) by eauto. (* NAMING! *) subst. assumption.
      eassumption.
    + split4; now trivial.
    }
Admitted.

(* Q: Would we get an easier proof if we defined the refinement
   relation as a function from symbolic to abstract, and use
   computation in the direction of forward refinement? *)

End RefinementSA.
