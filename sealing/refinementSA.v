Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.seq.
Require Import CoqUtils.ord CoqUtils.word CoqUtils.partmap.
Require Import lib.utils.
Require Import lib.partmap_utils.
Require Import common.types symbolic.symbolic.
Require Import sealing.classes sealing.symbolic sealing.abstract.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Give up any hope of forward simulation?
   + we could consider a weakened version of forwards simulation
     that only holds up to a failed symbolic key generation
   + see below how that could look like!
*)

Section RefinementSA.

Context {mt : machine_types}
        {ops : machine_ops mt}
        {opss : machine_ops_spec ops}
        {scr : syscall_regs mt}
        {ssa : sealing_syscall_addrs mt}

        {ssk : Sym.sealing_key}
        {ask : Abs.sealing_key}.

(* this is used in the unsealing case; if we were to show fwd
   refinement we would need bijectivity (a permutation on keys) *)
Definition key_map_inj (km : {partmap Abs.key -> Sym.key}) := forall ak ak' sk sk',
  km ak = Some sk ->
  km ak' = Some sk' ->
  sk = sk' ->
  ak = ak'.

Lemma fresh_set_inj : forall (km : {partmap Abs.key -> Sym.key}) akey skey,
  key_map_inj km ->
  (forall ak, ~ km ak = Some skey) ->
  key_map_inj (setm km akey skey).
Proof.
move => km akey skey kmi nk ak ak' sk sk' E1 E2 Esk.
rewrite -{}Esk {sk'} in E2; move: E1 E2; rewrite !getm_set.
have [-> {ak}|Hne] := altP (_ =P _).
  move=> [<-] {sk}.
  have [-> {ak'} //|Hne'] := altP (_ =P _).
  by move/nk.
have [-> {ak'} //|Hne'] := altP (_ =P _).
  by move=> E [E']; rewrite -{}E' {sk} in E; move/nk in E.
by move=> E1 E2; apply: kmi E1 E2 erefl.
Qed.

Section WithFixedKeyMap.

(* km k returns Some sk when k is allocated and sk is the
   corresponding symbolic key *)
Variable km : {partmap Abs.key -> Sym.key}.

Local Notation smemory := {partmap mword mt -> Sym.sym_sealing}.
Local Notation sregisters := {partmap reg mt -> Sym.sym_sealing}.
Local Notation astate := (@Abs.state mt ask).
Local Notation sstate := (@Symbolic.state mt Sym.sym_sealing).

Definition refine_key (ak : Abs.key) (sk : Sym.key) : Prop :=
  getm km ak = Some sk.

Definition refine_val_atom (v : Abs.value mt)
                           (a : atom (mword mt) Sym.stag) : Prop :=
  match v,a with
  | Abs.VData w     , w'@(Sym.DATA)      => w = w'
  | Abs.VKey ak     ,  _@(Sym.KEY sk)    => refine_key ak sk
  | Abs.VSealed w ak, w'@(Sym.SEALED sk) => w = w' /\ refine_key ak sk
  | _                   , _                      => False
  end.

Definition refine_mem : Abs.memory mt -> Sym.memory mt -> Prop :=
  pointwise refine_val_atom.

Definition refine_reg : Abs.registers mt -> Sym.registers mt -> Prop :=
  pointwise refine_val_atom.

(* We make no assumption about the pc tag, since it's unused in the policy *)
Definition refine_pc (w : mword mt) (a : atom (mword mt) unit) : Prop :=
  w = vala a.

(* This is surprisingly weak? The rest would be needed for the fwd direction? *)
Definition refine_ins (akeys : seq Abs.key) (next_skey : Sym.key) : Prop :=
  (forall ak, ak \notin akeys -> km ak = None) /\
  (forall ak sk, km ak = Some sk -> (sk < next_skey)%ord) /\
  (key_map_inj km).

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

Definition refine_upd_reg (aregs : Abs.registers mt) (sregs : Sym.registers mt) :=
  @refine_upd_pointwise _ _ _ refine_val_atom aregs sregs.

Definition refine_upd_mem (amem : Abs.memory mt) (smem : Sym.memory mt) :=
  @refine_upd_pointwise _ _ _ refine_val_atom amem smem.

End WithFixedKeyMap.

Ltac unfold_next_state_in H :=
  try unfold Symbolic.next_state_reg in H;
  try unfold Symbolic.next_state_pc in H;
  try unfold Symbolic.next_state_reg_and_pc in H;
  try unfold Symbolic.next_state in H.

(* We show that refinement relations are closed under key map extension *)
Lemma refine_key_set_km : forall km ak sk akey skey,
  getm km akey = None ->
  refine_key km ak sk ->
  refine_key (setm km akey skey) ak sk.
Proof.
  unfold refine_key. intros. rewrite getm_set.
  by have [eq_ak | /eqP neq_ak] := altP (ak =P akey); congruence.
Qed.

Lemma refine_val_atom_set_km : forall km v a akey skey,
  getm km akey = None ->
  refine_val_atom km v a ->
  refine_val_atom (setm km akey skey) v a.
Proof.
  move => km v [w tg] akey skey anew rva.
  destruct v; destruct tg; simpl in * => //=;
    intuition; eauto using refine_key_set_km.
Qed.

(* Instantiation of refine_extend_map not so simple *)
Lemma refine_reg_set_km : forall km aregs sregs akey skey,
  getm km akey = None ->
  refine_reg km aregs sregs ->
  refine_reg (setm km akey skey) aregs sregs.
Proof.
  intros. eapply refine_extend_map with
            (f := fun km k1 k2 => getm km k1 = None) => //.
  intros. by apply refine_val_atom_set_km.
Qed.

Lemma refine_mem_set_km : forall km amem smem akey skey,
  getm km akey = None ->
  refine_mem km amem smem ->
  refine_mem (setm km akey skey) amem smem.
Proof.
  intros. eapply refine_extend_map with
            (f := fun km k1 k2 => getm km k1 = None) => //.
  intros. by apply refine_val_atom_set_km.
Qed.


Lemma backward_simulation : forall km ast sst sst',
  refine_state km ast sst ->
  Sym.step sst sst' ->
  exists ast' km',
    Abs.step ast ast' /\
    refine_state km' ast' sst'.
Proof.
  Ltac REFINE_INSTR PC ti rmem rpc NEXT :=
    (apply refine_pc_inv in rpc; (* symmetry in rpc; *) subst;
    apply (refine_get_pointwise_inv rmem) in PC;
      destruct PC as [iv [PC riv]];
    destruct ti; unfold_next_state_in NEXT; simpl in NEXT; try discriminate NEXT;
    try apply refine_val_data in riv; subst).
  Ltac destruct_pc := repeat
    match goal with
    | [pc: Equality.sort (Symbolic.tag_type Symbolic.ttypes Symbolic.P) |- _] => destruct pc
    end.
  intros km [amem aregs apc akeys] sst sst' ref sstep. move: ref.
  destruct sstep; destruct sst as [smem sregs spc skey];
    injection ST; do 4 (intro H; symmetry in H; subst); clear ST;
    intros [rmem [rreg [rpc rins]]]; destruct_pc.
  - (* NOP *)
    REFINE_INSTR PC ti rmem rpc NEXT.

    injection NEXT; intro H; subst; clear NEXT.
    eexists. exists km. split.
    + eapply Abs.step_nop; [reflexivity | | reflexivity].
      unfold Abs.decode. rewrite PC. now apply INST.
    + split4; now trivial.
  - (* CONST *)
    REFINE_INSTR PC ti rmem rpc NEXT.
    apply obind_inv in NEXT. destruct NEXT as [sregs' [upd NEXT]].
    injection NEXT; intro H; subst; clear NEXT.
    edestruct refine_upd_reg as [aregs' [H1 H2]]; [eassumption | | eassumption |].
    instantiate (1:= Abs.VData (swcast n)). reflexivity.
    eexists. exists km. split.
    + eapply Abs.step_const; [reflexivity | | | reflexivity]. (* extra goal *)
      unfold Abs.decode. rewrite PC. now apply INST.
      eassumption.
    + split4; now trivial.
  - (* MOV *)
    REFINE_INSTR PC ti rmem rpc NEXT.
    apply obind_inv in NEXT. destruct NEXT as [sregs' [upd NEXT]].
    injection NEXT; intro H; subst; clear NEXT.
    destruct (refine_get_pointwise_inv rreg R1W) as [v [g rva]].
    edestruct refine_upd_reg as [aregs' [H1 H2]]; [eassumption | | eassumption |].
    eauto.
    eexists. exists km. split.
    + eapply Abs.step_mov; [reflexivity | | | | reflexivity]. (* two extra goals *)
      unfold Abs.decode. rewrite PC. now apply INST.
      eassumption.
      eassumption.
    + split4; now trivial.
  - (* BINOP *)
    REFINE_INSTR PC ti rmem rpc NEXT.
    apply obind_inv in NEXT. destruct NEXT as [st [stag NEXT]].
    apply obind_inv in NEXT; destruct NEXT as [sregs' [upd NEXT]].
    injection NEXT; intro H; subst; clear NEXT.
    destruct t1; destruct t2; try discriminate stag.
       injection stag; intro H; subst; clear stag. simpl in *.
    destruct (refine_get_pointwise_inv rreg R1W) as [v1 [g1 rva1]].
    apply refine_val_data in rva1; subst.
    destruct (refine_get_pointwise_inv rreg R2W) as [v2 [g2 rva2]].
    apply refine_val_data in rva2; subst.
    edestruct refine_upd_reg as [aregs' [H1 H2]]; [eassumption | | eassumption|].
    instantiate (1:= Abs.VData (binop_denote op w1 w2)); reflexivity.
    eexists. exists km. split.
    + eapply Abs.step_binop; [reflexivity | | | | | reflexivity].
      unfold Abs.decode. rewrite PC. now apply INST.
      eassumption.
      eassumption.
      eassumption.
    + split4; now trivial.
  - (* LOAD *)
    REFINE_INSTR PC ti rmem rpc NEXT.
    apply obind_inv in NEXT. destruct NEXT as [st [stag NEXT]].
    apply obind_inv in NEXT. destruct NEXT as [sregs' [upd NEXT]].
    injection NEXT; intro H; subst; clear NEXT.
    destruct t1; try discriminate stag.
       injection stag; intro H; subst; clear stag; simpl in *.
    destruct (refine_get_pointwise_inv rreg R1W) as [v [g rva]].
    apply refine_val_data in rva; subst.
    destruct (refine_get_pointwise_inv rmem MEM1) as [vm [gm rvam]].
    edestruct refine_upd_reg as [args' [H1 H2]]; [eassumption | | eassumption|].
    eassumption.
    eexists. exists km. split.
    + eapply Abs.step_load; [reflexivity | | | | | reflexivity].
      unfold Abs.decode. rewrite PC. now apply INST.
      eassumption.
      eassumption.
      eassumption.
    + split4; now trivial.
  - (* STORE *)
    REFINE_INSTR PC ti rmem rpc NEXT.
    apply obind_inv in NEXT. destruct NEXT as [st [stag NEXT]].
    apply obind_inv in NEXT. destruct NEXT as [smem' [upd NEXT]].
    injection NEXT; intro H; subst; clear NEXT.
    destruct t1; try discriminate stag.
       injection stag; intro H; subst; clear stag; simpl in *.
    destruct (refine_get_pointwise_inv rreg R1W) as [v1 [g1 rva1]].
    apply refine_val_data in rva1; subst.
    destruct (refine_get_pointwise_inv rreg R2W) as [v2 [g2 rva2]].
    edestruct refine_upd_mem as [amem' [? ?]]; [eassumption | | eassumption|].
    eassumption.
    eexists. exists km. split.
    + eapply Abs.step_store; [reflexivity | | | | | reflexivity].
      unfold Abs.decode. rewrite PC. now apply INST.
      eassumption.
      eassumption.
      eassumption.
    + split4; now trivial.
  - (* JUMP *)
    REFINE_INSTR PC ti rmem rpc NEXT.
    apply obind_inv in NEXT. destruct NEXT as [st [stag NEXT]].
    injection NEXT; intro H; subst; clear NEXT.
    destruct t1; try discriminate stag.
       injection stag; intro H; subst; clear stag; simpl in *.
    destruct (refine_get_pointwise_inv rreg RW) as [v [g rva]].
    apply refine_val_data in rva; subst; simpl.
    eexists. exists km. split.
    + eapply Abs.step_jump; [reflexivity | | | reflexivity].
      unfold Abs.decode. rewrite PC. now apply INST.
      eassumption.
    + split4; now trivial.
  - (* BNZ *)
    REFINE_INSTR PC ti rmem rpc NEXT.
    apply obind_inv in NEXT. destruct NEXT as [st [stag NEXT]].
    injection NEXT; intro H; subst; clear NEXT.
    destruct t1; try discriminate stag.
       injection stag; intro H; subst; clear stag; simpl in *.
    destruct (refine_get_pointwise_inv rreg RW) as [v [g rva]].
    apply refine_val_data in rva; subst; simpl.
    eexists. exists km. split.
    + eapply Abs.step_bnz; [reflexivity | | | reflexivity].
      unfold Abs.decode. rewrite PC. now apply INST.
      eassumption.
    + split4; now trivial.
  - (* JAL - not system call *)
    (* copy paste (all cases) *)
    REFINE_INSTR PC ti rmem rpc NEXT.
    apply obind_inv in NEXT. destruct NEXT as [st [stag NEXT]].
    apply obind_inv in NEXT. destruct NEXT as [sregs' [upd' NEXT]].
    injection NEXT; intro H; subst; clear NEXT.
    (* new *)
    destruct t1; try discriminate stag. injection stag; intro; subst; clear stag.
    (* new - reading a register *)
    destruct (refine_get_pointwise_inv rreg RW) as [v [g rva]].
    apply refine_val_data in rva; subst; simpl.
    (* the rest similar to CONST *)
    edestruct refine_upd_reg as [aregs' [H1 H2]]; [eassumption | | eassumption |].
    instantiate (1:= Abs.VData (pc + 1)%w). reflexivity.
    eexists. exists km. split.
    + eapply Abs.step_jal; [reflexivity | | | eassumption | reflexivity].
      unfold Abs.decode. rewrite PC. now apply INST.
      eassumption.
    + split4; now trivial.
  - (* system call *)
    (* copy paste (all cases) -- using ALLOWED instead of NEXT *)
    apply refine_pc_inv in rpc; symmetry in rpc; subst.
    erewrite (@pointwise_none _ _ _ _ amem smem apc rmem) in PC.
    simpl in GETCALL.
    rewrite getm_mkpartmap /= !(eq_sym apc) in GETCALL. move : GETCALL.
      have [eq_mkkey | neq_mkkey] := altP (mkkey_addr =P apc); [|
      have [eq_seal | neq_seal] := altP (seal_addr =P apc); [|
      have [eq_unseal | //] := altP (unseal_addr =P apc)]];
      move => GETCALL; injection GETCALL; move {GETCALL} => ?; subst.
    + {(* mkkey *)
    apply obind_inv in CALL. destruct CALL as [_ [_ CALL]].
    simpl in CALL; move: CALL.
    case lt_skey : (skey < Sym.max_key)%ord => // CALL.
    apply obind_inv in CALL. destruct CALL as [sreg' [upd CALL]].
    apply obind_inv in CALL. destruct CALL as [ret [GET CALL]].
    destruct ret as [ret [| |]]; try done.
    injection CALL; intro H; subst; clear CALL.
    apply (refine_get_pointwise_inv rreg) in GET.
    move: GET => [v1 [GET REF]].
    apply refine_val_data in REF. subst v1.

    assert(refine_val_atom (setm km (Abs.mkkey_f akeys) skey)
              (Abs.VKey mt (Abs.mkkey_f akeys))
              (0%w@(Sym.KEY skey))) as rva.
      unfold refine_val_atom, refine_key. by rewrite getm_set eqxx.

    (* need to show freshness for new abstract key to be able to use
       refine...set lemmas to port refinements to the extended km *)
    assert (getm km (Abs.mkkey_f akeys) = None).
    - pose proof Abs.mkkey_fresh.
      destruct rins as [rins1 _]. by apply rins1.

    (* dealing with the result -- similar to CONST *)
    edestruct refine_upd_reg as [aregs' [G1 G2]]; [| exact rva | eassumption |].
    apply refine_reg_set_km; eassumption.

    eexists. exists (setm km (Abs.mkkey_f akeys) skey). split.
    + eapply Abs.step_mkkey; [reflexivity | | |eassumption | reflexivity].
      unfold Abs.decode. now rewrite PC.
      eassumption.
    + split4; trivial; try reflexivity.
        by eauto using refine_mem_set_km.
      split3. (* the interesting part: reestablish refinement on keys *)
      - (* abstract keys *)
        intros ak ninak.
        have [eq_ak | /eqP neq_ak] := altP (ak =P (Abs.mkkey_f akeys)).
        + subst. apply False_ind. by rewrite inE eqxx in ninak.
        + simpl in ninak.
          rewrite getm_set (introF eqP neq_ak).
          destruct rins as [rins1 _]. apply rins1. by case/norP: ninak.
      - (* symbolic keys *)
        move => ak sk /=.
        have [eq_ak | /eqP neq_ak] := altP (ak =P (Abs.mkkey_f akeys)) => hsk.
        + subst. rewrite getm_set eqxx in hsk => //.
          injection hsk => hsk'. clear hsk.
          rewrite hsk'.
          by rewrite Sym.ltb_inc -?hsk' ?lt_skey //.
        + rewrite getm_set (introF eqP neq_ak) in hsk => //.
          destruct rins as [_ [rins2 _]]. eapply Ord.lt_trans. eapply rins2.
          eassumption.
          by rewrite /= Sym.ltb_inc ?lt_skey.
      - (* injectivity *)
        apply fresh_set_inj. by destruct rins as [_ [_ rins3]].
        destruct rins as [_ [rins2 _]].
        intros ? Hc. apply rins2 in Hc. by rewrite Ord.ltxx in Hc.
    }
    + {(* seal *)
    (* break up the effects of the system call *)
    apply obind_inv in CALL. destruct CALL as [_ [_ CALL]].
    simpl in CALL.
    apply obind_inv in CALL. destruct CALL as [[p tp] [gp CALL]].
    destruct tp; try discriminate CALL.
    apply obind_inv in CALL. destruct CALL as [[? tk] [gk CALL]].
    destruct tk; try discriminate CALL.
    apply obind_inv in CALL. destruct CALL as [sregs' [up CALL]].
    apply obind_inv in CALL.
    destruct CALL as [[ret [| |]] [GET CALL]]; try discriminate CALL.
    injection CALL; intro H; subst; clear CALL.
    apply (refine_get_pointwise_inv rreg) in GET.
    move: GET => [v1 [GET REF]].
    apply refine_val_data in REF. subst v1.

    (* 2 register lookups *)
    destruct (refine_get_pointwise_inv rreg gp) as [vp [ggp H]].
    destruct vp; try contradiction H. simpl in H. subst.
    destruct (refine_get_pointwise_inv rreg gk) as [vk [ggk H]].
    destruct vk; try contradiction H. simpl in H.
    (* register update *)
    edestruct refine_upd_reg as [aregs' [H1 H2]]; [eassumption | | eassumption |].
    instantiate (1:= Abs.VSealed p s0). split; now trivial. (* extra split *)
    eexists. exists km. split.
    + eapply Abs.step_seal; try eassumption; [reflexivity | | reflexivity].
      * unfold Abs.decode. rewrite PC. reflexivity.
    + split4; now trivial.
    }
    + {(* unseal -- very similar to seal *)
    (* break up the effects of the system call *)
    apply obind_inv in CALL. destruct CALL as [_ [_ CALL]].
    simpl in CALL.
    apply obind_inv in CALL. destruct CALL as [[p tp] [gp CALL]].
    destruct tp; try discriminate CALL.
    apply obind_inv in CALL. destruct CALL as [[? tk] [gk CALL]].
    destruct tk; try discriminate CALL.
    move: CALL.
    (* additional: equality check between keys *)
    have [eq_s CALL|//] := eqP.
    apply obind_inv in CALL. destruct CALL as [sregs' [up CALL]].
    apply obind_inv in CALL.
    destruct CALL as [[ret [| |]] [GET CALL]]; try discriminate CALL.
    injection CALL; intro H; subst; clear CALL.
    apply (refine_get_pointwise_inv rreg) in GET.
    move: GET => [v1 [GET REF]].
    apply refine_val_data in REF. subst v1.
    (* 2 register lookups *)
    destruct (refine_get_pointwise_inv rreg gp) as [vp [ggp H]].
    destruct vp; try contradiction H. simpl in H.
      destruct H; subst. (* extra destruct *)
    destruct (refine_get_pointwise_inv rreg gk) as [vk [ggk H]].
    destruct vk; try contradiction H. simpl in H. subst.
    (* register update *)
    edestruct refine_upd_reg as [aregs' [H1 H2]]; [eassumption | | eassumption |].
    instantiate (1:= Abs.VData p). reflexivity.
    eexists. exists km. split.
    + eapply Abs.step_unseal; try eassumption; [reflexivity | | | reflexivity].
      * unfold Abs.decode. rewrite PC. reflexivity.
      (* here we use injectivity *)
      destruct rins as [_ [_ rins3]].
      repeat match goal with
               | [H : refine_key _ _ _ |- _] =>
                 unfold refine_key in H; try rewrite e in H
             end.
      assert(s = s1) by eauto. (* NAMING! *) subst. assumption.

    + split4; now trivial.
    }
Qed.

(* Q: Would we get an easier proof if we defined the refinement
   relation as a function from symbolic to abstract, and use
   computation in the direction of forward refinement? *)

(* Here is a weaker form of forward simulation we can hope to prove.
   It intuitively says that we have forwards simulation for programs
   that don't run out of keys at the symbolic level. *)
Definition forward_simulation := forall km ast ast' sst,
  refine_state km ast sst ->
  Abs.step ast ast' ->
  (* each abstract step can be simulated by a corresponding symbolic one *)
  (exists sst' km',
    Sym.step sst sst' /\
    refine_state km' ast' sst')
  \/
  (* ... or the symbolic machine gets stuck on a failed key generation *)
  ((forall sst', ~Sym.step sst sst')
   /\
   (exists (i : mword mt) (r : reg mt) (ti t1 : Sym.stag) (sc : Symbolic.syscall mt),
      (getm (Symbolic.mem sst) (vala (Symbolic.pc sst)) = Some i@ti) /\
      (decode_instr i = Some (Jal r)) /\
      (getm (Symbolic.regs sst) r = Some mkkey_addr@t1) /\
      (Sym.sealing_syscalls mkkey_addr = Some sc) /\
      (Symbolic.sem sc sst = None))
  ).

End RefinementSA.
