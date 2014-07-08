Require Import Coq.Lists.List.
Require Import lib.utils.
Require Import lib.partial_maps.
Require Import lib.Coqlib.
Require lib.list_utils.
Require Import common.common.
Require Import symbolic.symbolic.
Require Import symbolic.exec.
Require Import concrete.concrete.
Require Import concrete.exec.
Require Import cfi.concrete.
Require Import cfi.symbolic.
Require Import cfi.preservation.
Require Import cfi.rules.
Require Import cfi.refinementAS. (*for Map - should remove when we move it*)
Require Import symbolic.backward.
Require Import symbolic.refinement_common.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Set Implicit Arguments.


Module MapTP.
  Import TotalMaps.
  Import PartMaps.

Section Mappable.
  Variable (M1 M2 : Type -> Type) (K V1 V2 : Type).


  Class mappable (tm1 : total_map M1 K) (pm2 : partial_map M2 K) := {

    map : (V1 -> option V2) -> M1 V1 -> M2 V2;

    map_correctness: forall (f : V1 -> option V2) (m1 : M1 V1) (k : K),
                       PartMaps.get (map f m1) k = f (TotalMaps.get m1 k)


    }.
End Mappable.

End MapTP.

Import PartMaps.

Section Refinement.


Context {mt : machine_types}
        {ops : machine_ops mt}
        {opss : machine_ops_spec ops}

        {e : @rules.encodable (@rules.cfi_tag_eqType mt) mt ops}

        {cr_map : MapTP.mappable (atom (word mt) (word mt)) (atom (word mt) (@cfi_tag mt)) reg_tmap_class reg_map_class}.

Variable valid_jmp : word mt -> word mt -> bool.

Definition sym_params := Sym.sym_cfi valid_jmp.

Variable stable : list (@Symbolic.syscall mt sym_params).

Variable ki : (@refinement_common.kernel_invariant mt ops sym_params e).

Definition masks := symbolic.rules.masks. (*is this right?*)

(*Used for our invariants*)
Hypothesis syscall_preserves_instruction_tags :
  forall sc st st',
    Sym.instructions_tagged valid_jmp (Symbolic.mem st) ->
    Symbolic.sem sc st = Some st' ->
    Sym.instructions_tagged valid_jmp (Symbolic.mem st').

Hypothesis syscall_preserves_valid_jmp_tags :
  forall sc st st',
    Sym.valid_jmp_tagged stable (Symbolic.mem st) ->
    Symbolic.sem sc st = Some st' ->
    Sym.valid_jmp_tagged stable (Symbolic.mem st').

Hypothesis syscall_preserves_entry_tags :
  forall sc st st',
    Sym.entry_points_tagged stable (Symbolic.mem st) ->
    Symbolic.sem sc st = Some st' ->
    Sym.entry_points_tagged stable (Symbolic.mem st').

Definition refine_state_no_inv (sst : @Symbolic.state mt sym_params) (cst : Concrete.state mt) :=
  @refine_state_weak mt ops sym_params e ki stable sst cst.

Definition refine_state (sst : @Symbolic.state mt sym_params) (cst : Concrete.state mt) :=
  @refine_state_weak mt ops sym_params e ki stable sst cst /\
  Sym.invariants stable sst.

Definition is_user (x : atom (word mt) (word mt)) :=
  rules.word_lift (fun t => rules.is_user t) (common.tag x).

Definition coerce (x : atom (word mt) (word mt)) : atom (word mt) (@cfi_tag mt) :=
  match rules.decode (common.tag x) with
    | Some (rules.USER tg) => (common.val x)@tg
    | _ => (common.val x)@DATA (*this is unreachable in our case, dummy value*)
  end.

(*Q: Why can't I get it to typecheck when I substitute the existential with what
  I use to instantiate it?*)
Lemma mem_refinement_equiv :
  forall (smem : @Symbolic.memory mt sym_params) cmem cmem',
    refinement_common.refine_memory smem cmem ->
    Conc.equiv cmem cmem' ->
    exists (smem' : @Symbolic.memory mt sym_params),
    refinement_common.refine_memory smem' cmem' /\
    Sym.equiv smem smem'.
Proof.
  intros smem cmem cmem' REF EQUIV.
  exists (PartMaps.map coerce (filter is_user cmem')).
  split.
  { (*refinement proof*)
    intros addr v tg.
    split.
    { intro CGET.
      rewrite PartMaps.map_correctness. rewrite filter_correctness.
      rewrite CGET. simpl.
      destruct (is_user v@(rules.encode (rules.USER (user_tag:=cfi_tag_eqType) tg))) eqn:USER.
      + simpl. unfold coerce. simpl. rewrite rules.decodeK. reflexivity.
      + unfold is_user in USER. simpl in USER.
        unfold rules.word_lift in USER.
        rewrite rules.decodeK in USER. simpl in USER. discriminate. }
    { intro SGET.
      rewrite PartMaps.map_correctness filter_correctness in SGET.
      destruct (get cmem' addr) eqn:CGET.
      - destruct a as [cv ctg].
        simpl in SGET.
        unfold is_user, rules.word_lift in SGET.
        destruct (rules.decode ctg) eqn:CTG.
        + destruct t; rewrite CTG in SGET; simpl in *.
          * unfold coerce in SGET. rewrite CTG in SGET.
            simpl in SGET. inv SGET.
            simpl. apply rules.encodeK in CTG. rewrite CTG. reflexivity.
          * discriminate.
          * discriminate.
        + rewrite CTG in SGET. simpl in SGET; discriminate.
      - simpl in SGET. discriminate.
    }
  }
  { (*equiv proof*)
    unfold Sym.equiv, pointwise.
    intro addr.
    unfold Conc.equiv in EQUIV. unfold pointwise in EQUIV.
    specialize (EQUIV addr). simpl.
    destruct (get smem addr) eqn:SGET; simpl in SGET; rewrite SGET.
    - destruct a as [v utg].
      unfold refinement_common.refine_memory in REF.
      specialize (REF addr v utg).
      destruct REF as [REFCS REFSC].
      assert (CGET := REFSC SGET).
      rewrite CGET in EQUIV.
      destruct (get cmem' addr) eqn:CGET'.
      + destruct a as [v' ctg'].
        inversion EQUIV
          as [a a' v0 v'' ut ut' EQ1 EQ2 SEQUIV| a a' NEQ EQ]; subst.
        * rewrite PartMaps.map_correctness filter_correctness.
          rewrite CGET'.
          unfold is_user. unfold rules.word_lift.
          simpl. inversion EQ1; inversion EQ2; subst.
          rewrite rules.decodeK.
          simpl. unfold coerce.
          simpl. rewrite rules.decodeK.
          apply rules.encode_inj in H1.
          inversion H1; subst.
          assumption.
        * simpl in NEQ.
          assert (CONTRA: (exists ut : cfi_tag,
           rules.encode (rules.USER (user_tag:=cfi_tag_eqType) utg) =
           rules.encode (rules.USER (user_tag:=cfi_tag_eqType) ut)))
             by (eexists; eauto).
          apply NEQ in CONTRA. destruct CONTRA.
      + destruct EQUIV.
    - destruct (get cmem addr) eqn:CGET.
      + destruct a as [v ctg]. unfold refinement_common.refine_memory in REF.
        rewrite PartMaps.map_correctness filter_correctness.
        unfold is_user. unfold rules.word_lift.
        destruct (get cmem' addr) eqn:CGET'.
        * destruct a as [v' ctg'].
          simpl.
          destruct (rules.decode ctg') eqn:DECODE.
          - destruct (rules.is_user t) eqn:USER.
            + simpl.
              unfold rules.is_user in USER.
              destruct t; try discriminate.
              apply rules.encodeK in DECODE.
              rewrite <- DECODE in EQUIV.
              inversion EQUIV
                as [a a' v0 v'' ? ut' EQ1 EQ2 SEQUIV| a a' NEQ EQ]; subst.
               { inversion EQ1; subst.
                 apply REF in CGET. rewrite SGET in CGET; discriminate. }
               { simpl in NEQ.
                 inv EQ.
                 apply NEQ. eexists; eauto.
               }
            + simpl. constructor.
          - simpl. constructor.
        * destruct EQUIV.
     + destruct (get cmem' addr) eqn:CGET'.
       * destruct EQUIV.
       * rewrite PartMaps.map_correctness filter_correctness.
         rewrite CGET'. simpl. constructor.
  }
Qed.

Definition creg_to_sreg x :=
  match is_user x with
    | true => Some (coerce x)
    | false => None
  end.

Lemma reg_refinement_equiv :
  forall (sregs : @Symbolic.registers mt sym_params) cregs cregs',
    refinement_common.refine_registers sregs cregs ->
    Conc.reg_equiv cregs cregs' ->
    exists (sregs' : @Symbolic.registers mt sym_params),
    refinement_common.refine_registers sregs' cregs' /\
    Sym.equiv sregs sregs'.
Proof.
  intros sreg creg creg' REF EQUIV.
  exists (MapTP.map creg_to_sreg creg').
  split.
  { (*Refinement proof*)
    intros n v tg.
    split.
    { intros CGET'.
      rewrite MapTP.map_correctness.
      rewrite CGET'. simpl.
      unfold creg_to_sreg.
      destruct (is_user v@(rules.encode (rules.USER (user_tag:=cfi_tag_eqType) tg))) eqn:USER.
      + simpl. unfold coerce. simpl. rewrite rules.decodeK. reflexivity.
      + unfold is_user in USER. simpl in USER.
        unfold rules.word_lift in USER.
        rewrite rules.decodeK in USER. simpl in USER. discriminate. }
    { intro SGET'.
      rewrite MapTP.map_correctness in SGET'.
      destruct (TotalMaps.get creg' n) eqn:CGET'.
      simpl in SGET'.
      unfold creg_to_sreg in SGET'.
      unfold is_user, rules.word_lift in SGET'.
      simpl in SGET'.
      destruct (rules.decode tag) eqn:CTG.
      + unfold rules.is_user, coerce in SGET'. destruct t; simpl in CTG.
        * rewrite CTG in SGET'.
          simpl in SGET'. inv SGET'.
          simpl. apply rules.encodeK in CTG. rewrite CTG. reflexivity.
        * discriminate.
        * discriminate.
      + discriminate.
    }
  }
  { (*equiv proof*)
    unfold Sym.equiv, pointwise.
    intro n.
    unfold Conc.reg_equiv in EQUIV.
    specialize (EQUIV n).
    destruct (get sreg n) eqn:SGET; simpl in SGET; rewrite SGET.
    - destruct a as [v utg].
      specialize (REF n v utg).
      destruct REF as [REFCS REFSC].
      assert (CGET := REFSC SGET).
      rewrite CGET in EQUIV.
      rewrite MapTP.map_correctness.
      destruct (TotalMaps.get creg' n) eqn:CGET'.
      inversion EQUIV
        as [a a' v0 v'' ? ut' EQ1 EQ2 SEQUIV| a a' NEQ EQ]; subst.
      * inv EQ2.
        unfold creg_to_sreg, is_user, rules.word_lift, coerce, rules.is_user.
        simpl. rewrite rules.decodeK.
        inv EQ1.
        apply rules.encode_inj in H1. inv H1.
        assumption.
      * inv EQ. simpl in NEQ.
        assert (CONTRA: (exists ut : cfi_tag,
           rules.encode (rules.USER (user_tag:=cfi_tag_eqType) utg) =
           rules.encode (rules.USER (user_tag:=cfi_tag_eqType) ut)))
          by (eexists; eauto).
        apply NEQ in CONTRA. destruct CONTRA.
    - rewrite MapTP.map_correctness.
      destruct (TotalMaps.get creg' n) eqn:CGET'.
      destruct (TotalMaps.get creg n) eqn:CGET.
      inversion EQUIV
        as [a a' v0 v'' ? ut' EQ1 EQ2 SEQUIV| a a' NEQ EQ]; subst.
       + inv EQ1.
         apply REF in CGET.
         rewrite CGET in SGET. discriminate.
       + inv EQ.
         unfold creg_to_sreg, is_user, rules.word_lift, coerce.
         simpl.
         destruct (rules.decode tag) eqn:DECODE.
         { destruct t.
           - apply rules.encodeK in DECODE.
             simpl in NEQ.
             exfalso. apply NEQ. eexists; eauto.
           - unfold rules.is_user. constructor.
           - unfold rules.is_user. constructor.
         }
         { constructor. }
  }
Qed.

(*Kernel invariants preserved by attacker*)
Lemma mvec_in_kernel_preserved_by_equiv
      (mem : Concrete.memory mt) (mem' : Concrete.memory mt) :
  refinement_common.mvec_in_kernel mem ->
  Conc.equiv mem mem' ->
  refinement_common.mvec_in_kernel mem'.
Proof.
  intros INV MEQUIV.
  unfold refinement_common.mvec_in_kernel.
  intros addr INMVEC.
  specialize (INV addr).
  apply INV in INMVEC.
  destruct INMVEC as [v GET].
  unfold Conc.equiv, pointwise in MEQUIV.
  specialize (MEQUIV addr).
  rewrite GET in MEQUIV.
  destruct (get mem' addr) eqn:GET'.
  - inversion MEQUIV
      as [? a' v0 v'' ? ut' EQ1 EQ2 SEQUIV| ? a' NEQ EQ]; subst.
    + inversion EQ1; subst.
      rewrite rules.encode_kernel_tag in H1.
      apply rules.encode_inj in H1.
      discriminate.
    + eexists; reflexivity.
  - destruct MEQUIV.
Qed.

Lemma wf_entry_points_preserved_by_equiv
      (mem : Concrete.memory mt) (mem' : Concrete.memory mt) :
  refinement_common.wf_entry_points stable mem ->
  Conc.equiv mem mem' ->
  refinement_common.wf_entry_points stable mem'.
Proof.
  intros INV MEQUIV.
  intros addr stg.
  specialize (INV addr stg).
  specialize (MEQUIV addr).
  split.
  { intro SCALL.
    apply INV in SCALL.
    destruct (get mem addr) eqn:GET.
    - destruct a as [v ctg].
      destruct (get mem' addr) eqn:GET'.
      + destruct a as [v' ctg'].
        inversion MEQUIV
          as [? a' v0 v'' ? ut' EQ1 EQ2 SEQUIV| ? a' NEQ EQ]; subst.
        * inv EQ1.
          apply andb_true_iff in SCALL.
          destruct SCALL as [? SCALL].
          move/eqP/rules.encode_inj: SCALL => CONTRA.
          inversion CONTRA.
        * simpl in *. inv EQ. assumption.
      + destruct MEQUIV.
    - discriminate.
  }
  { intro CALL.
    destruct (get mem' addr) eqn:GET'.
    - destruct a as [v' ctg'].
      destruct (get mem addr) eqn:GET.
      + destruct a as [v ctg].
        inversion MEQUIV
          as [? a' v0 v'' ? ut' EQ1 EQ2 SEQUIV| ? a' NEQ EQ]; subst.
        * inv EQ2.
          apply andb_true_iff in CALL.
          destruct CALL as [? CALL].
          move/eqP/rules.encode_inj: CALL => CONTRA.
          inversion CONTRA.
        * simpl in *. inv EQ. apply INV in CALL.
          assumption.
      + destruct MEQUIV.
    - discriminate.
  }
Qed.

(*Q: Do we want to prove anything about this? Maybe using the other assumptions
   on ki?*)
Hypothesis ki_preserved_by_equiv :
  forall mem mem' reg reg' cache int,
    refinement_common.kernel_invariant_statement ki mem reg cache int ->
    Conc.equiv mem mem' ->
    Conc.reg_equiv reg reg' ->
    refinement_common.kernel_invariant_statement ki mem' reg' cache int.

Hint Resolve mvec_in_kernel_preserved_by_equiv.
Hint Resolve wf_entry_points_preserved_by_equiv.

Lemma backwards_simulation_attacker_aux sst cst cst' :
  refine_state_no_inv sst cst ->
  Conc.step_a cst cst' ->
  exists sst',
    Sym.step_a sst sst' /\
    refine_state_no_inv sst' cst'.
Proof.
  intros REF STEP.
  inversion STEP; subst.
  unfold refine_state in REF.
  destruct REF as [REF | CONTRA].
  move: tpc INUSER REF STEP => tpc' INUSER REF STEP.
  - destruct REF as [smem sreg int cmem cregs cache' epc' pc' tpc
                     ? ? REFM REFR ? ? WFENTRY ?].
    subst sst.
    symmetry in EC. inv EC.
    destruct (mem_refinement_equiv REFM MEQUIV) as [smem' [REFM' SMEQUIV]].
    destruct (reg_refinement_equiv REFR REQUIV) as [sreg' [REFR' SREQUIV]].
    eexists; split; [idtac | left]; econstructor; eauto.
  - destruct CONTRA as [? [? [? [? CONTRA]]]].
    clear REQUIV MEQUIV.
    unfold refinement_common.kernel_exec in CONTRA.
    apply restricted_exec_snd in CONTRA.
    unfold refinement_common.in_kernel in CONTRA.
    simpl in CONTRA. unfold Concrete.is_kernel_tag in CONTRA.
    unfold rules.word_lift in INUSER.
    move/eqP: CONTRA => CONTRA.
    rewrite CONTRA in INUSER.
    rewrite rules.encode_kernel_tag in INUSER.
    rewrite rules.decodeK in INUSER.
    unfold rules.is_user in INUSER.
    congruence.
Qed.

Theorem backwards_simulation_attacker sst cst cst' :
  refine_state sst cst ->
  Conc.step_a cst cst' ->
  exists sst',
    Sym.step_a sst sst' /\
    refine_state sst' cst'.
Proof.
  intros REF STEP.
  destruct REF as [REF INV];
  destruct (backwards_simulation_attacker_aux REF STEP) as [sst' [SSTEP REF']];
  eexists; split; [eassumption | split];
  eauto using Sym.invariants_preserved_by_step_a.
Qed.

(* Preservation related stuff, probably move to other file*)

Definition in_user := @in_user mt ops sym_params e.

Definition smachine := Sym.symbolic_cfi_machine stable.
Definition cmachine := Conc.concrete_cfi_machine ki stable masks.

Context {kcc : kernel_code_correctness ki stable}. (*should this go to the top?*)

Definition check st st' := in_user st && in_user st'.

Program Instance cfi_refinementSC  :
  (machine_refinement smachine cmachine) := {
    refine_state st st' := refine_state st st';

    check st st' := check st st'
}.
Next Obligation.
Proof.
  unfold refine_state in REF.
  destruct REF as [REF INV].
  destruct REF as [UREF | KREF].
  - (*starting from a user state*)
    split.
    { (*Visible step starting from a user state*)
      intro VIS.
      unfold check in VIS.
      apply andb_true_iff in VIS.
      destruct VIS as [VIS VIS'].
      assert (HIT: @hit_step mt ops sym_params e cst cst')
          by (constructor; auto).
      destruct (cache_hit_simulation UREF HIT) as [sst' [SSTEP REF']].
      unfold refine_state, refine_state_weak.
      eexists; split. eauto.
      split;
      eauto using Sym.invariants_preserved_by_step.
    }
    { (*invisible step starting a from user state*)
      intro INVIS.
      unfold check in INVIS.
      apply andb_false_iff in INVIS.
      destruct INVIS as [CONTRA | NUSER].
      - eapply @refine_state_in_user in UREF.
        unfold in_user in CONTRA.
        rewrite UREF in CONTRA. discriminate.
      - (*user to not user step*)
        left.
        unfold refine_state. split.
        right. exists cst; exists cst'.
        repeat (split; auto).
        unfold kernel_exec.
        destruct (user_into_kernel UREF STEP NUSER).
        eapply re_refl; eauto.
        eauto using Sym.invariants_preserved_by_step.
    }
  - (*starting from a kernel state*)
    split.
    { (*and taking a visible step*)
      intro VIS.
      unfold check in VIS.
      apply andb_true_iff in VIS.
      destruct VIS as [VIS VIS'].
      destruct KREF as [ust [kst [UREF [UKSTEP KEXEC]]]].
      unfold kernel_exec in KEXEC.
      apply restricted_exec_snd in KEXEC.
      unfold in_user in VIS.
      apply (@in_user_in_kernel mt ops sym_params e) in VIS.
      rewrite VIS in KEXEC. discriminate.
    }
    { (*and taking an invisible step*)
      intro VIS.
      assert (REFW : @refine_state_weak mt ops sym_params e ki stable ast cst)
        by (right; auto).
      destruct (backwards_simulation REFW STEP) as [REFW' | [ast' [STEP' REF']]].
      - left. split; auto.
      - right. eexists; split; eauto.
        unfold refine_state.
        split.
        + left. assumption.
        + eauto using Sym.invariants_preserved_by_step.
    }
Qed.
Next Obligation.
  apply (backwards_simulation_attacker REF STEPA).
Qed.

Import ListNotations.

(*XXX: Move this to refinement_common?*)
Lemma kernel_step cst cst' ast kst cst0 :
  refinement_common.refine_state ki stable ast cst0 ->
  Concrete.step ops rules.masks cst0 kst ->
  kernel_exec kst cst ->
  Concrete.step _ masks cst cst' ->
  in_kernel cst = true ->
  in_user cst' = false ->
  in_kernel cst' = true.
Proof.
  intros REF STEP EXEC STEP' INKERNEL INUSER.
  assert (REFW: @refine_state_weak _ _ _ _ ki stable ast cst).
  { right. eauto. }
  generalize (backwards_simulation REFW STEP').
  intros [[REF' | (? & ? & ? & ? & KEXEC')] | (? & _ & REF')].
  - apply @refine_state_in_user in REF'. unfold in_user in INUSER. congruence.
  - by apply restricted_exec_snd in KEXEC'.
  - apply @refine_state_in_user in REF'. unfold in_user in INUSER. congruence.
Qed.

(*This is a helper lemma to instantiate CFI refinement between
  symbolic and concrete*)
Lemma attacker_no_v : forall si sj,
                 Sym.invariants stable si ->
                 Sym.ssucc stable si sj = false ->
                 Symbolic.step stable si sj ->
                 Sym.step_a si sj ->
                 False.
Proof.
  intros si sj INV SUCC STEP STEPA.
  destruct INV as [ITG [VTG ETG]].
  inversion STEPA. subst.
  inversion STEP; 
   repeat (
      match goal with
        | [H: Symbolic.next_state_pc _ _ _ = _ |- _] => 
          unfold Symbolic.next_state_pc in H
        | [H: Symbolic.next_state_reg _ _ _ _ = _ |- _] => 
          unfold Symbolic.next_state_reg in H
        | [H: Symbolic.next_state_reg_and_pc _ _ _ _ _ = _ |- _] => 
          unfold Symbolic.next_state_reg_and_pc in H
        | [H: Symbolic.next_state _ _ _ = Some _ |- _] =>
          unfold Symbolic.next_state in H; simpl in H; match_inv
      end); subst;
   unfold Sym.ssucc in SUCC; simpl in SUCC;
   inversion ST; try subst;

   try match goal with
     | [H: (?Pc + 1)%w = ?Pc |- _] => 
       rewrite H in SUCC; try subst mem' reg' int; try subst mem reg
  end;
   try rewrite PC in SUCC; try rewrite INST in SUCC;
   try match goal with 
     | [H: Some _ = Some _ |- _] => simpl in H; inversion H
   end;
   try match goal with
     | [H: (?Pc + 1)%w = ?Pc |- _] => 
       rewrite H in SUCC; rewrite eqxx in SUCC; discriminate
   end. 
  (*jump case*)
  unfold Sym.instructions_tagged in ITG.
  specialize (ITG _ _ _ PC). simpl in ITG. subst.
  congruence.
  (*bnz case*)
  destruct (w == 0%w).
  * subst mem' reg'.
    rewrite H2 in SUCC. rewrite PC in SUCC.
    rewrite INST in SUCC.
    apply orb_false_iff in SUCC. destruct SUCC.
    rewrite H2 in H. rewrite eqxx in H. discriminate.
  * subst mem' reg'.
    rewrite H2 in SUCC. rewrite PC in SUCC.
    rewrite INST in SUCC.
    apply orb_false_iff in SUCC. destruct SUCC.
    rewrite H2 in H0. rewrite eqxx in H0. discriminate.
 (*jal case*)
  unfold Sym.instructions_tagged in ITG.
  specialize (ITG _ _ _ PC). simpl in ITG. subst.
  congruence.
  (*syscall case*)
  rewrite GETCALL in SUCC. discriminate.
Qed.

Definition khandler := @rules.handler cfi_tag_eqType mt ops e (@Symbolic.handler sym_params).
Definition uhandler := @Symbolic.handler sym_params.

(*XXX: Move these to refinement_common*)
Lemma get_reg_no_user sreg reg r v ctg t :
  @refinement_common.refine_registers mt ops sym_params e sreg reg ->
  get sreg r = None ->
  TotalMaps.get reg r = v@ctg ->
  rules.decode ctg = Some t ->
  t = rules.KERNEL \/ (exists ut, t = rules.ENTRY ut).
Proof.
  intros REF SGET GET DEC.
  destruct t.
  - apply rules.encodeK in DEC.
    rewrite <- DEC in GET.
    apply REF in GET.
    rewrite SGET in GET. discriminate.
  - auto.
  - right; eexists; reflexivity.
Qed.

Lemma get_mem_no_user smem mem addr v ctg t :
  @refinement_common.refine_memory mt ops sym_params e smem mem ->
  get smem addr = None ->
  get mem addr = Some v@ctg ->
  rules.decode ctg = Some t ->
  t = rules.KERNEL \/ (exists ut, t = rules.ENTRY ut).
Proof.
  intros REF SGET GET DEC.
  destruct t.
  - apply rules.encodeK in DEC.
    rewrite <- DEC in GET.
    apply REF in GET.
    rewrite SGET in GET. discriminate.
  - auto.
  - right; eexists; reflexivity.
Qed.

Lemma in_user_ctpc cst :
  @refinement_common.in_user mt ops sym_params e cst = true ->
  exists ut,
    rules.decode (common.tag (Concrete.pc cst)) = Some (rules.USER ut).
Proof.
  intros USER.
  unfold refinement_common.in_user in USER.
  unfold rules.word_lift in USER.
  destruct (rules.decode (common.tag (Concrete.pc cst))) eqn:DEC.
  - destruct t.
    + eexists; reflexivity.
    + simpl in USER. discriminate.
    + simpl in USER. discriminate.
  - discriminate.
Qed.

(*Case 1: umvec = Some & cmvec = Some*)

Lemma umvec_implies_cmvec_aux sst cst smvec :
  refinement_common.refine_state ki stable sst cst ->
  build_mvec stable sst = Some smvec ->
  exists cmvec, build_cmvec mt cst = Some cmvec.
Proof.
  intros REF SMVEC.
  assert (USER := refinement_common.refine_state_in_user REF).
  destruct REF as [smem sreg int mem reg cache epc pc stpc
                   ? ? REFM REFR CACHE MVE WF KI].
  subst sst cst.
  unfold build_mvec in SMVEC.
  destruct (get smem pc) eqn:SGET.
  - destruct a as [w itg].
    simpl in SMVEC.
    destruct (decode_instr w) eqn:INST.
    + destruct i eqn:OP;
      unfold build_cmvec;
      apply REFM in SGET; rewrite SGET;
      simpl; rewrite INST;
      unfold bind in SMVEC;
      repeat match goal with
        | [H: match ?Expr with _ => _ end = _ |- _] =>
          remember (Expr) as hexpr; destruct hexpr
      end;
      try (eexists; reflexivity);
      repeat match goal with
               | [H: Some ?A = get _ _ |- _] => destruct A; symmetry in H
             end;
      simpl in *;
      repeat match goal with
               | [H : get sreg _ = Some _ |- _] =>
                 apply REFR in H; (try rewrite H)
               | [H : get smem _ = Some _ |- _] =>
                 apply REFM in H; try (rewrite H)
             end;
      simpl; try (eexists; reflexivity);
      try discriminate.
    + discriminate.
  - destruct (Symbolic.get_syscall stable pc) eqn:GETCALL.
    + unfold wf_entry_points in WF.
      remember (Symbolic.entry_tag s) eqn:TG.
      symmetry in TG.
      specialize (WF pc s0).
      assert (ECALL: exists sc, Symbolic.get_syscall stable pc = Some sc
                                /\ Symbolic.entry_tag sc = s0)
        by (eexists; eauto).
      apply WF in ECALL.
      destruct (get mem pc) eqn:GET.
      * destruct a.
        apply andb_true_iff in ECALL.
        destruct ECALL as [ENC CTG].
        unfold build_cmvec.
        rewrite GET.
        move/eqP:ENC => DEC.
        simpl.
        rewrite /is_nop in DEC.
        destruct (decode_instr val) as [[]|]; try by [].
        eexists; reflexivity.
      * discriminate.
    + discriminate.
Qed.

(*wrapping the above theorem to handle common contradiction*)
Lemma umvec_implies_cmvec sst cst smvec :
  in_user cst ->
  refine_state sst cst ->
  build_mvec stable sst = Some smvec ->
  exists cmvec, build_cmvec mt cst = Some cmvec.
Proof.
  intros USER [[REF | CONTRA] ?] MVEC.
  - eapply umvec_implies_cmvec_aux; eauto.
  - exfalso.
    destruct CONTRA as [? [? [? [? KEXEC]]]].
    apply restricted_exec_snd in KEXEC.
    unfold in_user in USER.
    eapply @in_user_in_kernel in USER.
    by congruence.
Qed.

Lemma uhandler_chandler_stop sst umvec :
  build_mvec stable sst = Some umvec ->
  uhandler umvec = None ->
  khandler (rules.encode_mvec (rules.mvec_of_umvec_with_calls umvec)) = None.
Proof. (*Postponted until khandler rewrite - proved but ok.*)
  intros UMVEC UHANDLER.
  unfold uhandler in UHANDLER. unfold Symbolic.handler in UHANDLER. simpl in UHANDLER.
  destruct sst as [mem regs [pc tpc] int].
  unfold build_mvec in UMVEC.
  destruct (get mem pc) eqn:GET.
  - destruct (decode_instr (common.val a)) eqn:INST.
    + destruct i eqn:OP; simpl in UMVEC; unfold bind in UMVEC;
      repeat match goal with
        | [H: match ?Expr with _ => _ end = _ |- _] =>
          remember (Expr) as hexpr; destruct hexpr
      end;
      inv UMVEC;
      unfold cfi_handler in UHANDLER; match_inv; subst;
      unfold khandler; simpl;
      rewrite op_to_wordK; rewrite rules.decodeK; try (rewrite rules.decodeK);
      simpl;
      try match goal with
        | [H : valid_jmp _ _ = false |- _] => rewrite H
      end;
       try reflexivity; repeat (rewrite rules.decodeK); try reflexivity.
    + discriminate.
  - destruct (Symbolic.get_syscall stable pc) eqn:GETCALL.
    + unfold cfi_handler in UHANDLER.
      inv UMVEC.
      match_inv; subst; simpl;
      rewrite op_to_wordK; rewrite rules.decodeK; try (rewrite rules.decodeK);
      simpl;
      try match goal with
        | [H : valid_jmp _ _ = false |- _] => rewrite H
      end; try reflexivity.
    + discriminate.
Qed.

Lemma unique_cmvec_aux sst cst umvec cmvec :
  @refinement_common.refine_state mt ops sym_params e ki stable sst cst ->
  build_mvec stable sst = Some umvec ->
  build_cmvec mt cst = Some cmvec ->
  rules.encode_mvec (rules.mvec_of_umvec_with_calls umvec) = cmvec.
Proof.
  intros REF UMVEC CMVEC.
  destruct REF as [smem sreg int mem reg cache epc pc stpc
                        ? ? REFM REFR CACHE MVE WF KI].
  subst.
  unfold build_mvec in UMVEC.
  destruct (get smem pc) eqn:SGET.
  - destruct a as [v tg]. simpl in UMVEC.
    destruct (decode_instr v) eqn:DEC.
    + destruct i eqn:OP;
      unfold bind in UMVEC;
      repeat match goal with
               | [H: match ?Expr with _ => _ end = _|- _] =>
                 remember (Expr) as hexpr; destruct hexpr
             end;
      repeat match goal with
               | [H: Some ?A = get _ _ |- _] => destruct A; symmetry in H
             end;
      repeat match goal with
               | [H : get sreg _ = Some _ |- _] =>
                 apply REFR in H
               | [H : get smem _ = Some _ |- _] =>
                 apply REFM in H
             end;
      unfold build_cmvec, bind in CMVEC;
      repeat match goal with
               | [H: match ?Expr with _ => _ end = _, H': ?Expr = _ |- _] =>
                 rewrite H' in H; simpl in H'
             end;
      inv CMVEC;
      inv UMVEC;
      repeat match goal with
               | [H: TotalMaps.get _ _ = _ |- _] => rewrite H
             end;
      unfold rules.mvec_of_umvec; simpl;
      unfold rules.encode_mvec; simpl;
      try reflexivity.
      (*handling automation fails*)
      * rewrite Heqhexpr in H0.
        simpl in H0.
        simpl in Heqhexpr0.
        rewrite Heqhexpr0 in H0.
        inv H0. rewrite Heqhexpr1.
        reflexivity.
      * rewrite Heqhexpr in H0.
        simpl in H0. simpl in Heqhexpr1. rewrite Heqhexpr1 in H0.
        inv H0.
        rewrite Heqhexpr0.
        reflexivity.
    + discriminate.
  - destruct (Symbolic.get_syscall stable pc) eqn:GETCALL.
    { (*syscall case*)
      inv UMVEC.
      unfold rules.mvec_of_umvec. simpl.
      unfold rules.encode_mvec. simpl.
      remember (Symbolic.entry_tag s) as etag eqn:ETAG. symmetry in ETAG.
      unfold wf_entry_points in WF.
      specialize (WF pc etag).
      assert (ECALL : (exists sc : Symbolic.syscall mt,
          Symbolic.get_syscall stable pc = Some sc /\
          Symbolic.entry_tag sc = etag))
        by (eexists; eauto).
      apply WF in ECALL.
      destruct (get mem pc) eqn:GET.
      - destruct a. apply andb_true_iff in ECALL.
        destruct ECALL as [VAL TG].
        move/eqP:VAL => VAL.
        move/eqP:TG => TG.
        unfold build_cmvec in CMVEC.
        rewrite GET in CMVEC. simpl in CMVEC.
        rewrite /is_nop in VAL.
        destruct (decode_instr val) as [[]|]; try by [].
        inv CMVEC.
        reflexivity.
      - discriminate.
    }
    { discriminate. }
Qed.

Lemma unique_cmvec sst cst umvec cmvec :
  in_user cst = true ->
  refine_state sst cst ->
  build_mvec stable sst = Some umvec ->
  build_cmvec mt cst = Some cmvec ->
  rules.encode_mvec (rules.mvec_of_umvec_with_calls umvec) = cmvec.
Proof.
  intros USER REF MVEC CMVEC.
  destruct REF as [REF INV].
  destruct REF as [UREF | KREF].
  - eauto using unique_cmvec_aux.
  - destruct KREF as [? [? [? [? KEXEC]]]].
    apply restricted_exec_snd in KEXEC.
    apply in_user_in_kernel in USER.
    by congruence.
Qed.

(*Case 2*)

Lemma no_user_access_implies_halt_aux sst cst cmvec :
  refinement_common.refine_state ki stable sst cst ->
  build_mvec stable sst = None ->
  build_cmvec mt cst = Some cmvec ->
  khandler cmvec = None.
Proof.
  intros REF SMVEC CMVEC.
  destruct REF as [smem sreg int mem reg cache epc pc stpc
                        ? ? REFM REFR CACHE MVE WF KI].
  subst.
  unfold khandler.
  unfold build_mvec in SMVEC.
  destruct (get smem pc) eqn:SGET.
  - destruct a as [w itg].
    simpl in SMVEC.
    destruct (decode_instr w) eqn:INST.
    Opaque Symbolic.handler. Opaque cfi_handler.
    + destruct i eqn:OP;
      simpl in SMVEC; try discriminate; (*nop case*)
      apply REFM in SGET;
      unfold bind in SMVEC;
      repeat match goal with
        | [H: match ?Expr with _ => _ end = _ |- _] =>
          remember (Expr) as hexpr; destruct hexpr
        | [H: Some ?A = get _ _ |- _] => destruct A; symmetry in H
        | [H: None = get _ _ |- _] => symmetry in H
      end;
      try discriminate;
      unfold build_cmvec in CMVEC;
      repeat match goal with
               |[H: get sreg ?R = Some _ |- _] =>
                apply REFR in H
               |[H: get smem ?Addr = Some _ |- _] =>
                apply REFM in H
             end;
      unfold bind in CMVEC;
      repeat match goal with
        | [H: match ?Expr with _ => _ end = _, H1: ?Expr = _ |- _] =>
          rewrite H1 in H; simpl in H
             end;
      try match goal with (*for memory accesses*)
            |[H: match get mem (common.val (TotalMaps.get _ ?R)) with _ => _ end = _,
                 H1: TotalMaps.get _ ?R = _ |- _] => rewrite H1 in H
          end;
      try match goal with (*for memory accesses*)
            |[H: match get mem (common.val (TotalMaps.get ?Reg ?R)) with _ => _ end = _
              |- _] => destruct (TotalMaps.get Reg R) eqn:?
          end;
      repeat match goal with
        | [H: match ?Expr with _ => _ end = _, H1: ?Expr = _ |- _] =>
          rewrite H1 in H; simpl in H
             end; simpl in *;
      try match goal with
            | [H: get smem ?Addr = None,
                  H1: match get mem ?Addr with _ => _ end = _ |- _] =>
              destruct (get mem Addr) as [[mval mtg] |] eqn:?;
                [ idtac | discriminate]
          end;
      try match goal with
               | [H: get smem ?Addr = None, H1: get mem ?Addr = Some _@?Mtg |- _] =>
                 destruct (rules.decode Mtg) eqn:DECMTG;
                   [ destruct (get_mem_no_user _ REFM H H1 DECMTG) | idtac]; clear H1
          end;
      try match goal with
            | [ H1: match get mem ?Addr with _ => _ end = _ |- _] =>
              destruct (get mem Addr) as [[mval2 mtg2] |] eqn:?;
                 [destruct (rules.decode mtg2) as [[| |] | ] eqn:DECMTG2 | discriminate]
          end;
      inv CMVEC;
      repeat match goal with
               | [H: TotalMaps.get ?Reg ?R = _ |- _] =>
                 rewrite H
             end;
      repeat match goal with
               | [|- context[TotalMaps.get ?Reg ?R]] =>
                 destruct (TotalMaps.get Reg R) eqn:?
             end;
      try match goal with
               | [H: get sreg ?R = None, H1: TotalMaps.get reg ?R = _@?Ctg |- _] =>
                 destruct (rules.decode Ctg) eqn:DECTG1;
                   [ destruct (get_reg_no_user _ REFR H H1 DECTG1) | idtac]; clear H1
          end;
      try match goal with
              | [H: TotalMaps.get reg ?R = _@?Ctg |- _] =>
                destruct (rules.decode Ctg) as [[| |] |] eqn:DECTG2;
                  clear H
            end;
        try match goal with
              | [H: TotalMaps.get reg ?R = _@?Ctg |- _] =>
                destruct (rules.decode Ctg) as [[| |] |] eqn:DECTG3;
                  clear H
            end;
       repeat match goal with
                | [H: exists _, _ = rules.ENTRY _ |- _] => destruct H
              end;
        subst;
      simpl;
      try rewrite op_to_wordK;  simpl;
      try rewrite DECTG1;
      try rewrite DECTG2;
      try rewrite DECTG3;
      try rewrite DECMTG;
      try rewrite DECMTG2;
      repeat rewrite (rules.decodeK);
      simpl;
      try reflexivity.
    + unfold build_cmvec in CMVEC.
      apply REFM in SGET. rewrite SGET in CMVEC.
      rewrite INST in CMVEC.
      by discriminate.
  - destruct (Symbolic.get_syscall stable pc) eqn:GETCALL.
    + discriminate.
    + unfold build_cmvec in CMVEC.
      destruct (get mem pc) eqn:GET.
      * destruct a as [v ctg].
        simpl in CMVEC.
        destruct (rules.decode ctg) eqn:DEC.
        { destruct (get_mem_no_user pc REFM SGET GET DEC); subst.
          - unfold rules.handler.
            destruct (decode_instr v) eqn:INST.
            + destruct i eqn:OP;
              unfold bind in CMVEC;
              try match goal with
                      [H: match get mem ?Addr with _ => _ end = _ |- _] =>
                      destruct (get mem Addr)
            end;
              inv CMVEC;
              rewrite op_to_wordK;
              try rewrite rules.decodeK;
              rewrite DEC; reflexivity.
            + discriminate.
          - (*case fetched instr is tagged entry*)
            destruct H as [ut H].
            rewrite H in DEC.
            unfold wf_entry_points in WF.
            unfold rules.handler.
            destruct (decode_instr v) eqn:INST.
            + destruct i eqn:OP;
              try (unfold bind in CMVEC;
              try match goal with
                      [H: match get mem ?Addr with _ => _ end = _ |- _] =>
                      destruct (get mem Addr)
            end;
              inv CMVEC;
              rewrite op_to_wordK;
              try rewrite rules.decodeK;
              rewrite DEC; reflexivity).
              (*entry point and NOP, sc case*)
              exfalso.
              specialize (WF pc ut).
              rewrite GET in WF.
              apply rules.encodeK in DEC.
              rewrite /is_nop INST DEC eqxx /= in WF.
              have CONTRA: true = true by [].
              apply WF in CONTRA.
              destruct CONTRA as [? [CONTRA ?]].
              rewrite CONTRA in GETCALL.
              by discriminate.
            + discriminate.
        }
        { unfold rules.handler.
          destruct (decode_instr v) eqn:INST.
          + destruct i eqn:OP;
            try (unfold bind in CMVEC;
              try match goal with
                      [H: match get mem ?Addr with _ => _ end = _ |- _] =>
                      destruct (get mem Addr)
            end;
              inv CMVEC;
              rewrite op_to_wordK;
              try rewrite rules.decodeK;
              rewrite DEC; reflexivity).
          + discriminate.
        }
      * discriminate.
Qed.

Lemma no_user_access_implies_halt sst cst cmvec :
  in_user cst = true ->
  refine_state sst cst ->
  build_mvec stable sst = None ->
  build_cmvec mt cst = Some cmvec ->
  khandler cmvec = None. 
Proof.
  intros USER REF MVEC CMVEC.
  destruct REF as [REF ?].
  destruct REF as [REF | CONTRA].
  - eauto using no_user_access_implies_halt_aux.
  - destruct CONTRA as [? [? [? [? KEXEC]]]].
    apply restricted_exec_snd in KEXEC.
    eapply @in_user_in_kernel in USER.
    by congruence.
Qed.

(*Case 3*)

Lemma concrete_stuck cst :
  build_cmvec mt cst = None ->
  ~exists cst', Concrete.step _ masks cst cst'.
Proof.
  intros CMVEC (cst' & STEP).
  destruct cst as [mem reg cache [pc tpc] epc].
  inversion STEP; inversion ST;
  unfold build_cmvec in CMVEC;
  subst;
  simpl in CMVEC;
  repeat (match goal with
    | [H: ?Expr = _, H' : match ?Expr with _ => _ end = _ |- _] =>
      rewrite H in H'
          end);
  try discriminate.
  rewrite REG1 in CMVEC.
  simpl in CMVEC. rewrite M1 in CMVEC. simpl in CMVEC. discriminate.
  rewrite REG1 in CMVEC. simpl in CMVEC. rewrite M1 in CMVEC.
  simpl in CMVEC. discriminate.
Qed.


(*Move to refinement_common?*)
(*Again rough statement, subject to change*)
Lemma fault_steps_at_kernel_aux ast cst cst' cmvec :
  refinement_common.refine_state ki stable ast cst ->
  Concrete.step _ masks cst cst' ->
  build_cmvec mt cst = Some cmvec ->
  khandler cmvec = None ->
  exists cmem',
  Concrete.store_mvec ops (Concrete.mem cst) cmvec = Some cmem' /\
  cst' = Concrete.mkState cmem'
                          (Concrete.regs cst)
                          (Concrete.cache cst)
                          (Concrete.fault_handler_start _ (t := mt))@Concrete.TKernel
                          (Concrete.pc cst).
Proof.
  intros REF CSTEP CMVEC KHANDLER.
  destruct REF as [smem sreg int cmem creg cache epc pc tpc
                         ASI CSI REFM REFR CACHE MVEC WF KI].
  inversion CSTEP; subst; inversion ST; unfold mvec in NEXT; subst; clear ST;
      repeat (
        match goal with
          | [H: Concrete.next_state_pc _ _ _ _ _ = _ |- _] =>
            unfold Concrete.next_state_pc in H
          | [H: Concrete.next_state_reg _ _ _ _ _ _ = _ |- _] =>
            unfold Concrete.next_state_reg in H
          | [H: Concrete.next_state_reg_and_pc _ _ _ _ _ _ _= _ |- _] =>
            unfold Concrete.next_state_reg_and_pc in H
          | [H: Concrete.next_state _ _ _ _ _ = Some _ |- _] =>
            unfold Concrete.next_state in H; simpl in H
        end);
      match goal with
        | [H: match Concrete.cache_lookup ops ?Cache masks ?Mvec with _ => _ end = _ |- _] =>
          destruct (Concrete.cache_lookup ops Cache masks Mvec) eqn:LOOKUP
      end;
  try match goal with
        | [H:Concrete.cache_lookup _ ?Cache _ ?Mvec = Some ?R |- _] =>
           (*lookup succeeds*)
          specialize (CACHE Mvec R);
            destruct CACHE as [? [? ?]];
            auto
        | [H:Concrete.miss_state ops ?ST1 ?ST2 = _ |- _] =>
          unfold Concrete.miss_state in H (*lookup fails*)
      end;
  try match goal with (*to discharge premise to cache correctness*)
          | [|- rules.word_lift _ _ = true] =>
            unfold rules.word_lift, rules.is_user; simpl;
            rewrite rules.decodeK; reflexivity
      end;
  try match goal with (*in case of a miss*)
        | [H: match Concrete.store_mvec ops ?ST1 ?ST2 with _ => _ end = _ |- _] =>
          destruct (Concrete.store_mvec ops ST1 ST2) eqn:?;
            [idtac | discriminate]
      end;
    unfold build_cmvec in CMVEC;
    repeat  match goal with
             |[H: match ?Expr with _ => _ end = _, H1:?Expr = _ |- _] =>
              rewrite H1 in H
            end;
      repeat match goal with
                |[H1:TotalMaps.get reg ?R = _ |- _] =>
                 rewrite H1 in CMVEC
              end; simpl in NEXT;
    unfold khandler in KHANDLER;
    try rewrite -> REG in *;
    try rewrite -> OLD in *;
    try rewrite -> REG1 in *;
    try rewrite -> REG2 in *;
    simpl in CMVEC;
    try rewrite ->  M1 in *;
    inv CMVEC; inv NEXT;

    try match goal with
            | [H: rules.handler _ ?Mvec = Some _, H1: rules.handler _ ?Mvec = None |- _] =>
              rewrite H in H1; discriminate
          end;
    eexists; split; eauto.
Qed.

Lemma fault_steps_at_kernel ast cst cst' cmvec :
  in_user cst = true ->
  refine_state ast cst ->
  Concrete.step _ masks cst cst' ->
  build_cmvec mt cst = Some cmvec ->
  khandler cmvec = None ->
  exists cmem',
  Concrete.store_mvec ops (Concrete.mem cst) cmvec = Some cmem' /\
  cst' = Concrete.mkState cmem'
                          (Concrete.regs cst)
                          (Concrete.cache cst)
                          (Concrete.fault_handler_start _ (t := mt))@Concrete.TKernel
                          (Concrete.pc cst).
Proof.
  intros USER REF STEP MVEC HANDLER.
  destruct REF as [REF ?].
  destruct REF as [UREF | KREF].
  - eauto using fault_steps_at_kernel_aux.
  - destruct KREF as [? [? [? [? KEXEC]]]].
    apply restricted_exec_snd in KEXEC.
    apply in_user_in_kernel in USER.
    by congruence.
Qed.

Lemma refine_traces_kexec axs cxs cst cst' :
  refine_traces cfi_refinementSC axs (cst :: cxs) ->
  in_kernel cst = true ->
  In cst' cxs ->
  in_kernel cst' \/ exists cst'', 
                      in_user cst'' = true /\
                      exec (Concrete.step ops masks) cst cst''.
Proof.
  intros RTRACE KERNEL IN.
  gdep cst. gdep axs.
  induction cxs; intros.
  - destruct IN.
  - inversion RTRACE
        as [? ? REF' | ? ? ? ? ? STEP CHECK REF REF' RTRACE' 
            | ? ? ? ? ? ? STEP ASTEP REF REF' RTRACE' 
            | ? ? ? ? ? ? NSTEP STEPA CSTEPA REF REF' RTRACE']; 
    subst; simpl in *.
    { (*non-visible step*)
      destruct IN as [? | IN]; subst.
      + destruct (in_user cst') eqn:USER.
        * right. exists cst'. split; auto.
          econstructor(eauto).
        * destruct REF as [WREF INV]; clear INV. 
          destruct WREF as [CONTRA | KREF].
          { apply (@refine_state_in_user mt ops sym_params e ki stable ast cst) in CONTRA.
            apply (@in_user_in_kernel mt ops sym_params e cst) in CONTRA.
            congruence.
          }
          { destruct KREF as [cst0 [kst [KREF [CSTEP KEXEC]]]].
            assert (KERNEL' := kernel_step KREF CSTEP KEXEC STEP KERNEL USER).
            left. assumption.
          }
      + destruct (in_user a) eqn:USER.
        * right. exists a; split; auto.
          econstructor(eauto).
        * destruct REF as [WREF INV]; clear INV. 
          destruct WREF as [CONTRA | KREF].
          { apply (@refine_state_in_user mt ops sym_params e ki stable ast cst) in CONTRA.
            apply (@in_user_in_kernel mt ops sym_params e cst) in CONTRA.
            congruence.
          }
          { destruct KREF as [cst0 [kst [KREF [CSTEP KEXEC]]]].
            assert (KERNEL' := kernel_step KREF CSTEP KEXEC STEP KERNEL USER).
            destruct (IHcxs IN (ast :: axs0) a RTRACE' KERNEL') 
              as [KERNEL'' | [cst'' [USER'' EXEC]]].
            - left; assumption.
            - right. exists cst''.
              split; auto.
              econstructor(eauto).
          }
    }
    { (*visible step*)
      destruct IN as [? | IN]; subst.
      + destruct (in_user cst') eqn:USER.
        * right. exists cst'. split; auto.
          econstructor(eauto).
        * destruct REF as [WREF INV]; clear INV. 
          destruct WREF as [CONTRA | KREF].
          { apply (@refine_state_in_user mt ops sym_params e ki stable ast cst) in CONTRA.
            apply (@in_user_in_kernel mt ops sym_params e cst) in CONTRA.
            congruence.
          }
          { destruct KREF as [cst0 [kst [KREF [CSTEP KEXEC]]]].
            assert (KERNEL' := kernel_step KREF CSTEP KEXEC STEP KERNEL USER).
            left. assumption.
          }
      + destruct (in_user a) eqn:USER.
        * right. exists a; split; auto.
          econstructor(eauto).
        * destruct REF as [WREF INV]; clear INV. 
          destruct WREF as [CONTRA | KREF].
          { apply (@refine_state_in_user mt ops sym_params e ki stable ast cst) in CONTRA.
            apply (@in_user_in_kernel mt ops sym_params e cst) in CONTRA.
            congruence.
          }
          { destruct KREF as [cst0 [kst [KREF [CSTEP KEXEC]]]].
            assert (KERNEL' := kernel_step KREF CSTEP KEXEC STEP KERNEL USER).
            destruct (IHcxs IN (ast' :: axs0) a RTRACE' KERNEL') 
              as [KERNEL'' | [cst'' [USER'' EXEC]]].
            - left; assumption.
            - right. exists cst''.
              split; auto.
              econstructor(eauto).
          }
    }
    { (*attacker step - attacker not allowed in kernel mode*)
      inversion STEPA; subst.
      clear IHcxs RTRACE' RTRACE NSTEP CSTEPA MEQUIV REQUIV IN.
      unfold rules.word_lift, rules.is_user in INUSER.
      unfold in_kernel, Concrete.is_kernel_tag in KERNEL.
      rewrite rules.encode_kernel_tag in KERNEL. simpl in KERNEL.
      move/eqP:KERNEL=>KERNEL.
      rewrite KERNEL in INUSER.
      rewrite rules.decodeK in INUSER.
      inversion INUSER.
    } 
Qed.

Lemma attacker_up_to ast ast' cst cst' axs cxs : 
  Sym.all_attacker (ast :: ast' :: axs) ->
  Sym.all_stuck stable (ast :: ast' :: axs) ->
  Conc.step_a cst cst' /\ ~ Concrete.step ops masks cst cst' ->
  refine_traces cfi_refinementSC (ast :: ast' :: axs) (cst :: cst' :: cxs) ->
  Conc.all_attacker masks (cst :: cst' :: cxs) \/
  exists hd tl csi csj, 
    cst :: cst' :: cxs = hd ++ csi :: csj :: tl /\
    Conc.all_attacker masks (hd ++ [csi]) /\
    Concrete.step _ masks csi csj /\ check csi csj = false /\
    ((exists asi, refine_traces cfi_refinementSC [asi] (csi :: csj :: tl)
                /\ exec (@Sym.step_a mt ops valid_jmp) ast asi)
    \/ (exists asi asj atl, 
          refine_traces cfi_refinementSC (asi :: asj :: atl) (csj :: tl) /\
          Sym.all_stuck stable (asi :: asj :: atl) /\
          exec (@Sym.step_a mt ops valid_jmp) ast asi /\
          refine_state asi csi)).
Proof.
  intros ALLA ALLS CSTEP RTRACE.
  gdep ast'. gdep ast. gdep cst'. gdep cst. gdep axs.
  induction cxs as [|cst'' cxs]; simpl in *; intros.
  - inversion RTRACE
        as [? ? REF' | ? ? ? ? ? STEP CHECK REF REF' RTRACE' 
            | ? ? ? ? ? ? STEP ASTEP REF REF' RTRACE' 
            | ? ? ? ? ? ? NSTEP STEPA CSTEPA REF REF' RTRACE']; subst.
    + left.
      intros ? ? IN2;
        destruct IN2 as [[? ?] | CONTRA];
        [subst | destruct CONTRA].
      auto.
    + exfalso. simpl in *.
      assert (IN: In ast (ast :: ast' :: axs))
        by (simpl; auto).
      specialize (ALLS ast IN).
      eauto.
    + left. intros ? ? IN2.
      destruct IN2 as [[? ?] | CONTRA];
        [subst | destruct CONTRA].
      * simpl in *. auto.
  - inversion RTRACE
        as [? ? REF' | ? ? ? ? ? STEP CHECK REF REF' RTRACE' 
            | ? ? ? ? ? ? STEP ASTEP REF REF' RTRACE' 
            | ? ? ? ? ? ? NSTEP STEPA CSTEPA REF REF' RTRACE']; subst.
    + exfalso. simpl in STEP.
      destruct CSTEP as [? CONTRA].
      destruct (CONTRA STEP).
    + exfalso. simpl in *.
      assert (IN: In ast (ast :: ast' :: axs))
        by (simpl; auto).
      specialize (ALLS ast IN).
      eauto.
    + destruct axs as [|ast'' axs].
      * inversion RTRACE'
          as [? ? REF''| | | ]; subst.
       { simpl in *.
         right.
         exists [cst]; exists cxs; exists cst'; exists cst''.
         split; auto.
         split. intros ? ? IN2.
         destruct IN2 as [[? ?] | CONTRA];
           [subst | destruct CONTRA].
         split; auto.
         split; auto.
         split; auto.
         left.
         exists ast'. split; auto.
         econstructor(eauto).
       }
      * inversion RTRACE'; subst.
        { right.
          exists [cst]; exists cxs; exists cst'; exists cst''.
          split; auto.
          split.
          intros ? ? IN2; 
            destruct IN2 as [[? ?] | CONTRA]; [subst | destruct CONTRA].
          auto.
          split. assumption.
          split. assumption.
          right.  
          eexists; eexists; eexists; split; eauto.
          split.
          apply Sym.all_stuck_red in ALLS.
          by auto.
          by econstructor(eauto).
        }
        { assert (IN: In ast' (ast :: ast' :: ast'' :: axs))
            by (simpl; auto).
          specialize (ALLS ast' IN). 
          simpl in H6.
          exfalso.
          eauto.
        }
        { 
          apply Sym.all_attacker_red in ALLA.
          apply Sym.all_stuck_red in ALLS.
          assert (STEP: Conc.step_a cst' cst'' /\ ~ Concrete.step ops masks cst' cst'')
            by auto.
          specialize (IHcxs axs cst' cst'' STEP ast' ast'' ALLA ALLS RTRACE').
          destruct IHcxs as [ALLA' | IH].
          - (*all attacker*)
            left.
            intros csi csj IN2.
            destruct IN2 as [[? ?] | IN2]; subst.
            + simpl in *. auto.
            + auto.
          - destruct IH 
              as [chd [ctl [csi [csj [CLST [ALLA' [UCSTEP [CHECK IH]]]]]]]].
            destruct IH as [IH | IH].
            { destruct IH as [asi [RTRACE'' EXEC]].
              right.
              rewrite CLST.
              exists (cst :: chd); exists ctl; exists csi; exists csj.
              split; auto.
              split.
              { intros ? ? IN2.
                destruct chd.
                - destruct IN2 as [[? ?] | CONTRA];
                [subst | destruct CONTRA].
                  inv CLST.
                  assumption.
                - inv CLST.
                  destruct IN2 as [[? ?] | IN2]; subst.
                + auto.
                + apply ALLA' in IN2.
                  assumption.
              }
              { split. assumption.
                split; [assumption | idtac].
                left. exists asi. split; auto.
                econstructor(eauto).
              }
            }
            { destruct IH as [asi [asj [atl [RTRACE'' [STUCK'' [EXEC'' REF'']]]]]].
              right.
              rewrite CLST.
              exists (cst :: chd); exists ctl; exists csi; exists csj.
              split; auto.
              split.
              { intros ? ? IN2.
                destruct chd.
                - destruct IN2 as [[? ?] | CONTRA];
                [subst | destruct CONTRA].
                  inv CLST.
                  assumption.
                - inv CLST.
                  destruct IN2 as [[? ?] | IN2]; subst.
                + auto.
                + apply ALLA' in IN2.
                  assumption.
              }
              { split. assumption.
                split; [assumption | idtac].
                right. eexists; eexists; eexists; split;  eauto. 
              }
            } 
        }
Qed.

Lemma all_attacker_implies_all_user cst cst' cxs :
  Conc.all_attacker masks (cst :: cst' :: cxs) ->
  forallb in_user (cst :: cst' :: cxs).
Proof.
  intro ALLA.
  apply forallb_forall.
  intros x IN.
  gdep cst'. gdep cst.
  induction cxs; intros.
  - destruct IN as [? | IN]; subst.
    + assert (IN2 : In2 x cst' [x;cst'])
        by (simpl; auto).
      apply ALLA in IN2.
      destruct IN2 as [STEPA ?].
      inv STEPA; auto.
    + destruct IN as [? | CONTRA];
      [subst | destruct CONTRA].
      assert (IN2 : In2 cst x [cst;x])
        by (simpl; auto).
      destruct (ALLA _ _ IN2) as [STEPA ?].
      inv STEPA; auto.
  - destruct IN as [? | IN]; subst.
    + assert (IN2: In2 x cst' (x :: cst' :: a :: cxs))
        by (simpl; auto).
      destruct (ALLA _ _ IN2) as [STEPA ?].
      inv STEPA; auto.
    + apply Conc.all_attacker_red in ALLA.
      eauto.
Qed.

Lemma all_attacker_implies_all_user' cst cst' cxs :
  Conc.all_attacker masks (cst :: cxs ++ [cst']) ->
  forallb in_user (cst :: cxs ++ [cst']).
Proof.
  intro ALLA.
  apply forallb_forall.
  intros x IN. 
  gdep cst'. gdep cst.
  induction cxs; intros.
  - destruct IN as [? | IN]; subst.
    + assert (IN2 : In2 x cst' [x;cst'])
        by (simpl; auto).
      apply ALLA in IN2.
      destruct IN2 as [STEPA ?].
      inv STEPA; auto.
    + destruct IN as [? | CONTRA];
      [subst | destruct CONTRA].
      assert (IN2 : In2 cst x [cst;x])
        by (simpl; auto).
      destruct (ALLA _ _ IN2) as [STEPA ?].
      inv STEPA; auto.
  - destruct IN as [? | IN]; subst.
    + assert (IN2: In2 x a (x :: a :: cxs ++ [cst']))
        by (simpl; auto).
      simpl in ALLA. 
      apply ALLA in IN2.
      destruct IN2 as [STEPA ?].
      inv STEPA; auto.
    + simpl in ALLA.
      apply Conc.all_attacker_red in ALLA.
      specialize (IHcxs _ _ ALLA IN).
      assumption.
Qed.

Lemma user_into_kernel_wrapped sst cst cst' :
  in_user cst = true ->
  refine_state sst cst ->
  Concrete.step ops masks cst cst' ->
  in_user cst' = false -> in_kernel cst' = true.
Proof.
  intros USER REF STEP NUSER.
  destruct REF as [REF ?].
  destruct REF as [WREF | CONTRA].
  - eauto using user_into_kernel.
  - destruct CONTRA as [? [? [? [? KEXEC]]]].
    apply restricted_exec_snd in KEXEC.
    apply in_user_in_kernel in USER.
    by congruence.
Qed.

Lemma violation_implies_kexec sst cst cst' umvec sxs cxs :
  Sym.violation stable sst ->
  build_mvec stable sst = Some umvec ->
  in_user cst = true ->
  check cst cst' = false ->
  Concrete.step ops masks cst cst' ->
  refine_state sst cst ->
  refine_traces cfi_refinementSC (sst :: sxs) (cst' :: cxs) ->
  forallb in_kernel (cst' :: cxs).
Proof.
  intros VIOLATION UMVEC USER CHECK STEP REF RTRACE.
  apply andb_false_iff in CHECK.
  destruct CHECK as [CONTRA | NUSER'];
    [congruence | idtac].
  assert (UHANDLER := Sym.is_violation_implies_stop stable sst VIOLATION UMVEC).
  assert (KERNEL := user_into_kernel_wrapped USER REF STEP NUSER').
  destruct (umvec_implies_cmvec USER REF UMVEC) as [cmvec CMVEC].
  assert (KHANDLER := uhandler_chandler_stop _ UMVEC UHANDLER).
  assert (EQ := unique_cmvec USER REF UMVEC CMVEC).
  rewrite EQ in KHANDLER. clear EQ.
  destruct (fault_steps_at_kernel USER REF STEP CMVEC KHANDLER) 
    as [cmem' [STORE EQST]].
  apply forallb_forall.
  intros kst IN. 
  destruct IN as [? | IN]; [subst kst; auto | idtac].
  destruct (refine_traces_kexec kst RTRACE KERNEL IN) 
    as [KERNEL' | [cst'' [USER'' EXEC]]].
  * assumption.
  * (*the case where one user step was in the trace contradicts*)
    destruct REF as [REF ?].
    destruct REF as [REF | CONTRA].
    { destruct REF.
      destruct (in_kernel cst'') eqn:KERNEL''.
      - apply in_user_in_kernel in USER''. by congruence.
      - destruct cst as [cmemt cregt cachet [cpct ctpct] epct].
        destruct sst as [smemt sregt [spct tpct] intt].
        simpl in EQST. inversion ES.
        subst smemt sregt spct tpct intt.
        inversion EC.
        subst cmemt cregt cachet cpct epct.
        assert (KEXEC:=
                  @handler_correct_disallowed_case mt ops sym_params e ki
                                                   stable _ cmem
                                                   cmem' cmvec cregs
                                                   cache (pc@ctpct) int cst''
                                                   KINV KHANDLER STORE KERNEL'').
        rewrite <- EQST in *.
        destruct (KEXEC EXEC).
    }
    { (*refinement contradictory case*)
      destruct CONTRA as [? [? [? [? KEXEC]]]].
      apply restricted_exec_snd in KEXEC.
      apply in_user_in_kernel in USER.
        by congruence.
    }
Qed.

Lemma no_umvec_implies_kexec sst cst cst' sxs cxs :
  Sym.violation stable sst ->
  build_mvec stable sst = None ->
  in_user cst = true ->
  check cst cst' = false ->
  Concrete.step ops masks cst cst' ->
  refine_state sst cst ->
  refine_traces cfi_refinementSC (sst :: sxs) (cst' :: cxs) ->
  forallb in_kernel (cst' :: cxs).
Proof.
  intros VIOLATION UMVEC USER CHECK STEP REF RTRACES.
  destruct (build_cmvec mt cst) as [cmvec|] eqn:CMVEC.
      { (*case the cmvec for cst exists*)
        assert (KHANDLER := no_user_access_implies_halt USER REF UMVEC CMVEC).
        (*factor this in a seperate lemma*)
        destruct (fault_steps_at_kernel USER REF STEP CMVEC KHANDLER) 
        as [cmem' [STORE EQST]].
        (*kernel tail proof*)
        apply forallb_forall.
        intros kst IN.
        apply andb_false_iff in CHECK.
        destruct CHECK as [CONTRA | NUSER']; [congruence | idtac].
        assert (KERNEL := user_into_kernel_wrapped USER REF STEP NUSER').
        destruct IN as [? | IN]; [subst kst; auto | idtac].
        destruct (refine_traces_kexec kst RTRACES KERNEL IN) 
          as [KERNEL' | [cst'' [USER'' EXEC]]].
        * assumption.
        * (*the case where one user step was in the trace contradicts*)
          destruct REF as [REF ?].
            destruct REF as [REF | CONTRA].
            { destruct REF.
              destruct (in_kernel cst'') eqn:KERNEL''.
              - apply in_user_in_kernel in USER''. by congruence.
              - destruct cst as [cmemt cregt cachet [cpct ctpct] epct].
                destruct sst as [smemt sregt [spct tpct] intt].
                simpl in EQST. inversion ES.
                subst smemt sregt spct tpct intt.
                inversion EC.
                subst cmemt cregt cachet cpct epct.
                assert (KEXEC:=
                      @handler_correct_disallowed_case mt ops sym_params e ki
                                                       stable _ cmem
                                                       cmem' cmvec cregs
                                                       cache (pc@ctpct) int cst''
                                                       KINV KHANDLER STORE KERNEL'').
                rewrite <- EQST in *.
                destruct (KEXEC EXEC).
            }
            { (*refinement contradictory case*)
              destruct CONTRA as [? [? [? [? KEXEC]]]].
              apply restricted_exec_snd in KEXEC.
              apply in_user_in_kernel in USER.
              by congruence.
            }
      }
      { (*case the cmvec does not exist*)
        exfalso.
        assert (STUCK := concrete_stuck CMVEC).
        eauto. } 
Qed.

Theorem cfg_true_equiv ssi ssj csi csj :
  refine_state ssi csi ->
  refine_state ssj csj ->
  Symbolic.step stable ssi ssj -> 
  Sym.ssucc stable ssi ssj = true ->
  Concrete.step ops masks csi csj ->
  Conc.csucc valid_jmp csi csj = true.
Proof.
  intros.
  destruct H as [REF INV].
  destruct REF as [UREFI | KREFI].
  - destruct H0 as [REF' INV'].
    destruct REF' as [UREFJ | KREFJ].
    + move: (refine_state_in_user UREFI) (refine_state_in_user UREFJ) => USERI USERJ.
      destruct UREFI as [smemi sregi inti cmemi cregi cachei epci pci tpci
                         ASI CSI REFM REFR CACHE MVE C2 KI],
               UREFJ as [smemj sregj intj cmemj cregj cachej epcj pcj tpcj
                         ASJ CSJ PC' TPC' REFM' REFR' C3 C5 C6 C7].
      assert (NKERNEL : in_kernel csi || in_kernel csj = false).
      { apply (@in_user_in_kernel mt ops sym_params e) in USERI.
        apply (@in_user_in_kernel mt ops sym_params e) in USERJ.
        apply orb_false_iff. split; subst; auto.
      }
      unfold Conc.csucc.
      rewrite NKERNEL CSI CSJ /=.
      unfold Sym.ssucc in H2.
      rewrite ASI ASJ /= in H2.
      destruct (get smemi pci) as [[v tg]|] eqn:GET.
      * rewrite GET in H2. specialize (REFM pci v tg).
        apply REFM in GET.
        by rewrite GET /= rules.decodeK.
      * destruct (get cmemi pci) as [[v ctg]|] eqn:GET'.
        { simpl.
          subst csi csj.
          assert (CONTRA := fun CACHE GET' =>
                              valid_initial_user_instr_tags (v := v) (ti := ctg) CACHE USERI USERJ H3 GET').
          specialize (CONTRA CACHE GET').
          destruct (rules.decode ctg) as [[t | | ]|] eqn:DEC; try solve [inversion CONTRA].
          apply rules.encodeK in DEC.
          rewrite <- DEC in GET'.
          simpl in GET'. apply REFM in GET'. subst.
          rewrite GET' in GET. discriminate.
        }
        { inversion H3;
          inv ST; simpl in *; try congruence.
        }
    + destruct KREFJ as [? [? [? [? KEXEC]]]].
      apply restricted_exec_snd in KEXEC.
      unfold Conc.csucc. rewrite KEXEC.
      simpl. rewrite orb_true_r. reflexivity.
  - destruct KREFI as [? [? [? [? KEXEC]]]].
    apply restricted_exec_snd in KEXEC.
    unfold Conc.csucc. rewrite KEXEC.
    by reflexivity.
Qed.

Theorem cfg_false_equiv ssi ssj csi csj :
  refine_state ssi csi ->
  refine_state ssj csj ->
  Sym.ssucc stable ssi ssj = false ->
  check csi csj = true ->
  Concrete.step ops masks csi csj ->
  Conc.csucc valid_jmp csi csj = false.
Proof.
  intros.
  destruct H as [REF INV], H0 as [REF' INV']. clear INV INV'.
  unfold check in H2.
  apply andb_true_iff in H2.
  destruct H2 as [USER USER'].
  destruct REF as [REF | CONTRA].
  - destruct REF' as [REF' | CONTRA'].
    + apply in_user_in_kernel in USER.
      apply in_user_in_kernel in USER'.
      unfold Conc.csucc. rewrite USER USER'.
      simpl.
      move: (refine_state_in_user REF) (refine_state_in_user REF') => USERT USERT'.
      destruct REF as [smem sreg int cmem creg cache epc pc tpc
                       ASI CSI REFM REFR CACHE MVEC C2 KI],
               REF' as [smem' sreg' int' cmem' creg' cache' epc' pc' tpc'
                        ASJ CSJ REFM' REFR' C3 C5 C6 C7].
      simpl. subst.
      unfold Sym.ssucc in H1.
      simpl in H1.
      destruct (get smem pc) eqn:GET.
      { destruct a as [v utg].
        destruct utg.
        - rewrite GET in H1.
          apply REFM in GET.
          rewrite GET.
          simpl.
          rewrite rules.decodeK.
          destruct (decode_instr v).
          + (*is instruction*)
            destruct i; trivial.
          + trivial.
        - apply REFM in GET. rewrite GET.
          simpl. rewrite rules.decodeK. reflexivity.
      }
      { simpl. destruct (get cmem pc) as [[v ctg]|] eqn:GET'; trivial. simpl.
        destruct (rules.decode ctg) as [[t | | ]| ] eqn:DECTG; trivial.
        apply rules.encodeK in DECTG.
        rewrite <- DECTG in GET'.
        apply REFM in GET'.
        rewrite GET in GET'; discriminate.
      }
    + destruct CONTRA' as [? [? [? [? KEXEC]]]].
      apply restricted_exec_snd in KEXEC.
      apply in_user_in_kernel in USER'. rewrite KEXEC in USER'.
      discriminate.
  - destruct CONTRA as [? [? [? [? KEXEC]]]].
      apply restricted_exec_snd in KEXEC.
      apply in_user_in_kernel in USER. rewrite KEXEC in USER.
      discriminate.
Qed.

Require Import Classical.
Import ListNotations.

Open Scope list_scope.
Close Scope seq_scope.

Program Instance cfi_refinementAS_specs :
  machine_refinement_specs cfi_refinementSC.
Next Obligation. (*step or no step*)
  by apply classic.
Qed.
Next Obligation. (*initial states*)
  unfold Conc.cinitial in H.
  destruct H as [ast [INIT REF]].
  eexists; split; [eassumption | split].
  - left; assumption.
  - destruct INIT as [? INV]; by assumption.
Qed.
Next Obligation.
  unfold check in H1.
  apply andb_false_iff in H1.
  destruct H1 as [CONTRA | NUSER].
  - destruct H as [REF INV].
    move: REF => [/(@refine_state_in_user _) INUSER | REF].
    + unfold in_user in CONTRA. rewrite INUSER in CONTRA.
        by discriminate.
    + destruct REF as [? [? [? [? KEXEC]]]].
      apply restricted_exec_snd in KEXEC.
      unfold Conc.csucc. rewrite KEXEC.
      by reflexivity.
  - destruct H as [REF INV].
    destruct REF as [REF | REF].
    + assert (KERNEL' := user_into_kernel REF H0 NUSER).
      unfold Conc.csucc. rewrite KERNEL'.
      rewrite orb_true_r. reflexivity.
    + destruct REF as [? [? [? [? KEXEC]]]].
      apply restricted_exec_snd in KEXEC.
      unfold Conc.csucc. rewrite KEXEC.
      by reflexivity.
Qed.
Next Obligation. (*symbolic-concrete cfg relation*)
  destruct (Sym.ssucc stable asi asj) eqn:SUCC.
  - eauto using cfg_true_equiv.
  - eauto using cfg_false_equiv.
Qed.
Next Obligation. (*symbolic no attacker on violation*)
  destruct H as [? INV].
  eauto using attacker_no_v.
Qed.
Next Obligation. (*symbolic stopping implies concrete stopping*)
Proof.
  rename H into CHECK.
  rename H0 into SUCC.
  rename H1 into SSTEP.
  rename H2 into REFI.
  rename H3 into RTRACES.
  rename H4 into SSTOP.
  unfold Sym.stopping in SSTOP.
  unfold Conc.stopping.
  unfold check in CHECK.
  apply andb_true_iff in CHECK.
  destruct CHECK as [USERI USERJ].
  destruct REFI as [WREFI INVI].
  inversion RTRACES
    as [? ? REF' | ? ? ? ? ? STEP CHECK REFJ REF' RTRACE' 
        | ? ? ? ? ? ? STEP ASTEP REFJ REF' RTRACE' 
        | ? ? ? ? ? ? NSTEP STEPA SSTEPA REF REF' RTRACE'];
    subst; simpl in *.
  - (*case trace is a singleton*)
    left.
    split; [intros ? ? IN2; destruct IN2 | idtac].
    unfold Conc.in_user.
    unfold in_user in USERJ.
    apply andb_true_iff. auto.
  - (*case an invisible step is taken*)
    destruct (Sym.succ_false_implies_violation INVI SUCC SSTEP) 
      as [CONTRA | VIOLATION]; first done.
    right.
    exists [csj]; exists (cst' :: cxs0).
    split; auto.
    split.
    intros ? ? CONTRA; destruct CONTRA.
    split.
    apply forallb_forall. intros ? IN. 
    destruct IN as [? | CONTRA];
      [subst | destruct CONTRA].
      by auto.
    destruct (build_mvec stable asj) as [umvec|] eqn:UMVEC.
    + (*case the umvec for asj exists*)
        by eauto using violation_implies_kexec.
    + (*case where the umvec for asj does not exist*)
        by eauto using no_umvec_implies_kexec.
  - (*case of normal steps*)
    exfalso.
    destruct SSTOP as [? ALLS].
    assert (IN: In asj (asj :: ast' :: axs0))
      by (simpl; auto).
    apply ALLS in IN.
    by eauto.
  - (*case of attacker steps*)
     destruct (Sym.succ_false_implies_violation INVI SUCC SSTEP) 
      as [CONTRA | VIOLATION]; first done.
     destruct SSTOP as [ALLA ALLS].
     assert (STEPA' : Conc.step_a csj cst' /\ ~ Concrete.step ops masks csj cst')
       by auto.
     clear STEPA NSTEP.
     destruct (attacker_up_to ALLA ALLS STEPA' RTRACES) as [ALLA' | IH].
     + left. split. by assumption.
       apply all_attacker_implies_all_user in ALLA'. by assumption.
     + (*inductive cases*)
       destruct IH 
         as [chd [ctl [csi' [csj' [CLST [ALLA' [CSTEP [CHECK IH']]]]]]]].
       clear RTRACES RTRACE'.
       destruct IH' as [[asj' [RTRACE AEXEC]]| [asi' [asj' [atl RTRACE]]]].
       { (*non-contradictory case, we took some attacker steps at first*)
         assert (VIOLATION' := Sym.violation_preserved_by_exec_a _ VIOLATION AEXEC).
         clear VIOLATION.
         right.
         rewrite CLST.
         exists (chd++[csi']); exists (csj'::ctl).
         split. rewrite <- app_assoc. by reflexivity.
         split. by assumption.
         split. 
         { apply forallb_forall.
           destruct chd.
           - intros ? IN. 
             destruct IN as [? | IN]; subst.
             + inv CLST.
               by auto.
             + destruct IN.
           - intros x IN.
             apply all_attacker_implies_all_user' in ALLA'.
             assert (ALLU: forall x, In x ((s :: chd) ++ [csi']) -> in_user x)
               by (apply forallb_forall; auto).
             specialize (ALLU _ IN). by auto.
         }
         { inversion RTRACE as [| ? ? ? ? ? STEP' CHECK' REFI' REFJ' RTRACE' | |]; 
           subst.
           assert (USERI' : in_user csi' = true).
           { destruct chd.
             - inv CLST.
                 by assumption.
             - apply all_attacker_implies_all_user' in ALLA'.
               assert (IN: In csi' (s :: chd ++ [csi']))
                 by (eauto using list_utils.in_last).
               assert (ALLU: forall x, In x ((s :: chd) ++ [csi']) -> in_user x)
               by (apply forallb_forall; auto).
             specialize (ALLU _ IN). by auto.
           }
           destruct (build_mvec stable asj') as [umvec|] eqn:UMVEC.
           - (*case the umvec exists*)
             eauto using violation_implies_kexec.
           - (*case the umvec does not exist*)
             eauto using no_umvec_implies_kexec.
         }
       }
       { (*contradictory case, mixed attacker steps and unchecked ones*)
         exfalso.
         destruct RTRACE as [RTRACE [ALLS' [AEXEC REFN]]].
         destruct (refine_traces_astep RTRACE) 
           as [csn [csn' [IN2 [SSTEPN | [SSTEPAN STEPAN]]]]].
         * assert (IN: In asi' (asi' :: asj' :: atl))
             by (simpl; auto).
           apply ALLS' in IN. by eauto.
           assert (VIOLATION' := Sym.violation_preserved_by_exec_a _ VIOLATION AEXEC).
           clear VIOLATION.
           assert (USERI' : in_user csi' = true).
           { destruct chd.
             - inv CLST.
               by auto.
             - apply all_attacker_implies_all_user' in ALLA'.
               assert (ALLU : forall x, In x (s :: chd ++ [csi']) -> 
                                        in_user x = true)
                 by (apply forallb_forall; auto).
               assert (IN: In csi' (s :: chd ++ [csi']))
                 by (eauto using list_utils.in_last).
               by auto.
           }
           assert (USERN: in_user csn = true)
             by (inv STEPAN; auto).
           destruct ctl; [by inversion RTRACE |idtac].
           destruct (build_mvec stable asi') as [umvec|] eqn:UMVEC.
            - (*case the umvec exists*)
             assert (KERNEL := violation_implies_kexec VIOLATION' UMVEC USERI' 
                                                       CHECK CSTEP REFN RTRACE).
             apply In2_implies_In in IN2.
             assert (KERNEL' : forall x, In x (csj' :: s :: ctl) -> in_kernel x)
               by (apply forallb_forall; auto).
             apply KERNEL' in IN2.
             apply in_user_in_kernel in USERN.
             rewrite IN2 in USERN.
             by discriminate.
           - (*case the umvec does not exist*)
             assert (KERNEL := no_umvec_implies_kexec VIOLATION' UMVEC USERI' 
                                                       CHECK CSTEP REFN RTRACE).
             apply In2_implies_In in IN2.
             assert (KERNEL' : forall x, In x (csj' :: s :: ctl) -> in_kernel x)
               by (apply forallb_forall; auto).
             apply KERNEL' in IN2.
             apply in_user_in_kernel in USERN.
             rewrite IN2 in USERN.
             by discriminate.
       }
Qed.

End Refinement.
