Require Import Coq.Lists.List.
Require Import lib.utils.
Require Import lib.partial_maps.
Require Import lib.Coqlib.
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
  Variable M1 M2 K V1 V2 : Type.

  
  Class mappable (tm1 : total_map M1 K V1) (pm2 : partial_map M2 K V2) := {

    map : (V1 -> option V2) -> M1 -> M2;

    map_correctness: forall (f : V1 -> option V2) (m1 : M1) (k : K),
                       PartMaps.get (map f m1) k = f (TotalMaps.get m1 k)


    }.
End Mappable. 

End MapTP.

Import PartMaps.

Section Refinement.


Context {mt : machine_types}
        {ops : machine_ops mt}
        {opss : machine_ops_spec ops}

        {cp : Concrete.concrete_params mt}
        {sp : Concrete.params_spec cp}
        {e : @rules.encodable (@rules.cfi_tag_eqType mt) mt ops}

        {smemory : Type}
        {sm : partial_map smemory (word mt) (atom (word mt) (@cfi_tag mt))}
        {smems : axioms sm}

        {sregisters : Type}
        {sr : partial_map sregisters (reg mt) (atom (word mt) (@cfi_tag mt))}
        {sregs : axioms sr}

        {cm_map : Map.mappable (@Concrete.mem_class mt cp) sm}
        {cr_map : MapTP.mappable (@Concrete.reg_class mt cp) sr}.

Variable valid_jmp : word mt -> word mt -> bool.

Definition sym_params := Sym.sym_cfi valid_jmp.

Variable stable : list (@Symbolic.syscall mt sym_params).

Variable ki : (@refinement_common.kernel_invariant mt ops sym_params cp e).

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
  @refine_state_weak mt ops sym_params cp e ki stable sst cst.

Definition refine_state (sst : @Symbolic.state mt sym_params) (cst : Concrete.state mt) :=
  @refine_state_weak mt ops sym_params cp e ki stable sst cst /\
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
  exists (Map.map coerce (filter is_user cmem')).
  split.
  { (*refinement proof*)
    intros addr v tg.
    split.
    { intro CGET.
      rewrite Map.map_correctness. rewrite filter_correctness.
      rewrite CGET. simpl. 
      destruct (is_user v@(rules.encode (rules.USER (user_tag:=cfi_tag_eqType) tg))) eqn:USER.
      + simpl. unfold coerce. simpl. rewrite rules.decodeK. reflexivity.
      + unfold is_user in USER. simpl in USER.
        unfold rules.word_lift in USER.
        rewrite rules.decodeK in USER. simpl in USER. discriminate. }
    { intro SGET.
      rewrite Map.map_correctness filter_correctness in SGET.
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
    specialize (EQUIV addr).
    destruct (get smem addr) eqn:SGET.
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
        * rewrite Map.map_correctness filter_correctness.
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
        rewrite Map.map_correctness filter_correctness.
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
       * rewrite Map.map_correctness filter_correctness.
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
    destruct (get sreg n) eqn:SGET.
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
  Conc.step_a valid_jmp cst cst' ->
  exists sst',
    Sym.step_a stable sst sst' /\
    refine_state_no_inv sst' cst'.
Proof. 
  intros REF STEP.
  inversion STEP; subst.
  unfold refine_state in REF.
  destruct REF as [REF | CONTRA].
  move: tpc INUSER NOV REF STEP => tpc' INUSER NOV REF STEP.
  - destruct REF as [smem sreg int cmem cregs cache' epc' pc' tpc
                     ? ? REFM REFR ? ? WFENTRY ?].
    subst sst.
    symmetry in EC. inv EC.
    unfold Conc.no_violation in NOV.
    destruct NOV as [NOV NOVSYS].
    apply REFM in FETCH.
    subst.
    destruct (mem_refinement_equiv REFM MEQUIV) as [smem' [REFM' SMEQUIV]].
    destruct (reg_refinement_equiv REFR REQUIV) as [sreg' [REFR' SREQUIV]].
    eexists; split.
    { econstructor; eauto.
      unfold Sym.no_violation.
      split.
      { intros i0 ti src SGET STPC.
        apply REFM in SGET.
        rewrite STPC in NOV.
        destruct (NOV _ _ _ SGET erefl) as [dst [TI VALID]].
        eexists; eauto.
      }
      { intros sc SGET SGETCALL src STPC. (*we currently don't allow attacker when in syscall*)
        unfold refinement_common.wf_entry_points in WFENTRY.
        clear NOV.
        remember (Symbolic.entry_tag sc) as etg.
        specialize (WFENTRY pc etg).
        assert (SCALL: (exists sc : Symbolic.syscall mt,
                          Symbolic.get_syscall stable pc = Some sc /\
                          Symbolic.entry_tag sc = etg))
          by (eexists; eauto).
        apply WFENTRY in SCALL.
        apply REFM in FETCH. rewrite FETCH in SCALL.
        apply andb_true_iff in SCALL.
        destruct SCALL as [? SCALL].
        move/eqP/rules.encode_inj: SCALL => SCALL.
        inversion SCALL.
      }
    }
    { left.
      econstructor; eauto.
    }
  - destruct CONTRA as [? [? [? [? CONTRA]]]].
    clear FETCH NOV REQUIV MEQUIV.
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
  Conc.step_a valid_jmp cst cst' ->
  exists sst',
    Sym.step_a stable sst sst' /\
    refine_state sst' cst'.
Proof. 
  intros REF STEP.
  destruct REF as [REF INV];
  destruct (backwards_simulation_attacker_aux REF STEP) as [sst' [SSTEP REF']];
  eexists; split; [eassumption | split];
  eauto using Sym.invariants_preserved_by_step_a.
Qed.

(* Preservation related stuff, probably move to other file*)

Definition in_user := @in_user mt ops sym_params cp e.

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
      assert (HIT: @hit_step mt ops sym_params cp e cst cst')
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
      apply (@in_user_in_kernel mt ops sym_params cp e) in VIS.
      rewrite VIS in KEXEC. discriminate.
    }
    { (*and taking an invisible step*)
      intro VIS.
      assert (REFW : @refine_state_weak mt ops sym_params cp e ki stable ast cst)
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
  assert (REFW: @refine_state_weak _ _ _ _ _ ki stable ast cst).
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
                 Sym.step_a stable si sj ->
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
  rewrite FETCH in PC. inversion PC; subst.
  unfold Sym.instructions_tagged in ITG.
  specialize (ITG pc0 i0 s FETCH). simpl in ITG. subst.
  congruence.
  (*bnz case*)
  destruct (w == 0%w).
  * subst mem' reg'.
    rewrite H2 in FETCH. rewrite FETCH in PC. inversion PC; subst i.
    rewrite H2 in SUCC. rewrite FETCH in SUCC.
    rewrite INST in SUCC.
    apply orb_false_iff in SUCC. destruct SUCC.
    rewrite H2 in H. rewrite eqxx in H. discriminate.
  * subst mem' reg'.
    rewrite H2 in FETCH. rewrite FETCH in PC. inversion PC; subst i.
    rewrite H2 in SUCC. rewrite FETCH in SUCC.
    rewrite INST in SUCC.
    apply orb_false_iff in SUCC. destruct SUCC.
    rewrite H2 in H0. rewrite eqxx in H0. discriminate.
 (*jal case*)
  rewrite FETCH in PC. inversion PC; subst.
  unfold Sym.instructions_tagged in ITG.
  specialize (ITG pc0 i0 s FETCH). simpl in ITG. subst.
  congruence.
  (*syscall case*)
  rewrite GETCALL in SUCC. discriminate.
Qed.


Definition khandler := @rules.handler cfi_tag_eqType mt ops e (@Symbolic.handler mt sym_params).
Definition uhandler := @Symbolic.handler mt sym_params.

(*XXX: Move these to refinement_common*)
Lemma get_reg_no_user sreg reg r v ctg t :
  @refinement_common.refine_registers mt ops sym_params cp e sreg reg ->
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
  @refinement_common.refine_memory mt ops sym_params cp e smem mem ->
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
  @refinement_common.in_user mt ops sym_params cp e cst = true ->
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

Lemma umvec_implies_cmvec sst cst smvec :
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
        simpl. rewrite DEC.
        rewrite decodeK.
        eexists; reflexivity.
      * discriminate.
    + discriminate.
Qed.

(*not sure if useful*)    
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
(* Qed. *)
Admitted.


Lemma unique_cmvec sst cst umvec cmvec :
  @refinement_common.refine_state mt ops sym_params cp e ki stable sst cst ->
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
        rewrite GET in CMVEC. simpl in CMVEC. rewrite VAL in CMVEC.
        rewrite common.decodeK in CMVEC. inv CMVEC.
        reflexivity.
      - discriminate.
    }
    { discriminate. }
Qed.

(*Case 2*)

(*The first part (if get smem pc = Some _) works.
  The second part, should work as well however we will have to replay
  things like 3 times and it's already too slow.
  Stays as admit*)
Lemma no_user_access_implies_halt sst cst cmvec :
  refinement_common.refine_state ki stable sst cst ->
  build_mvec stable sst = None ->
  build_cmvec mt cst = Some cmvec ->
  khandler cmvec = None. 
Proof.
  (*intros REF SMVEC CMVEC.
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
        destruct (rules.decode ctg) eqn:DEC.
        destruct (get_mem_no_user pc REFM SGET GET DEC); subst.
        { simpl in CMVEC.
          destruct (decode_instr v) eqn:INST.
          - destruct i eqn:OP;
              admit. 
             (*these are all trivial (or can be solved as above but the way the handler is
               a full case analysis must be done on all parts of the mvec resulting in a
               very-very slow proof. I will leave this as admitted until we change the
               handler and proof auxiliary lemmas that reduce the load*)
          - discriminate.
        }
        { 
          unfold wf_entry_points in WF.
          destruct H as [ut TG]. subst.
          specialize (WF pc ut).
          rewrite GET in WF.
          destruct (decode_instr v) eqn:INST.
          + destruct i.
            - apply common.encodeK in INST.
              assert ((v == encode_instr (Nop mt)) && (ctg == rules.encode (rules.ENTRY ut)))
                by admit.
              apply WF in H.
              destruct H as [? [CONTRA ?]].
              rewrite CONTRA in GETCALL. discriminate.
            - simpl in CMVEC.
              rewrite INST in CMVEC.
              admit. admit. admit. admit.
              admit. admit. admit. admit.
              admit. admit. admit. admit.
              admit.
          + rewrite INST in CMVEC. discriminate.
        }
        (*case decode ctg fails*)
        admit. (*trivial*)
      * discriminate. *)
Admitted.
            
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
Lemma fault_steps_at_kernel ast cst cst' cmvec :
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
Proof. Admitted.

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
  (*
  destruct asi as [smemi sregi [spci tpci] inti] eqn:ASI,
           asj as [smemj sregj [spcj tpcj] intj] eqn:ASJ.
  destruct csi as [cmemi cregi cachei [cpci ctpci] epci] eqn:CSI,
           csj as [cmemj cregj cachej [cpcj ctpcj] epcj] eqn:CSJ.*)
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
      { apply (@in_user_in_kernel mt ops sym_params cp e) in USERI.
        apply (@in_user_in_kernel mt ops sym_params cp e) in USERJ.
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
Next Obligation. (*symbolic no attacker on violation*)
  destruct H as [? INV].
  eauto using attacker_no_v.
Qed.
Next Obligation. (*symolic violation implies concrete violation*)
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
Next Obligation. (*symbolic stopping implies concrete stopping*) 
Proof.
  unfold Sym.stopping in H4.
  unfold Conc.stopping.
  destruct H4 as [sst [AXS STUCK]].
  inv AXS.
  unfold check in H. 
  apply andb_true_iff in H.
  destruct H as [USERI USERJ].  
  destruct H2 as [WREF INV].
  destruct WREF as [REFI | CONTRA].
  {
    destruct (build_mvec stable sst) eqn:UMVEC.
    { (*case the symbolic umvec exists*)
      inversion H3 as [? ? REF' | ? ? ? ? ? STEP CHECK REF REF' RTRACE' | |]; subst; simpl in *.
      - (*case concrete trace is singleton*)
        left. eexists; eauto.
      - (*case the concrete trace is longer*)
        unfold refine_state in REF. 
        destruct REF as [WREF ?].
        destruct WREF as [REF | CONTRA].
        + destruct (umvec_implies_cmvec REF UMVEC) as [cmvec CMVEC].
          assert (UHANDLER := Sym.succ_false_handler INV H0 H1). 
          unfold Sym.option_handler in UHANDLER.
          rewrite UMVEC in UHANDLER.
          assert (KHANDLER := uhandler_chandler_stop _ UMVEC UHANDLER).
          assert (EQ := unique_cmvec REF UMVEC CMVEC).
          rewrite EQ in KHANDLER.
          destruct csj as [cmem creg cache [cpc ctpc] epc].
          destruct sst as [smem sreg [spc tpc] int].
          destruct (fault_steps_at_kernel REF STEP CMVEC KHANDLER) as [cmem' [STORE EQST]].
          simpl in EQST.
          right.
          eexists. exists (cst' :: cxs0). split. reflexivity.
          split. auto.
          apply forallb_forall. intros kst IN.
          destruct (in_kernel kst) eqn:KERNEL.
          { reflexivity. }
          { destruct REF.
            inversion ES. subst smem0 sregs0 spc tpc0 int0. clear ES.
            inversion EC. subst cmem0 cregs cache0 pc epc0. clear EC.
            assert ( EXEC:=
                       @handler_correct_disallowed_case mt ops sym_params cp e ki
                                                        stable _ cmem cmem' cmvec creg
                                                        cache (cpc@ctpc) int kst
                                                        KINV KHANDLER STORE KERNEL).
            assert (EXEC' := refine_traces_execution RTRACE' IN).
            simpl in EXEC'.
            rewrite <- EQST in EXEC.
            destruct (EXEC EXEC').
          }
        + (*csj in kernel, contradiction*)
          destruct CONTRA as [? [? [? [? KEXEC]]]].
          apply restricted_exec_snd in KEXEC.
          unfold in_user in USERJ.
          apply (@in_user_in_kernel mt ops sym_params cp e) in USERJ.
          rewrite USERJ in KEXEC. discriminate.
    }
    { (*case the symbolic umvec does not exist.*)
      destruct (build_cmvec mt csj) eqn:CMVEC.
      - (* if concrete cmvec exists, then it must be kernel mode (or at least not user)*)
        inversion H3 as [? ? REF' | ? ? ? ? ? STEP CHECK REF REF' RTRACE' | |]; subst; simpl in *.
        + (*case concrete trace is singleton*)
          left. eexists; eauto.
        + destruct REF as [WREF ?].
          destruct WREF as [REF | CONTRA].
          { (*case we get user REF for csj*)
            (*ugly copy-paste*)
            assert (KHANDLER := no_user_access_implies_halt REF UMVEC CMVEC).  
            destruct csj as [cmem creg cache [cpc ctpc] epc].
            destruct sst as [smem sreg [spc tpc] int].
            destruct (fault_steps_at_kernel REF STEP CMVEC KHANDLER) as [cmem' [STORE EQST]].
            simpl in EQST.
            right. eexists; exists (cst' :: cxs0). split; first done.
            split; first done.
            apply forallb_forall. intros kst IN.
            destruct (in_kernel kst) eqn:KERNEL; first done.
            destruct REF.
            inversion ES. subst smem0 sregs0 spc tpc0 int0. clear ES.
            inversion EC. subst cmem0 cregs cache0 pc epc0. clear EC.
            { assert ( EXEC:=
                         @handler_correct_disallowed_case mt ops sym_params cp e ki
                                                          stable _ cmem cmem' m creg
                                                          cache (cpc@ctpc) int kst
                                                          KINV KHANDLER STORE KERNEL).
              assert (EXEC' := refine_traces_execution RTRACE' IN).
              simpl in EXEC'.
              rewrite <- EQST in EXEC.
              destruct (EXEC EXEC').
            }
          }
          { (*case we get kernel ref for csj - contradiction*)
            destruct CONTRA as [? [? [? [? KEXEC]]]].
            apply restricted_exec_snd in KEXEC.
            unfold in_user in USERJ.
            apply (@in_user_in_kernel mt ops sym_params cp e) in USERJ.
            rewrite USERJ in KEXEC. discriminate.
          }
      - (*case the concrete cmvec does not exist - so both machines are stuck in one step
          this could be an extra case in our stopping predicate*)
        apply concrete_stuck in CMVEC.
        destruct cxs.
        + (*Case the trace is a singleton*)
          left; eexists; eauto.
        + (*Case there is a step, contradiction*)
          inversion H3 as [? ? REF' | ? ? ? ? ? STEP CHECK REF REF' RTRACE' | |]; subst; simpl in *.
          * assert (ESTEP : exists cst', Concrete.step ops masks csj cst')
              by (eexists; eauto).
            destruct (CMVEC ESTEP).
    }
  }
  { (*case we get a kernel ref for csi - contradiction*)
    destruct CONTRA as [? [? [? [? KEXEC]]]].
    apply restricted_exec_snd in KEXEC.
    unfold in_user in USERI.
    apply (@in_user_in_kernel mt ops sym_params cp e) in USERI.
    rewrite USERI in KEXEC. discriminate.
  }
Qed.
  
End Refinement.
