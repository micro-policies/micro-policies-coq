Require Import Coq.Lists.List.
Require Import lib.utils.
Require Import lib.partial_maps.
Require Import lib.Coqlib.
Require Import common.common.
Require Import symbolic.symbolic.
Require Import concrete.concrete.
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
  destruct sst as [smem sreg [spc stpc] int].
  unfold refine_state in REF.
  destruct REF as [REF | CONTRA].
  - unfold refinement_common.refine_state in REF.
    destruct REF as [PCV [PCT [REFM [REFR [? [? [WFENTRY ?]]]]]]];
    unfold Conc.no_violation in NOV.
    destruct NOV as [NOV NOVSYS].
    apply REFM in FETCH.
    destruct (rules.decode tpc) eqn:DECODE.
    + destruct t.
      * subst.
        destruct (mem_refinement_equiv REFM MEQUIV) as [smem' [REFM' SMEQUIV]].
        destruct (reg_refinement_equiv REFR REQUIV) as [sreg' [REFR' SREQUIV]].
        eexists;
        split. 
        { econstructor; eauto.
          unfold Sym.no_violation.
          apply rules.encodeK in DECODE;
            subst.
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
          unfold refinement_common.refine_state.
          repeat (split; eauto).
          rewrite DECODE. reflexivity.
        }
      * destruct PCT.
      * destruct PCT.
    + destruct PCT.
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
      destruct (cache_hit_simulation _ UREF HIT) as [sst' [SSTEP REF']].
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
        destruct (user_into_kernel _ UREF STEP NUSER).
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
      assert (REFW' := kernel_simulation_strong REFW STEP VIS).
      left; split; auto.
    }
Qed.
Next Obligation.
  apply (backwards_simulation_attacker REF STEPA).
Qed.

Import ListNotations.
  
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

Require Import Classical.

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
    + assert (KERNEL' := user_into_kernel _ REF H0 NUSER).
      unfold Conc.csucc. rewrite KERNEL'.
      rewrite orb_true_r. reflexivity.
    + destruct REF as [? [? [? [? KEXEC]]]].
      apply restricted_exec_snd in KEXEC.
      unfold Conc.csucc. rewrite KEXEC.
      by reflexivity.
Qed.
Next Obligation. (*symbolic-concrete cfg relation*)
  destruct asi as [smemi sregi [spci tpci] inti] eqn:ASI,
           asj as [smemj sregj [spcj tpcj] intj] eqn:ASJ.
  destruct csi as [cmemi cregi cachei [cpci ctpci] epci] eqn:CSI,
           csj as [cmemj cregj cachej [cpcj ctpcj] epcj] eqn:CSJ.
  destruct H as [REF INV].
  destruct REF as [UREFI | KREFI].
  - destruct H0 as [REF' INV'].
    destruct REF' as [UREFJ | KREFJ].
    + move: (refine_state_in_user _ _ _ _ UREFI) (refine_state_in_user _ _ _ _ UREFJ) => USERI USERJ.
      destruct UREFI as [PC [TPC [REFM [REFR [CACHE [MVEC [C2 KI]]]]]]],
               UREFJ as [PC' [TPC' [REFM' [REFR' [C3 [C5 [C6 C7]]]]]]].
      subst spcj. subst spci.
      assert (NKERNEL : in_kernel csi || in_kernel csj = false).
      { apply (@in_user_in_kernel mt ops sym_params cp e) in USERI.
        apply (@in_user_in_kernel mt ops sym_params cp e) in USERJ.
        apply orb_false_iff. split; subst; auto.
      }
      unfold Conc.csucc.
      rewrite <- CSI. rewrite <- CSJ. rewrite NKERNEL.
      unfold Sym.ssucc in H2.
      rewrite <- ASI in H2. rewrite <- ASJ in H2.
      destruct (get (Symbolic.mem asi) (common.val (Symbolic.pc asi))) eqn:GET.
      * destruct a as [v tg].
        specialize (REFM (common.val (Symbolic.pc asi)) v tg).
        rewrite ASI in GET. simpl in GET.
        rewrite ASI in REFM. simpl in REFM. apply REFM in GET.
        rewrite CSI. simpl.
        rewrite GET. simpl.
        destruct tg.
        { (*if tagged instruction*)
          rewrite rules.decodeK.
          destruct (decode_instr v).
          - destruct i; subst; simpl; simpl in H1; trivial.
          - discriminate.
        }
        { discriminate. }
      * (*symbolic syscall case, must contradict*)
        rewrite ASI in H2. simpl in H2.
        simpl.
        destruct (get (Concrete.mem csi) (common.val (Concrete.pc csi))) eqn:GET'.
        { destruct a as [v ctg]. simpl.
          change cachei with (Concrete.cache (Concrete.mkState cmemi cregi cachei cpci@ctpci epci)) 
                in CACHE.
          rewrite CSI in GET'.
          assert (CONTRA := valid_initial_user_instr_tags CACHE USERI USERJ H3 GET').
         destruct (rules.decode ctg) eqn:DEC.
         - destruct t.
           + apply rules.encodeK in DEC.
             rewrite <- DEC in GET'.
             simpl in GET'. apply REFM in GET'. subst.
             rewrite GET' in GET. discriminate.
           + inversion CONTRA.
           + inversion CONTRA.
         - inversion CONTRA.
        }
        { rewrite CSI in GET'. simpl in GET'. inversion H3;
          inv ST; rewrite GET' in PC; discriminate.
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
      destruct ast as [smem sreg [spc tpc] int] eqn:ASI,
               ast' as [smem' sreg' [spc' tpc'] int'] eqn:ASJ.
      destruct cst as [cmem creg cache [cpc ctpc] epc] eqn:CSI,
               cst' as [cmem' creg' cache' [cpc' ctpc'] epc'] eqn:CSJ.
      move: (refine_state_in_user _ _ _ _ REF) (refine_state_in_user _ _ _ _ REF') => USERT USERT'.
      destruct REF as [PC [TPC [REFM [REFR [CACHE [MVEC [C2 KI]]]]]]],
               REF' as [PC' [TPC' [REFM' [REFR' [C3 [C5 [C6 C7]]]]]]].
      simpl. subst.
      unfold Sym.ssucc in H1.
      simpl in H1.
      destruct (get smem cpc) eqn:GET.
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
      { destruct (get cmem cpc) eqn:GET'.
        destruct a as [v ctg].
        simpl.
        destruct (rules.decode ctg) eqn:DECTG.
        - destruct t.
          + apply rules.encodeK in DECTG.
            rewrite <- DECTG in GET'. 
            apply REFM in GET'.
            rewrite GET in GET'; discriminate.
          + reflexivity.
          + reflexivity.
          + reflexivity.
        - reflexivity.
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
  unfold Sym.stopping in H0.
  destruct H0 as [sst [AXS STUCK]].
  subst.
  unfold Conc.stopping.
  induction H. 
  - unfold preservation.refine_state in H. simpl in H.
    unfold refine_state in H.
    destruct H as [[UREF | KREF] INV].
    + unfold Conc.in_user. left. exists cst.
      split; eauto using refine_state_in_user.
    + destruct KREF as [cst0 [kst [REF [CSTEP KEXEC]]]].
      (*case cst is in kernel, need to contradict it probably*)
      admit.
  - simpl in *. unfold check in H3.
Admitted.
      
End Refinement.
