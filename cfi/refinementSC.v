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

(* Definition refine_user_state (sst : Symbolic.state mt) (cst : Concrete.state mt) := *)
(*   refinement_common.refine_state ki stable sst cst. *)

(* Definition refine_kernel_state (st : Symbolic.state mt) (kst : Concrete.state mt) := *)
(*   refinement_common.in_kernel kst = true /\ *)
(*   exists (ust : Concrete.state mt),  *)
(*     (@refinement_common.in_user mt ops sym_params cp e) ust = true /\ *)
(*     exists kst', Concrete.step _ masks ust kst' /\  *)
(*                 restricted_exec (fun s s' => Concrete.step _ masks s s')  *)
(*                                 (fun s => refinement_common.in_kernel s = true)  *)
(*                                 kst' kst /\ *)
(*                 refine_user_state st ust. *)

Definition refine_state (sst : @Symbolic.state mt sym_params) (cst : Concrete.state mt) :=
  @refine_state_weak mt ops sym_params cp e ki stable sst cst.

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
          as [a a' v0 v'' ut ut' EQ1 EQ2 SEQUIV| a a' ut ut' CONTRA ? ? |a a' CONTRA]; subst.
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
        * apply rules.encode_inj in CONTRA.
          inversion CONTRA.
        * simpl in CONTRA. apply rules.encode_inj in CONTRA.
          inversion CONTRA.
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
          as [a a' v0 v'' ? ? EQ1 EQ2 SEQUIV| a a' ? ? ? CONTRA ? |a a' ? CONTRA];
                subst.
               { inversion EQ1; subst.
                 apply REF in CGET. rewrite SGET in CGET; discriminate. }
               { simpl in CONTRA. apply rules.encode_inj in CONTRA.
                 inversion CONTRA. }
               { simpl in CONTRA. apply rules.encode_inj in CONTRA.
                 inversion CONTRA. }
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
        as [a a' v0 v'' ut ut' EQ1 EQ2 SEQUIV| a a' ut ut' CONTRA ? ? |a a' CONTRA]; subst.
      * inv EQ2.
        unfold creg_to_sreg, is_user, rules.word_lift, coerce, rules.is_user.
        simpl. rewrite rules.decodeK.
        inv EQ1.
        apply rules.encode_inj in H1. inv H1.
        assumption.
      * apply rules.encode_inj in CONTRA.
          inversion CONTRA.
      * simpl in CONTRA. apply rules.encode_inj in CONTRA.
          inversion CONTRA.
    - rewrite MapTP.map_correctness.
      destruct (TotalMaps.get creg' n) eqn:CGET'.
      destruct (TotalMaps.get creg n) eqn:CGET.
      inversion EQUIV 
        as [a a' v0 v'' ? ? EQ1 EQ2 SEQUIV| a a' ? ? EQ1 EQ2 EQ3 |a a' EQ1 EQ2 EQ3];
        subst.
       + inv EQ1.
         apply REF in CGET.
         rewrite CGET in SGET. discriminate.
       + inv EQ3.
         unfold creg_to_sreg, is_user, rules.word_lift, coerce.
         rewrite EQ1. rewrite rules.decodeK. simpl.
         constructor.
       + inv EQ3.
         unfold creg_to_sreg, is_user, rules.word_lift, coerce.
         rewrite EQ1. rewrite rules.decodeK. simpl.
         constructor.
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
        as [a0 a' v0 v'' ? ? EQ1 EQ2 SEQUIV | a0 a' ? ? EQ1 EQ2 EQ3 |a0 a' EQ1 EQ2 EQ3];
    subst.
    + inversion EQ1; subst.
      rewrite rules.encode_kernel_tag in H1.
      apply rules.encode_inj in H1.
      discriminate.
    + simpl in EQ1. rewrite rules.encode_kernel_tag in EQ1.
      apply rules.encode_inj in EQ1. discriminate.
    + eexists; reflexivity.
  - destruct MEQUIV.
Qed.
    
Lemma ra_in_user_preserved_by_equiv 
      (reg reg' : Concrete.registers mt) :
  @refinement_common.ra_in_user mt ops sym_params cp e reg ->
  Conc.reg_equiv reg reg' ->
  @refinement_common.ra_in_user mt ops sym_params cp e reg'.
Proof.
  intros INV REQUIV.
  unfold refinement_common.ra_in_user, rules.word_lift.
  destruct (TotalMaps.get reg' ra) eqn:GET'.
  unfold Conc.reg_equiv in REQUIV.
  specialize (REQUIV ra).
  inversion REQUIV 
        as [a0 a' v0 v'' ? ? EQ1 EQ2 SEQUIV | a0 a' ? ? EQ1 EQ2 EQ3 |a0 a' EQ1 EQ2 EQ3];
    subst.
  - rewrite GET' in EQ2.
    inv EQ2.
    simpl. rewrite rules.decodeK.
    simpl. constructor.
  - unfold refinement_common.ra_in_user in INV.
    unfold rules.word_lift in INV. 
    rewrite EQ1 in INV.
    rewrite rules.decodeK in INV. inversion INV.
  - unfold refinement_common.ra_in_user, rules.word_lift in INV.
    rewrite EQ1 in INV.
    rewrite rules.decodeK in INV. inversion INV.
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
        as [a0 a' v0 v'' ? ? EQ1 EQ2 SEQUIV | a0 a' ? ? EQ1 EQ2 EQ3 |a0 a' EQ1 EQ2 EQ3];
          subst.
        * inv EQ1.
          move/eqP/rules.encode_inj: SCALL => CONTRA.
          inversion CONTRA.
        * simpl in *. inv EQ3.
          apply rules.encode_inj in H1. inv H1.
          assumption.
        * simpl in *. inv EQ3.
          move/eqP/rules.encode_inj: SCALL => CONTRA.
          inversion CONTRA.
      + destruct MEQUIV.
    - discriminate.
  }
  { intro CALL.
    destruct (get mem' addr) eqn:GET'.
    - destruct a as [v' ctg'].
      destruct (get mem addr) eqn:GET.
      + destruct a as [v ctg].
        inversion MEQUIV 
        as [a0 a' v0 v'' ? ? EQ1 EQ2 SEQUIV | a0 a' ? ? EQ1 EQ2 EQ3 |a0 a' EQ1 EQ2 EQ3];
          subst.
        * inv EQ2.
          move/eqP/rules.encode_inj: CALL => CONTRA.
          inversion CONTRA.
        * simpl in *. inv EQ3.
          apply rules.encode_inj in H1. inv H1.
          apply INV in CALL. assumption.
        * simpl in *. inv EQ3.
          move/eqP/rules.encode_inj: CALL => CONTRA.
          inversion CONTRA.
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
Hint Resolve ra_in_user_preserved_by_equiv.
Hint Resolve wf_entry_points_preserved_by_equiv.

Theorem backwards_simulation_attacker sst cst cst' :
  refine_state sst cst ->
  Conc.step_a valid_jmp cst cst' ->
  exists sst',
    Sym.step_a stable sst sst' /\
    refine_state sst' cst'.
Proof. 
  intros REF STEP.
  inversion STEP; subst.
  destruct sst as [smem sreg [spc stpc] int].
  unfold refine_state in REF.
  destruct REF as [REF | CONTRA].
  - unfold refinement_common.refine_state in REF.
    destruct REF as [? [PCV [PCT [REFM [REFR [? [? [? [WFENTRY ?]]]]]]]]];
    unfold Conc.no_violation in NOV.
    destruct NOV as [NOV NOVSYS].
    apply REFM in FETCH.
    destruct (rules.decode tpc) eqn:DECODE.
    + destruct t.
      * subst.
        destruct (mem_refinement_equiv REFM MEQUIV) as [smem' [REFM' SMEQUIV]].
        destruct (reg_refinement_equiv REFR REQUIV) as [sreg' [REFR' SREQUIV]].
        eexists; split. 
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
            move/eqP/rules.encode_inj: SCALL => SCALL.
            inversion SCALL.
          }
        }
        { left.
          unfold refinement_common.refine_state.
          (*need to prove invariants are preserved by attacker/equiv*)
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

(* Preservation related stuff, probably move to other file*)

Definition in_user := @in_user mt ops sym_params cp e.

Definition visible cst cst' := 
  in_user cst && in_user cst'.

Definition smachine := Sym.symbolic_cfi_machine stable.
Definition cmachine := Conc.concrete_cfi_machine valid_jmp masks.

Context {kcc : kernel_code_correctness ki stable}. (*should this go to the top?*)

Program Instance cfi_refinementSC  : 
  (machine_refinement smachine cmachine) := {
    refine_state st st' := refine_state st st';

    visible st st' := visible st st'
}.
Next Obligation.
Proof.
  unfold refine_state in REF.
  destruct REF as [UREF | KREF].
  - split.
    { (*Visible steps*)
      intro VIS.
      unfold visible in VIS.
      apply andb_true_iff in VIS.
      destruct VIS as [VIS VIS'].
      assert (HIT: @hit_step mt ops sym_params cp e cst cst')
        by (constructor; auto).
      destruct (hit_simulation UREF HIT) as [sst' [SSTEP REF']].
      unfold refine_state, refine_state_weak.
      eexists; split; eauto.
    }
    { (*cst' invisible*)
      intro INVIS.
      apply andb_false_iff in INVIS.
      destruct INVIS as [CONTRA | INVIS].
      - unfold refinement_common.refine_state in UREF.
        destruct UREF as [USER ?].
        unfold in_user in CONTRA.
        rewrite USER in CONTRA. discriminate.
      - (*user to not user step*)
        right. exists cst; exists cst'.
        repeat (split; auto).
        unfold kernel_exec.
        destruct (user_into_kernel UREF STEP INVIS).
        eapply re_refl; eauto.
    }
  - split.
    { 
      intro VIS.
      apply andb_true_iff in VIS.
      destruct VIS as [VIS VIS'].
      destruct KREF as [ust [kst [UREF [UKSTEP KEXEC]]]].
      unfold kernel_exec in KEXEC.
      apply restricted_exec_snd in KEXEC.
      unfold in_user in VIS.
      apply (@in_user_in_kernel mt ops sym_params cp e) in VIS.
      rewrite VIS in KEXEC. discriminate.
    }
    { intros INVIS. apply andb_false_iff in INVIS.
      destruct KREF as [ust [kst [UREF [UKSTEP KEXEC]]]].
      assert (INKERNEL := restricted_exec_snd KEXEC). simpl in INKERNEL.
      clear INVIS.
      destruct (in_user cst') eqn:INUSER.
      - unfold refine_state, refine_state_weak.
        destruct ast as [mem regs [pc tpc] int].
        destruct (Symbolic.get_syscall stable pc) eqn:GETCALL.
        - destruct (Symbolic.run_syscall s (Symbolic.State mem regs pc@tpc int)) eqn:RUNCALL.
          (*case system call is allowed*)
          assert (INUSERUST: @refinement_common.in_user mt ops sym_params cp e ust = true).
            by (destruct UREF; assumption).
          assert (KUEXEC: kernel_user_exec kst cst').
          { econstructor; eauto. apply (@in_user_in_kernel mt ops sym_params cp e).
            unfold in_user in INUSER.  assumption. }
          assert (UKU1: @user_kernel_user_step mt ops sym_params cp e ust cst').
            by (econstructor; eauto).
          destruct ust as [cmem cregs cache [cpc ctpc] epc].
          destruct UREF as [USTUSER [? [TPC [REFM [REFR [CACHE [MVEC [RA [WF KI]]]]]]]]].
          destruct s0 as [mem0 regs0 [pc0 tpc0] int0]. subst.
          destruct (syscalls_correct_allowed_case cpc tpc int epc KI REFM REFR CACHE MVEC GETCALL RUNCALL)
            as [cmem' [creg' [cache' [epc' [UKU2 [REFM' [REFR' [CACHE' [MVEC' [RA' [WF' KI']]]]]]]]]]].
          left. 
          destruct (rules.decode ctpc) eqn:DECODE.
          - destruct t; try contradiction. subst.
            apply rules.encodeK in DECODE.
            rewrite DECODE in UKU2.
            assert (EQ := user_kernel_user_step_determ UKU1 UKU2).
            subst.
            

Arguments ki, table, amem, areg, amem', areg', apc', tpc', int', cmem, creg,
cache, sc are implicit
Arguments mt, ops, ap, cp, e, kernel_code_correctness are implicit and
maximally inserted
Argument scopes are


        (*
        

    destruct (backward.backwards_simulation REF STEP) as [CONTRA | [ast' [SSTEP]]].
    - unfold refine_state_weak in CONTRA.
      destruct CONTRA as [CONTRA | CONTRA].
      + unfold refinement_common.refine_state in CONTRA.
        destruct ast, cst'.
        destruct [
      
      
   
End Refinement.
        
  