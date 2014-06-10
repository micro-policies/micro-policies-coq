Require Import Coq.Bool.Bool.
Require Import Coq.Classes.SetoidDec.
Require Import lib.utils.
Require Import lib.Coqlib.
Require Import concrete.common.
Require Import cfi.abstract.
Require Import cfi.qa.
Require Import cfi.cfi_rules.
Require Import symbolic.symbolic.
Require Coq.Vectors.Vector.

Set Implicit Arguments.

Section Refinement.

Context {mt : machine_types}
        {ops : machine_ops mt}
        {opss : machine_ops_spec ops}
        {ap : Abstract.abstract_params mt}
        {aps : Abstract.params_spec ap}
        {sp : @SymbolicCFI.sym_cfi_params mt}.

Variable valid_jmp : word mt -> word mt -> bool.

(* Instantiate the symbolic machine with the CFI stuff*)
Definition sym_params := SymbolicCFI.sym_cfi valid_jmp.

Context {sps : @Symbolic.params_spec mt sym_params}.

Variable atable : list (Abstract.syscall mt).
Variable stable : list (@Symbolic.syscall mt sym_params).

(*this should be replaced, when step_a is defined*)
Variable step_a : @Symbolic.state mt sym_params -> @Symbolic.state mt sym_params -> Prop.

Definition amachine := Abstract.abstract_cfi_machine atable valid_jmp.
Definition smachine := SymbolicCFI.symbolic_cfi_machine stable step_a.

Definition refine_dmemory (admem : Abstract.dmemory mt) (smem : @Symbolic.memory mt sym_params) :=
  forall w (x : word mt),
    Symbolic.get_mem smem w = Some x@DATA <->
    Abstract.get_dmem admem w = Some x. 

Definition refine_imemory (aimem : Abstract.imemory mt) (smem : @Symbolic.memory mt sym_params) :=
  forall w x,
    (forall id, Symbolic.get_mem smem w = Some x@(INSTR id) ->
                Abstract.get_imem aimem w = Some x) /\
    (exists id, Abstract.get_imem aimem w = Some x ->
                Symbolic.get_mem smem w = Some x@(INSTR id)).

Definition refine_registers (areg : Abstract.registers mt) (sreg : @Symbolic.registers mt sym_params) :=
  forall n (x : word mt),
    (forall ut, Symbolic.get_reg sreg n = Some x@ut ->
                Abstract.get_reg areg n = Some x) /\
    (exists ut, Abstract.get_reg areg n = Some x ->
                Symbolic.get_reg sreg n = Some x@ut).

Definition refine_syscalls (atbl : list (Abstract.syscall mt)) (stbl : list (@Symbolic.syscall mt sym_params)) :=
  forall addr,
    (forall sc, Symbolic.get_syscall stbl addr = Some sc ->
                exists sc', Abstract.get_syscall atbl addr = Some sc') /\
    (forall sc, Abstract.get_syscall atbl addr = Some sc ->
                exists sc', Symbolic.get_syscall stbl addr = Some sc').

Definition refine_normal_state (ast : Abstract.state mt) (sst : Symbolic.state mt) :=
  let '(Symbolic.State mem regs pc@tpc _) := sst in
  let '(imem, dmem, aregs, apc, b) := ast in
  b = true /\
  pc = apc /\
  refine_imemory imem mem /\
  refine_dmemory dmem mem /\
  refine_registers aregs regs /\
  refine_syscalls atable stable.

Definition refine_violation_state (ast : Abstract.state mt) (sst : Symbolic.state mt) :=
  let '(imem, dmem, aregs, apc, b) := ast in
  b = false /\
  exists ast0 sst0, 
    let '(_, _, _, apc0, b0) := ast0 in
    b0 = true /\
    Abstract.step atable valid_jmp ast0 ast /\
    Symbolic.step stable sst0 sst /\
    refine_normal_state ast0 sst0 /\
    valid_jmp apc0 apc = false.

Definition refine_state ast sst := 
  refine_normal_state ast sst \/ refine_violation_state ast sst.

Hypothesis id_hypothesis :
  forall pc (w : word mt) (mem : @Symbolic.memory mt sym_params) id, 
    Symbolic.get_mem mem pc = Some w@(INSTR (Some id)) ->
    id = pc.

Hypothesis jump_tagged :
  forall pc w smem aimem r,
    Abstract.get_imem aimem pc = Some w ->
    decode_instr w = Some (Jump _ r) ->
    refine_imemory aimem smem ->
    Symbolic.get_mem smem pc = Some w@(INSTR (Some pc)).

Hypothesis jal_tagged :
  forall pc w smem aimem r,
    Abstract.get_imem aimem pc = Some w ->
    decode_instr w = Some (Jal _ r) ->
    refine_imemory aimem smem ->
    Symbolic.get_mem smem pc = Some w@(INSTR (Some pc)).

Hypothesis jump_targets_tagged :
  forall pc i smem regs r w (ti ti' : @Symbolic.tag mt sym_params),
    Symbolic.get_mem smem pc = Some i@ti ->
    decode_instr i = Some (Jump _ r) ->
    Symbolic.get_reg regs r = Some w@ti' ->
    ti' = INSTR (Some w).


Import Vector.VectorNotations.

Lemma refine_registers_upd sreg sreg' areg r v t v' t' :
  refine_registers areg sreg ->
  Symbolic.get_reg sreg r = Some v@t ->
  Symbolic.upd_reg sreg r v'@t' = Some sreg' ->
  exists areg',
    Abstract.upd_reg areg r v' = Some areg' /\
    refine_registers areg' sreg'.
Proof.
  intros REFR GET UPD. unfold refine_registers in REFR.
  destruct (REFR r v) as [REGSA REGAS].
  apply REGSA in GET.
  assert (NEW := PartMaps.upd_defined v' GET).
  destruct NEW as [areg' UPD'].
  eexists; split; eauto.
  unfold refine_registers. intros r' v''.
  destruct (r' == r) as [EQ | NEQ]; [simpl in EQ | simpl in NEQ]; subst.
  *
    rewrite (PartMaps.get_upd_eq UPD').
    rewrite (PartMaps.get_upd_eq UPD). 
    split. 
    - intros ut H. inversion H; reflexivity.
    - exists t'. intro H1; inversion H1; auto.
  * rewrite (PartMaps.get_upd_neq NEQ UPD).
    rewrite (PartMaps.get_upd_neq NEQ UPD').
    auto.
Qed.

Lemma refine_memory_upd smem smem' amemd addr v v' :
  refine_dmemory amemd smem ->
  Symbolic.get_mem smem addr = Some v@DATA ->
  Symbolic.upd_mem smem addr v'@DATA = Some smem' ->
  exists amemd',
    Abstract.upd_dmem amemd addr v' = Some amemd' /\
    refine_dmemory amemd' smem'.
Proof.
  intros MEM GET UPD. unfold refine_dmemory in MEM.
  assert (GET': Abstract.get_dmem amemd addr = Some v) 
    by (apply MEM in GET; auto).
  destruct (PartMaps.upd_defined v' GET') as [amem' UPD'].
  do 2 eexists; eauto.
  intros addr' w'.
  destruct (addr' == addr) as [EQ | NEQ]; [simpl in EQ | simpl in NEQ]; subst.
  - rewrite (PartMaps.get_upd_eq UPD).
    rewrite (PartMaps.get_upd_eq UPD').
    split; try congruence.
  - rewrite (PartMaps.get_upd_neq NEQ UPD').
    rewrite (PartMaps.get_upd_neq NEQ UPD).
    now apply MEM.
Qed.

Lemma data_memory_upd (smem : @Symbolic.memory mt sym_params) smem' addr v v' :
  Symbolic.get_mem smem addr = Some v@DATA -> 
  Symbolic.upd_mem smem addr v'@DATA = Some smem' ->
  (forall addr' i id, 
     Symbolic.get_mem smem addr' = Some i@(INSTR id) ->
     Symbolic.get_mem smem' addr' = Some i@(INSTR id)).
Proof.
  intros GET UPD addr' i id GET'.
  destruct (addr' == addr) as [EQ | NEQ]; [simpl in EQ | simpl in NEQ]; subst.
  * rewrite GET in GET'. discriminate.
  * rewrite (PartMaps.get_upd_neq NEQ UPD);
    assumption.
Qed.

Lemma imem_upd_preservation amemi (smem : @Symbolic.memory mt sym_params) (smem' : @Symbolic.memory mt sym_params) addr v v':
  refine_imemory amemi smem ->
  Symbolic.get_mem smem addr = Some v@DATA ->
  Symbolic.upd_mem smem addr v'@DATA = Some smem' ->
  refine_imemory amemi smem'.
Proof.
  intros MEM GET UPD w x.
  destruct (MEM w x) as [MEMSA MEMAS].
  split.
  - intros id GET'.
    destruct (addr == w) as [EQ | NEQ]; [simpl in EQ | simpl in NEQ]; subst.
    * assert (CONTRA := PartMaps.get_upd_eq UPD).
      rewrite CONTRA in GET'. discriminate.
    * eapply PartMaps.get_upd_neq in UPD; eauto.
      Focus 2. apply sps.
      rewrite UPD in GET'.
      eapply MEMSA; eauto.
  - destruct MEMAS as [id' H].
    exists id'.
    intro GET'. apply H in GET'.
    destruct (addr == w) as [EQ | NEQ]; [simpl in EQ | simpl in NEQ]; subst.
    * rewrite GET in GET'. discriminate.
    * eapply PartMaps.get_upd_neq in UPD; eauto. Focus 2. apply sps.
      rewrite UPD; assumption.
Qed.

Hint Resolve imem_upd_preservation.

Ltac match_inv :=
  repeat match goal with
  | H : bind (fun x : _ => _) _ = Some _ |- _ =>
    apply bind_inv in H;
    let x := fresh x in
    let E := fresh "E" in
    destruct H as (x & H & E);
    simpl in H; simpl in E
  | H : (if ?b then _ else _) = Some _ |- _ =>
    let E := fresh "E" in
    destruct b eqn:E;
    try discriminate
  | H : match ?E with _ => _ end = _ |- _ =>
    destruct E eqn:?; try discriminate
  | H : Some _ = Some _ |- _ => inv H
  | H : ?O = Some _ |- context[bind _ ?O] => rewrite H; simpl
  | H : True |- _ => clear H
  end.

Theorem backwards_simulation_normal ast sst sst' :
  refine_normal_state ast sst ->
  Symbolic.step stable sst sst' ->
  exists ast',
    Abstract.step atable valid_jmp ast ast' /\
    refine_state ast' sst'.
Proof.
  intros REF SSTEP.
  destruct ast as [[[[imem dmem] aregs] apc] b].
  destruct b; [idtac | inversion SSTEP; subst; destruct REF; discriminate].
  inversion SSTEP; subst;
  destruct REF as [? [? [? [? ?]]]]; subst apc;
  (*unfoldings and case analysis on tags*)
  repeat (
      match goal with
        | [H: Symbolic.next_state_pc _ _ _ = _ |- _] => unfold Symbolic.next_state_pc in H
        | [H: Symbolic.next_state_reg _ _ _ _ = _ |- _] => unfold Symbolic.next_state_reg in H
        | [H: Symbolic.next_state_reg_and_pc _ _ _ _ _ = _ |- _] => 
          unfold Symbolic.next_state_reg_and_pc in H
        | [H: Symbolic.next_state _ _ _ = Some _ |- _] =>
          unfold Symbolic.next_state in H; simpl in H; match_inv
      end);
  (* switch memory updates to abstract*)
  repeat (
      match goal with
        | [H: SymbolicCFI.upd_mem ?Mem ?Addr ?V@_ = Some _, H1 : refine_dmemory _ ?Mem, 
          H2: Symbolic.get_mem ?Mem ?Addr = Some _ |- _] => 
          simpl in H; destruct (refine_memory_upd Addr V H1 H2 H) as [dmem' [? ?]]
  end);

  (*switch memory and register reads to abstract*)
  repeat  match goal with
    | [H1: refine_imemory _ _, H2: Symbolic.get_mem _ _ = Some _@(INSTR _) |- _] =>
      apply H1 in H2
    | [H1: refine_dmemory _ _, H2: Symbolic.get_mem _ _ = Some _@DATA |- _] => 
      apply H1 in H2
    | [H1: refine_registers _ _, H2: Symbolic.get_reg _ _ = Some _ |- _] => 
      apply H1 in H2
  end;
        
  repeat match goal with
    | [H: refine_registers ?Aregs ?Regs, H1: Abstract.get_reg _ ?R = Some ?Old |- _] => 
      unfold refine_registers in H; destruct (H R Old) as [RSA RAS]; destruct RAS as [x RAS'];
      apply RAS' in H1; fold (refine_registers Aregs Regs) in H
    | [H: refine_registers _ _, H1: Symbolic.get_reg ?Reg ?R = Some _,
                                    H2: SymbolicCFI.upd_reg _ ?R ?V'@?T' = Some _ |- _] =>
      destruct (refine_registers_upd R V' T' H H1 H2) as [aregs' [? ?]]
    
  end; auto;

  (*handle abstract steps*)
  repeat (match goal with 
    | [|- exists _,  _ /\ _] => eexists; split
    | [|- Abstract.step _ _ _ _] => econstructor(eassumption)
    | [H: decode_instr _ = Some (Load _ _ _) |- Abstract.step _ _ _ _] => 
      eapply Abstract.step_load; eauto
    | [H: Symbolic.get_mem _ ?Addr = _, H1: refine_imemory _ _, H2: refine_dmemory _ _ 
       |- Abstract.get_imem _ ?Addr =  _ \/ Abstract.get_dmem _ ?Addr = _] => (*for load*)
      destruct t2; [left; apply H1 in H; eassumption | right; apply H2 in H; eassumption]
    | [H: decode_instr _ = Some (Store _ _ _) |- Abstract.step _ _ _ _] => 
      eapply Abstract.step_store; eauto
    | [H: decode_instr _ = Some (Jump _ _ ) |- Abstract.step _ _ _ _] => 
      eapply Abstract.step_jump; eauto
    | [H: decode_instr _ = Some (Bnz _ _ _) |- Abstract.step _ _ _ _] =>
      eapply Abstract.step_bnz; eauto
    | [H: decode_instr _ = Some (Jal _ _ ) |- Abstract.step _ _ _ _] =>
      eapply Abstract.step_jal; eauto
         end);

  (*handle final state refinement*)
  repeat (match goal with
    | [H: decode_instr _ = Some (Jump _ _) |- refine_state (_,_,_,_, valid_jmp ?Pc ?W) _] =>
      remember (valid_jmp Pc W) as b; destruct b; [left; unfold refine_normal_state; repeat (split; auto) | idtac]
    | [H: false = valid_jmp ?Pc ?W |- refine_state (_,_,_,_, false) _] =>
      right; unfold refine_violation_state
    | [|- _ /\ _] => split; [eauto | idtac]
    | [|- exists _ _, _] => exists (imem,dmem,aregs,pc,true)
    | [|- exists _, _] => eexists
    | [H: decode_instr _ = Some (Jump _ _) |- Abstract.step _ _ _ (_,_,_,_,false)] =>
      eapply Abstract.step_jump; eauto
    | [|- refine_state (_,_,_,_,true) _] => left 
    | [|- refine_normal_state _ _] => unfold refine_normal_state; simpl
    | [H: refine_imemory ?Imem ?Mem |- refine_imemory ?Imem ?Mem] => assumption
    | [H: refine_imemory ?Imem ?Mem |- refine_imemory ?Imem ?Mem'] => 
        eapply imem_upd_preservation; eauto
   end); 
  repeat match goal with
           | [H: refine_dmemory dmem ?Mem |- Symbolic.get_mem ?Mem _ = Some _] => eapply H; eauto
         end; auto. 

(*TODO: SYSTEM CALLS*)
Admitted.           

Lemma imem_refined_instructions mem imem pc i i' ut :
  refine_imemory imem mem ->
  Abstract.get_imem imem pc = Some i ->
  Symbolic.get_mem mem pc = Some i'@ut ->
  decode_instr i = decode_instr i'.
Proof.
  intros MEM GET GET'.
  destruct (MEM pc i).
  destruct H0. apply H0 in GET. rewrite GET in GET'. inversion GET'. subst. reflexivity.
Qed.

Lemma reg_refined_values reg areg r v v' ut :
  refine_registers areg reg ->
  Abstract.get_reg areg r = Some v ->
  Symbolic.get_reg reg r = Some v'@ut ->
  v = v'.
Proof.
  intros REG GET GET'.
  destruct (REG r v). destruct H0. apply H0 in GET.
  rewrite GET in GET'. inversion GET'. reflexivity.
Qed.


Theorem backwards_simulation_violation ast sst sst' :
  refine_violation_state ast sst ->
  Symbolic.step stable sst sst' ->
  exists ast',
    Abstract.step atable valid_jmp ast ast' /\
    refine_state ast' sst'.
Proof.
   intros REF SSTEP.
  destruct ast as [[[[imem dmem] aregs] apc] b].
  destruct b; [inversion SSTEP; subst; destruct REF; discriminate | idtac].
  destruct sst.
  destruct REF as [? [ast0 [sst0 REF]]].
  destruct ast0 as [[[[imem0 dmem0] aregs0] apc0] b0].
  destruct REF as [B0 [ASTEP0 [SSTEP0 [REF0 INVALID]]]];
  destruct sst0 as [mem0 regs0 [pc0 tpc0] ?]; 
  destruct REF0 as [? [PC0EQ [REFI0 [REFD0 [REFR0 REFS0]]]]]; subst;
  inversion ASTEP0;
  inversion SSTEP0; inversion ST; subst; clear ST;
  (*uninteresting cases*)
    match goal with 
        | [H: refine_imemory ?Imem ?Mem, H1: Abstract.get_imem ?Imem ?Pc = Some ?I,
           H2: Symbolic.get_mem ?Mem ?Pc = Some ?I'@_ |- _] => 
          destruct (imem_refined_instructions Pc H H1 H2); try congruence
    end. Focus 3.
  match goal with 
      [H: decode_instr ?I = Some ?V, H': decode_instr ?I = Some ?V' |- _] => 
      assert (EQINSTR: V = V') by (rewrite H in H'; inversion H'; auto); inversion EQINSTR;
      subst; clear EQINSTR
  end. 
  

  match goal with
      | [H: Abstract.get_reg ?Aregs ?R = Some ?V, H': Symbolic.get_reg ?Sregs ?R' = Some ?V'@_,
         H1: refine_registers ?Aregs ?Sregs |- _] =>
        apply H1 in H'
  end.
  unfold refine_syscalls in REFS0. apply REFS0 in GETCALL0. destruct GETCALL0. rewrite GETCALL in H1.
  
  rewrite INST0 in INST. inversion INST. subst.
  apply REFR0 in RW0. rewrite RW0 in RW. inversion RW. subst.
  unfold refine_syscalls in REFS0.
  destruct (REFS0 apc). 
  apply H1 in GETCALL0. destruct GETCALL0. rewrite GETCALL in H3. inversion H3.
  
  unfold refine_registers in REFR0.
  destruct ti; [idtac | simpl in ALLOWED; match_inv]. 
   match goal with
    | [H: Abstract.get_imem ?Imem ?Pc = Some ?I, H': Symbolic.get_mem ?Smem ?Pc = Some ?I'@(INSTR ?ID),
       H1: refine_imemory ?Imem ?Smem |- _] => 
      assert (I = I') by (apply H1 in H'; rewrite H' in H; inversion H; reflexivity); subst
    | [H: Abstract.get_reg ?Aregs ?R = Some ?V, H': Symbolic.get_reg ?Sregs ?R' = Some ?V'@_,
      H1: refine_registers ?Aregs ?Sregs |- _] =>
      apply H1 in H'
  end.
   match goal with 
         [H: decode_instr ?I = Some ?V, H': decode_instr ?I = Some ?V' |- _] => 
         assert (EQINSTR: V = V') by (rewrite H in H'; inversion H'; auto); inversion EQINSTR;
         subst; clear EQINSTR
   end.




  intros REF SSTEP.
  destruct ast as [[[[imem dmem] aregs] apc] b].
  destruct b; [inversion SSTEP; subst; destruct REF; discriminate | idtac];
  inversion SSTEP; subst;
  destruct REF as [? [ast0 [sst0 REF]]];
  destruct ast0 as [[[[imem0 dmem0] aregs0] apc0] b0];
  destruct REF as [B0 [ASTEP0 [SSTEP0 [REF0 INVALID]]]]; subst;
  destruct sst0 as [mem0 regs0 [pc0 tpc0] ?]; 
  destruct REF0 as [? [PC0EQ [REFI0 [REFD0 [REFR0 REFS0]]]]]; subst;
  inversion ASTEP0;
  inversion SSTEP0; inversion ST; subst;
  (*uninteresting cases*)
    match goal with 
        | [H: refine_imemory ?Imem ?Mem, H1: Abstract.get_imem ?Imem ?Pc = Some ?I,
           H2: Symbolic.get_mem ?Mem ?Pc = Some ?I'@_ |- _] => 
          destruct (imem_refined_instructions Pc H H1 H2); try congruence
    end;
    (*unfoldings and case analysis on tags*)
  repeat (
      match goal with
        | [H: Symbolic.next_state_pc _ _ _ = _ |- _] => unfold Symbolic.next_state_pc in H
        | [H: Symbolic.next_state_reg _ _ _ _ = _ |- _] => unfold Symbolic.next_state_reg in H
        | [H: Symbolic.next_state_reg_and_pc _ _ _ _ _ = _ |- _] => 
          unfold Symbolic.next_state_reg_and_pc in H
        | [H: Symbolic.next_state _ _ _ = Some _ |- _] =>
          unfold Symbolic.next_state in H; simpl in H
      end). Focus 4. rewrite CA

  
destruct ast0 as [[[[imem0 dmme0] aregs0] apc0] b0].
  destruct REF as [B0 [ASTEP0 [SSTEP0 [REF0 INVALID]]]]; subst.
  unfold Symbolic.next_state_pc in NEXT. unfold Symbolic.next_state in NEXT.
  simpl in NEXT. 
  destruct sst0 as [mem0 regs0 [pc0 tpc0] ?].
  destruct REF0 as [? [PC0EQ [REFI0 [REFD0 REFR0]]]]; subst.
  inversion ASTEP0; subst.

  repeat (
      match goal with
        | [H: refine_violation_state _ _ => destruct H as [? [? [? ?]]]
        | [H: 

 (*unfoldings and case analysis on tags*)
  repeat (
      match goal with
        | [H: Symbolic.next_state_pc _ _ _ = _ |- _] => unfold Symbolic.next_state_pc in H
        | [H: Symbolic.next_state_reg _ _ _ _ = _ |- _] => unfold Symbolic.next_state_reg in H
        | [H: Symbolic.next_state_reg_and_pc _ _ _ _ _ = _ |- _] => 
          unfold Symbolic.next_state_reg_and_pc in H
        | [H: Symbolic.next_state _ _ _ = Some _ |- _] =>
          unfold Symbolic.next_state in H; simpl in H; match_inv
      end);



  * (*case amachine took a jump*)
     inversion SSTEP0; inversion ST; subst;
    (*uninteresting cases*)
    match goal with 
        | [H: refine_imemory ?Imem ?Mem, H1: Abstract.get_imem ?Imem ?Pc = Some ?I,
           H2: Symbolic.get_mem ?Mem ?Pc = Some ?I'@_ |- _] => 
          destruct (imem_refined_instructions Pc H H1 H2); try congruence
    end. 
     (*case smachine took a jump too*)
     unfold Symbolic.next_state_pc in NEXT0.
     unfold Symbolic.next_state in NEXT0. simpl in NEXT0.
     assert (GET := jump_tagged pc0 FETCH INST0 REFI0).
     assert (ti0 = INSTR (Some pc0)).
     { rewrite GET in PC0; inversion PC0; auto. }
     subst.
     destruct tpc1.
    { (*case sst0 has a pc tag set*)
      destruct o; [idtac | inversion NEXT0].
      destruct (valid_jmp w0 pc0); [idtac | inversion NEXT0].
      simpl in NEXT0. inversion NEXT0; subst.
      destruct ti. (*could avoid this*)
      - (*case ti is tagged as an instr*)
        destruct o.
        + (*case ti has an id - only valid case since we are coming from a jump*)
          assert (w = pc) by (eapply id_hypothesis; eauto). subst w.
          assert (r = r0) by (rewrite INST0 in INST1; inversion INST1; auto); subst r0.
          assert (EQ := reg_refined_values r REFR0 RW RW0). subst apc.
          rewrite VALID in NEXT. match_inv.
        + simpl in NEXT; inversion NEXT.
      - simpl in NEXT; inversion NEXT.
    }
    { simpl in NEXT0. inversion NEXT0; subst.
      destruct ti. (*could avoid this*)
      - (*case ti is tagged as an instr*)
        destruct o.
        + (*case ti has an id - only valid case since we are coming from a jump*)
          assert (w = pc) by (eapply id_hypothesis; eauto). subst w.
          assert (r = r0) by (rewrite INST0 in INST1; inversion INST1; auto); subst r0.
          assert (EQ := reg_refined_values r REFR0 RW RW0). subst apc.
          rewrite VALID in NEXT. simpl in NEXT. inversion NEXT. match_inv.
        + simpl in NEXT; inversion NEXT.
      - simpl in NEXT; inversion NEXT.
    }
  * 



     simpl in H5. inversion H5; subst.
     rewrite INST0 in INST1. inversion INST1; subst.
     

     
     destruct tpc1.
    { (*case sst0 has a pc tag set*)
      destruct o; [idtac | inversion NEXT0].
      destruct (valid_jmp w0 pc0); [idtac | inversion NEXT0].
      simpl in NEXT0. inversion NEXT0; subst.
      destruct ti. (*could avoid this*)
      - (*case ti is tagged as an instr*)
        destruct o.
        + (*case ti has an id - only valid case since we are coming from a jump*)
          assert (w = pc) by (eapply id_hypothesis; eauto). subst w.
          assert (r = r0) by (rewrite INST0 in INST1; inversion INST1; auto); subst r0.
          assert (EQ := reg_refined_values r REFR0 RW RW0). subst apc.
          rewrite VALID in NEXT. match_inv.
        + simpl in NEXT; inversion NEXT.
      - simpl in NEXT; inversion NEXT.
    }
     
  



  (*nop*)
  unfold refine_violation_state in REF.
  destruct REF as [? [ast0 [sst0 REF]]].
  destruct ast0 as [[[[imem0 dmem0] aregs0] apc0] b0].
  destruct REF as [? [? [? [? ?]]]]; subst.
  unfold Symbolic.next_state_pc in NEXT. unfold Symbolic.next_state in NEXT.
  simpl in NEXT.
  unfold refine_normal_state in H3. 
  destruct sst0 as [mem0 regs0 [pc0 tpc0] ?]. 
  destruct H3 as [? [? [? [? ?]]]].
  inversion H1; subst.
  * (*case amachine took a jump*)
    inversion H2; inversion ST; subst;
    (*uninteresting cases*)
    match goal with 
        | [H: refine_imemory ?Imem ?Mem, H1: Abstract.get_imem ?Imem ?Pc = Some ?I,
           H2: Symbolic.get_mem ?Mem ?Pc = Some ?I'@_ |- _] => 
          destruct (imem_refined_instructions Pc H H1 H2); try congruence
    end. 
    (*case smachine took a jump too*)
    unfold Symbolic.next_state_pc in NEXT0.
    unfold Symbolic.next_state in NEXT0. simpl in NEXT0.
    assert (GET := jump_tagged pc0 FETCH INST0 H5). 
    assert (ti0 = (INSTR (Some pc0))).
    { rewrite GET in PC0. inversion PC0; auto. }
    subst ti0.
    destruct tpc1.
    { (*case sst0 has a pc tag set*)
      destruct o; [idtac | inversion NEXT0].
      destruct (valid_jmp w0 pc0); [idtac | inversion NEXT0].
      simpl in NEXT0. inversion NEXT0; subst.
      destruct ti. (*could avoid this*)
      - (*case ti is tagged as an instr*)
        destruct o.
        + (*case ti has an id - only valid case since we are coming from a jump*)
          assert (w = pc) by (eapply id_hypothesis; eauto). subst w.
          assert (r = r0) by (rewrite INST0 in INST1; inversion INST1; auto); subst r0.
          assert (EQ := reg_refined_values r H7 RW RW0). subst apc.
          rewrite VALID in NEXT. simpl in NEXT. inversion NEXT.
        + simpl in NEXT; inversion NEXT.
      - simpl in NEXT; inversion NEXT.
    }
    { simpl in NEXT0. inversion NEXT0; subst.
      destruct ti. (*could avoid this*)
      - (*case ti is tagged as an instr*)
        destruct o.
        + (*case ti has an id - only valid case since we are coming from a jump*)
          assert (w = pc) by (eapply id_hypothesis; eauto). subst w.
          assert (r = r0) by (rewrite INST0 in INST1; inversion INST1; auto); subst r0.
          assert (EQ := reg_refined_values r H7 RW RW0). subst apc.
          rewrite VALID in NEXT. simpl in NEXT. inversion NEXT.
        + simpl in NEXT; inversion NEXT.
      - simpl in NEXT; inversion NEXT.
    }
  * (*case amachine took a JAL*)
    inversion H2; inversion ST; subst;
    (*uninteresting cases*)
    match goal with 
        | [H: refine_imemory ?Imem ?Mem, H1: Abstract.get_imem ?Imem ?Pc = Some ?I,
           H2: Symbolic.get_mem ?Mem ?Pc = Some ?I'@_ |- _] => 
          destruct (imem_refined_instructions Pc H H1 H2); try congruence
    end.
   
    
      

(* ast ~v sst,  ast = (imem,dmem,reg,apc,false) 
   sst -> sst'
  --------------------
   ast ~v sst => ast0 ~ sst0, ast0 -> ast, sst0 -> sst, valid_jmp apc0 apc = false
   
   1. analysis on sst -> sst'
      a. case tpc = INSTR (Some n) and ti = INTR (Some m). By hypothesis n = apc0, m = apc.
      b. case tpc = DATA. by SSTEP, sst' rvec results in INSTR. Contadiction.
    

*)

Theorem backwards_simulation ast sst sst' :
  refine_state ast sst ->
  Symbolic.step stable sst sst' ->
  exists ast',
    Abstract.step atable valid_jmp ast ast' /\
    refine_state ast' sst'.
Proof.
Admitted.
 
    
    