Require Import Coq.Bool.Bool.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Require Import lib.utils lib.partial_maps lib.Coqlib.
Require Import common.common.
Require Import symbolic.symbolic.
Require Import cfi.abstract.
Require Import cfi.symbolic.
Require Import cfi.rules.
Require Coq.Vectors.Vector.

Set Implicit Arguments.

Module Map.
  Import PartMaps.

Section Mappable.
  Variable M1 M2 K V1 V2 : Type.

  
  Class mappable (pm1 : partial_map M1 K V1) (pm2 : partial_map M2 K V2) := {

    map : (V1 -> V2) -> M1 -> M2;

    map_correctness: forall (f : V1 -> V2) (m1 : M1) (k : K),
                       get (map f m1) k = option_map f (get m1 k)


    }.
End Mappable. 

End Map.

Module RefinementAS.

Section Refinement.
Import PartMaps.

Context {t : machine_types}
        {ops : machine_ops t}
        {opss : machine_ops_spec ops}
        
        {ap : Abs.abstract_params t}
        {aps : Abs.params_spec ap}

        {smemory : Type}
        {sm : partial_map smemory (word t) (atom (word t) (@cfi_tag t))}
        {smems : axioms sm}
        {smemory_map : Map.mappable sm (@Abs.dmem_class t ap)}

        {sregisters : Type}
        {sr : partial_map sregisters (reg t) (atom (word t) (@cfi_tag t))}
        {sregs : axioms sr}
        {sregs_map : Map.mappable sr (@Abs.reg_class t ap)}.

Variable valid_jmp : word t -> word t -> bool.

(* Instantiate the symbolic machine with the CFI stuff*)
Definition sym_params := Sym.sym_cfi valid_jmp.

Variable atable : list (Abs.syscall t).
Variable stable : list (@Symbolic.syscall t sym_params).

(*Probably not needed here*)
Definition amachine := Abs.abstract_cfi_machine atable valid_jmp.
Definition smachine := Sym.symbolic_cfi_machine stable.

(*Refinement related definitions*)
Definition refine_dmemory (admem : Abs.dmemory t)
                          (smem : smemory) :=
  forall w (x : word t),
    get smem w = Some x@DATA <->
    get admem w = Some x. 

Definition refine_imemory (aimem : Abs.imemory t)
                          (smem : smemory) :=
  forall w x,
    (exists id, get smem w = Some x@(INSTR id)) <->
    get aimem w = Some x.

Definition refine_registers (areg : Abs.registers t)
                            (sreg : sregisters) :=
  forall n (x : word t),
    (exists ut, get sreg n = Some x@ut) <->
    get areg n = Some x.

Definition refine_pc 
           (apc : word t) 
           (spc : atom (word t) (@Symbolic.tag t sym_params)) :=
  apc = common.val spc /\ 
  (common.tag spc = DATA \/ 
   exists id, common.tag spc = INSTR (Some id)).

Lemma refine_memory_total aimem admem smem :
  refine_imemory aimem smem ->
  refine_dmemory admem smem ->
  (forall addr, get aimem addr = None /\ get admem addr = None <->
                get smem addr = None).
Proof.
  intros REFI REFD addr.
  split.
  { intros [AGETI AGETD].
    destruct (get smem addr) eqn:GET.
    - destruct a as [v [id|]].
      + assert (EGET: exists id, get smem addr = Some v@(INSTR id)) 
          by (eexists; eauto).
        apply REFI in EGET. congruence.
      + apply REFD in GET.
        congruence.
    - reflexivity.
  }
  { intros GET. split.
    - destruct (get aimem addr) eqn:AGET.
      + apply REFI in AGET.
      destruct AGET as [id AGET]. congruence.
      + reflexivity.
    - destruct (get admem addr) eqn:AGET.
      + apply REFD in AGET.
        congruence.
      + reflexivity.
  }
Qed.
 
(*Some useless lemmas, just for sanity check -- probably to be removed*)
Lemma xxx : forall tpc ti,
    (tpc = DATA \/ tpc = INSTR None \/
     (exists src dst, tpc = INSTR (Some src) /\
                      ti = INSTR (Some dst) /\
                      valid_jmp src dst = true)) <->
    (forall src, tpc = INSTR (Some src) ->
       exists dst, ti = INSTR (Some dst) /\ valid_jmp src dst = true).
Proof.
  split.
  - intro H.
    destruct H as [? | [? | [src [dst [TPC [TI VALID]]]]]]; try (intros; congruence).
    intros src0 TPC'.
    rewrite TPC in TPC'. inversion TPC'; subst.
    eexists; eauto.
  - intros H.
    destruct tpc.
    + right. destruct o.
      * right.
        assert (H' := H s).
        destruct H' as [dst [? ?]]. reflexivity.
        eexists; eexists; eauto.
      * left; reflexivity.
    + left; reflexivity.
Qed.

Lemma yyy : forall tpc ti,
   match tpc with
   | INSTR (Some src) =>
     exists dst, ti = INSTR (Some dst) /\ valid_jmp src dst = true
   | _ => True
   end
    <->
    (forall src, tpc = INSTR (Some src) ->
       exists dst, ti = INSTR (Some dst) /\ valid_jmp src dst = true).
Proof.
  intros tpc ti.
  split.
  - destruct tpc.
    * destruct o.
      + intros H src H'. inversion H'; subst. assumption.
      + intros ? src CONTRA. inversion CONTRA.
    * intros ? ? CONTRA; inversion CONTRA.
  - intros H. 
    destruct tpc.
    * destruct o.
      + apply H; reflexivity.
      + auto.
    * auto.
Qed.

Definition symbolic_invariants (mem : Symbolic.memory t) := 
  Sym.instructions_tagged valid_jmp mem /\
  Sym.valid_jmp_tagged stable mem.

Definition refine_state (ast : Abs.state t)
                        (sst : @Symbolic.state t sym_params) :=
  let '(imem, dmem, aregs, apc, cont) := ast in
  let '(Symbolic.State smem sregs spc@tpc _) := sst in
  refine_imemory imem smem /\
  refine_dmemory dmem smem /\
  refine_registers aregs sregs /\
  refine_pc apc (spc@tpc) /\
  (forall i ti,
    get smem spc = Some i@ti ->
    (cont = true <->
    (forall src, tpc = INSTR (Some src) ->
       exists dst, ti = INSTR (Some dst) /\ valid_jmp src dst = true))) /\
  (forall sc, get smem spc = None -> 
   Symbolic.get_syscall stable spc = Some sc ->
   (cont = true <->
    (forall src, 
       tpc = INSTR (Some src) ->
       exists dst, 
         (Symbolic.entry_tag sc) = INSTR (Some dst) /\ valid_jmp src dst))) /\
  symbolic_invariants smem.

Definition refine_syscall acall scall :=
  forall ast sst,
    refine_state ast sst ->
    match acall ast, scall sst with
    | Some ares, Some sres => refine_state ares sres
    | None, None => True
    | _, _ => False
    end.

Definition syscall_domains
           (atbl : list (Abs.syscall t))
           (stbl : list (@Symbolic.syscall t sym_params)) : Prop :=
  forall addr,
    (exists acall, Abs.get_syscall atbl addr = Some acall) <->
    (exists scall, Symbolic.get_syscall stbl addr = Some scall).

Lemma same_domain_total :
  forall atbl stbl,
    syscall_domains atbl stbl ->
    forall addr', Abs.get_syscall atbl addr' = None <-> 
                  Symbolic.get_syscall stbl addr' = None.
Proof.
  intros atbl stbl SAME addr'.
  assert (ACALL: forall addr'', Abs.get_syscall atbl addr'' = None \/
                         exists ac, Abs.get_syscall atbl addr'' = Some ac).
  { intros addr'';
    destruct (Abs.get_syscall atbl addr'');
    [right; eexists; eauto | left; reflexivity].
  }
  assert (SCALL: forall addr'', Symbolic.get_syscall stbl addr'' = None \/
                         exists sc, Symbolic.get_syscall stbl addr'' = Some sc).
  { intros addr''.
    destruct (Symbolic.get_syscall stbl addr'');
      [right; eexists; eauto | left; reflexivity].
  }
  split.
  - intro ACALL'. 
    destruct (SCALL addr') as [? | CONTRA]; 
      [assumption | apply SAME in CONTRA; destruct CONTRA; congruence].
  - intro SCALL'.
    destruct (ACALL addr') as [? | CONTRA]; 
      [assumption | apply SAME in CONTRA; destruct CONTRA; congruence].
Qed.

(* Might need absence of duplicates in these maps? *)
(* Could use pointwise, and pointwise -> same_domains *)
Definition refine_syscalls 
           (atbl : list (Abs.syscall t))
           (stbl : list (@Symbolic.syscall t sym_params)) : Prop :=
  forall addr,
    match Abs.get_syscall atbl addr, Symbolic.get_syscall stbl addr with
    | Some acall, Some scall =>
      refine_syscall (@Abs.sem t ap acall)
                     (@Symbolic.run_syscall t sym_params scall)
    | None, None => True
    | _, _ => False
    end.

Lemma refine_syscalls_domains : forall atbl stbl,
  refine_syscalls atbl stbl ->
  syscall_domains atbl stbl.
Admitted.

Hypothesis refine_syscalls_correct : refine_syscalls atable stable.

Lemma syscalls_backwards_simulation ast sst addr sc sst' :
    refine_syscalls atable stable ->
    Symbolic.get_syscall stable addr = Some sc ->
    refine_state ast sst ->
    Symbolic.run_syscall sc sst = Some sst' ->
    exists ac ast',
      Abs.get_syscall atable addr = Some ac /\
      Abs.sem ac ast = Some ast' /\
      refine_state ast' sst'.
Proof.
  intros. unfold refine_syscalls in *. specialize (H addr).
  rewrite H0 in H. destruct (Abs.get_syscall atable addr); [| contradiction H].
  specialize (H _ _ H1). rewrite H2 in H.
  destruct (Abs.sem s ast) eqn:?; [| contradiction H].
  do 2 eexists. split. reflexivity. split. eassumption. assumption.
Qed.

Hypothesis syscall_sem :
  forall ac ast ast',
    Abs.sem ac ast = Some ast' ->
       let '(imem,dmem,aregs,pc,b) := ast in
       let '(imem',dmem',aregs',pc',b') := ast' in
         imem = imem' /\ b' = b.

(*We will need stronger assumption on symbolic system calls for fwd simulation?*)
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

Import Vector.VectorNotations.

Lemma refine_registers_upd sreg sreg' areg r v tg v' tg' :
  refine_registers areg sreg ->
  get sreg r = Some v@tg ->
  upd sreg r v'@tg' = Some sreg' ->
  exists areg',
    upd areg r v' = Some areg' /\
    refine_registers areg' sreg'.
Proof.
  intros REFR GET UPD. 
  assert (EGET: exists ut, get sreg r = Some v@ut) 
    by (eexists; eassumption).
  apply REFR in EGET.
  assert (NEW := PartMaps.upd_defined v' EGET).
  destruct NEW as [areg' UPD'].
  eexists; split; eauto.
  unfold refine_registers. intros r' v''.
  have [EQ|/eqP NEQ] := altP (r' =P r); [simpl in EQ | simpl in NEQ]; subst.
  *
    rewrite (PartMaps.get_upd_eq UPD').
    rewrite (PartMaps.get_upd_eq UPD). 
    split. 
    - intro H. destruct H as [ut H]. inversion H; reflexivity.
    - intro H. exists tg'; inversion H; reflexivity.
  * rewrite (PartMaps.get_upd_neq NEQ UPD).
    rewrite (PartMaps.get_upd_neq NEQ UPD').
    auto.
Qed.

Lemma refine_memory_upd smem smem' amemd addr v v' :
  refine_dmemory amemd smem ->
  get smem addr = Some v@DATA ->
  upd smem addr v'@DATA = Some smem' ->
  exists amemd',
    upd amemd addr v' = Some amemd' /\
    refine_dmemory amemd' smem'.
Proof.
  intros MEM GET UPD. 
  assert (GET': get amemd addr = Some v) 
    by (apply MEM in GET; auto).
  destruct (PartMaps.upd_defined v' GET') as [amem' UPD'].
  do 2 eexists; eauto.
  intros addr' w'.
  have [EQ|/eqP NEQ] := altP (addr' =P addr); [simpl in EQ | simpl in NEQ]; subst.
  - rewrite (PartMaps.get_upd_eq UPD).
    rewrite (PartMaps.get_upd_eq UPD').
    split; try congruence.
  - rewrite (PartMaps.get_upd_neq NEQ UPD').
    rewrite (PartMaps.get_upd_neq NEQ UPD).
    now apply MEM.
Qed.

Lemma data_memory_upd (smem : @Symbolic.memory t sym_params) smem' addr v v' :
  get smem addr = Some v@DATA -> 
  upd smem addr v'@DATA = Some smem' ->
  (forall addr' i id, 
     get smem addr' = Some i@(INSTR id) ->
     get smem' addr' = Some i@(INSTR id)).
Proof.
  intros GET UPD addr' i id GET'.
  have [EQ|/eqP NEQ] := altP (addr' =P addr); [simpl in EQ | simpl in NEQ]; subst.
  * rewrite GET in GET'. discriminate.
  * rewrite (PartMaps.get_upd_neq NEQ UPD);
    assumption.
Qed.

Lemma imem_upd_preservation amemi (smem : @Symbolic.memory t sym_params) 
      (smem' : @Symbolic.memory t sym_params) addr v v' :
  refine_imemory amemi smem ->
  get smem addr = Some v@DATA ->
  upd smem addr v'@DATA = Some smem' ->
  refine_imemory amemi smem'.
Proof.
  intros MEM GET UPD w x.
  split.
  - intros (id & GET').
    have [EQ|/eqP NEQ] := altP (addr =P w); [simpl in EQ | simpl in NEQ]; subst.
    * assert (CONTRA := PartMaps.get_upd_eq UPD).
      simpl in CONTRA. rewrite CONTRA in GET'. discriminate.
    * eapply PartMaps.get_upd_neq in UPD; eauto.
      simpl in UPD. rewrite UPD in GET'.
      eapply MEM; eauto.
  - intro GET'.
    apply MEM in GET'.
    have [EQ|/eqP NEQ] := altP (addr =P w); [simpl in EQ | simpl in NEQ]; subst.
    * simpl in GET. rewrite GET in GET'. destruct GET'; congruence.
    * eapply PartMaps.get_upd_neq in UPD; eauto; simpl in UPD;
      rewrite UPD; assumption.
Qed.


Lemma refine_imemory_none aimem smem pc :
  refine_imemory aimem smem ->
  get smem pc = None ->
  get aimem pc = None.
Proof.
  intros REF GET.
  case E: (get aimem pc) => [i|] //.
  move/(REF _ _): E => [? ?]; congruence.
Qed.


(*TODO: Syscalls and clean up of this mess*)
Theorem backwards_simulation ast sst sst' :
  refine_state ast sst ->
  Symbolic.step stable sst sst' ->
  exists ast',
    Abs.step atable valid_jmp ast ast' /\
    refine_state ast' sst'.
Proof.
  intros REF SSTEP.
  destruct ast as [[[[imem dmem] aregs] apc] b].
  destruct b.
  { (*1st case*)
    inversion SSTEP; subst;
    destruct REF 
      as [REFI [REFD [REFR [REFPC [CORRECTNESS [SYSCORRECT [ITG VALIDTGS]]]]]]];
    (*unfoldings and case analysis on tags*)
    repeat (
        match goal with
          | [H: refine_pc _ _ |- _] => 
            unfold refine_pc in H; simpl in H; destruct H as [? ?]
          | [H: Symbolic.next_state_pc _ _ _ = _ |- _] => 
            unfold Symbolic.next_state_pc in H
          | [H: Symbolic.next_state_reg _ _ _ _ = _ |- _] => 
            unfold Symbolic.next_state_reg in H
          | [H: Symbolic.next_state_reg_and_pc _ _ _ _ _ = _ |- _] => 
            unfold Symbolic.next_state_reg_and_pc in H
          | [H: Symbolic.next_state _ _ _ = Some _ |- _] =>
            unfold Symbolic.next_state in H; simpl in H
        end); match_inv; subst;
    (* switch memory updates to abstract*)
    repeat (
        match goal with
          | [H: upd ?Mem ?Addr ?V@_ = Some _, 
                H1 : refine_dmemory _ ?Mem, 
                     H2: get ?Mem ?Addr = Some _ |- _] => 
            simpl in H; 
          destruct (refine_memory_upd Addr V H1 H2 H) as [dmem' [? ?]]
        end);
    (*switch memory and register reads to abstract*)
    try match goal with
          | [H1: refine_imemory _ ?Mem, 
                 H2: get ?Mem ?Pc = Some ?I@(INSTR _) |- _] =>
            assert (exists id, get Mem Pc = Some I@(INSTR id)) 
              by (eexists;eauto)
        end;
    (*make register gets in the form of existentials*)
    try match goal with
          | [H1: refine_registers _ ?Reg, H2: get ?Reg ?R = Some ?V@_,
               H3: get ?Reg ?R' = Some ?V'@_, 
               H4: get ?Reg ?R'' = Some ?V''@_ |- _] =>
            assert (exists ut, get Reg R = Some V@ut) 
              by (eexists;eauto);
              assert (exists ut, get Reg R' = Some V'@ut) 
              by (eexists;eauto);
              assert (exists ut, get Reg R' = Some V'@ut) 
                by (eexists;eauto)
          | [H1: refine_registers _ ?Reg, H2: get ?Reg ?R = Some ?V@_,
               H3: get ?Reg ?R' = Some ?V'@_|- _] =>
            assert (exists ut, get Reg R = Some V@ut) 
              by (eexists;eauto);
              assert (exists ut, get Reg R' = Some V'@ut) 
              by (eexists;eauto)
          | [H1: refine_registers _ ?Reg, 
               H2: get ?Reg ?R = Some ?V@_ |- _] =>
            assert (exists ut, get Reg R = Some V@ut) 
              by (eexists;eauto)
        end;
    (*do actual refinements*)
    repeat match goal with
             | [H1: refine_imemory _ ?Mem, 
                    H2: exists _, get ?Mem _ = Some _@(INSTR _) |- _] =>
               apply H1 in H2
             | [H1: refine_dmemory _ ?Mem, H2: get ?Mem _ = Some _@DATA |- _] => 
               apply H1 in H2
             | [H1: refine_registers _ ?Reg, 
                    H2: exists _, get ?Reg _ = Some _ |- _] => 
               apply H1 in H2
           end;
    (*Refine registers update - unsure about this part - it seems to still work*)
    repeat match goal with
             | [H: refine_registers ?Aregs ?Regs, 
                 H1: get ?Aregs ?R = Some ?Old |- _] => 
               unfold refine_registers in H; destruct (H R Old) as [RSA RAS]; 
               destruct RAS as [x RAS'];
               apply RAS' in H1; fold (refine_registers Aregs Regs) in H
             | [H: refine_registers _ _, H1: get ?Reg ?R = Some _,
                 H2: upd _ ?R ?V'@?T' = Some _ |- _] =>
               destruct (refine_registers_upd R V' T' H H1 H2) as [aregs' [? ?]]
                                                                    
           end; auto;
    pose proof (refine_syscalls_domains refine_syscalls_correct) as DOMAIN.
    (* put into context stuff required for syscalls *)
    match goal with
      | [H1: Symbolic.get_syscall _ ?W = Some _
         |- _] => (
          assert (EGETCALL: exists sc, Symbolic.get_syscall stable W = Some sc)
          by (eexists; eauto);
          destruct (DOMAIN W) as [ASDOM SADOM];
          apply SADOM in EGETCALL; destruct EGETCALL;
          assert (REF: refine_state (imem,dmem,aregs,pc,true) 
                                    (Symbolic.State mem reg pc@tpc int))
            by (repeat (split; auto));
          destruct (syscalls_backwards_simulation (imem,dmem,aregs,pc,true) 
                                                  (Symbolic.State mem reg pc@tpc int)
                                                  W
                                                  refine_syscalls_correct H1
                                                  REF CALL) as
              [ac [ast' [GETCALL' [CALL' FINALREF]]]];
          destruct ast' as [[[[imem' dmem'] aregs'] apc'] b];
          destruct (syscall_sem ac (imem,dmem,aregs,pc,true) CALL') as 
              [? ?];
          subst
        ) || fail 4 "Couldn't analyze syscall"
      | |- _ => idtac
    end. Focus 14. eexists; split.
    eapply Abs.step_jump. eauto. eauto. eauto. eauto.
    
    
    (*handle abstract steps*)
    repeat (match goal with 
              | [|- exists _,  _ /\ _] => eexists; split
              | [|- Abs.step _ _ _ _] => econstructor(eassumption)
              | [H: decode_instr _ = Some (Load _ _ _) |- Abs.step _ _ _ _] => 
                eapply Abs.step_load; eauto
              | [H: get ?Mem ?Addr = Some ?V@?TG, H1: refine_imemory _ _, 
                  H2: refine_dmemory _ _ |- get _ ?Addr =  _ \/ get _ ?Addr = _] => (*for load*)
                destruct TG; 
                  [left; 
                    assert(MEMLOAD: exists id, get Mem Addr = Some V@(INSTR id)) 
                     by (eexists; eauto); apply H1 in MEMLOAD; eassumption | 
                   right; apply H2 in H; eassumption]
              | [H: decode_instr _ = Some (Store _ _ _) |- Abs.step _ _ _ _] => 
                eapply Abs.step_store; eauto
              | [H: decode_instr _ = Some (Jump _ _ ) |- Abs.step _ _ _ _] => 
                eapply Abs.step_jump; eauto
              | [H: decode_instr _ = Some (Bnz _ _ _) |- Abs.step _ _ _ _] =>
                eapply Abs.step_bnz; eauto
              | [H: decode_instr _ = Some (Jal _ _ ) |- Abs.step _ _ _ _] =>
                eapply Abs.step_jal; eauto
              | [H: get _ ?Pc = None, H1: refine_imemory _ _, 
                     H2: refine_dmemory _ _ |- _] => 
                  destruct (refine_memory_total H1 H2 Pc) as [? NOMEM];
                  destruct (NOMEM H)
              | [H1: Symbolic.get_syscall _ _ = Some _ |- Abs.step _ _ _ _] =>
                eapply Abs.step_syscall; eauto 
            end);
    unfold refine_state; 
    (*handle final state refinement*)
    repeat (match goal with
              | [H: decode_instr _ = Some (Jump _ _) 
                   |- refine_state (_,_,_,_, valid_jmp ?Pc ?W) _] =>
                remember (valid_jmp Pc W) as b; destruct b; 
                [left; unfold refine_normal_state; repeat (split; auto) | idtac]
              | [|- _ /\ _] => split; [eauto | idtac]
              | [H: decode_instr _ = Some (Jump _ _) |- 
                 Abs.step _ _ _ (_,_,_,_,false)] =>
                  eapply Abs.step_jump; eauto
              | [H: refine_imemory ?Imem ?Mem |- refine_imemory ?Imem ?Mem] => 
                assumption
              | [H: refine_imemory ?Imem ?Mem |- refine_imemory ?Imem ?Mem'] => 
                eapply imem_upd_preservation; eauto
              | [|- refine_pc _ _] => unfold refine_pc; simpl; auto
              | [|- INSTR _ = DATA \/ _ ] => right; eexists; eauto
            end);
    (*handle the correctness part*)
    repeat match goal with
             | [|- forall _, _] => intros
             | [|- _ <-> _] => simpl; split; try discriminate
             | [|- true = true] => reflexivity
           end; 
    repeat match goal with
             | [H: refine_dmemory dmem ?Mem |- get ?Mem _ = Some _] => 
               eapply H; eauto
           end; auto;
    (*jump/jal related stuff*)
    (*no syscall*)
    repeat (
        match goal with
          | [H: INSTR _ = INSTR _ |- _] => inv H
        end).
    unfold Sym.valid_jmp_tagged in VALIDTGS. 
    destruct (VALIDTGS _ _ H3) as [[? GET] [[I' GET'] | [GET' SCTG]]].
    rewrite H2 in GET'. inversion GET'. subst.
    exists w. rewrite GET in PC. inversion PC; subst.
    split; auto.
    rewrite GET' in H2. congruence.
    destruct (H3 _ erefl) as [dst [TI VALID]]. clear H3.
    subst. 
    try match goal with
          | [H: Sym.valid_jmp_tagged _ _,
             H' : valid_jmp _ _ = true |- _] => 
            unfold Sym.valid_jmp_tagged in H;
            destruct (H _ _ H') as [? ?] [[? ?] | [? ?]]]
         end;
     try match goal with
           | [H: get ?Mem ?Pc

    Focus 2. simpl in SSTEP. 
    destruct (CORRECTNESS w 
    try match goal with
          | [H: get ?Mem ?Pc = Some ?I@(INSTR (Some _)), 
              H1: decode_instr ?I = Some (Jump _ ?R), 
              H2: get ?Reg ?R = Some ?W@_,
              H3: get ?Mem ?W = Some _ |- _] =>
              assert (EQ := jump_target_tagged Pc Mem Reg H H1 H2 H3);
              assert (EQ' := jump_tagged Pc Mem H H1); inversion EQ'; subst
          | [H: get ?Mem ?Pc = Some ?I@(INSTR (Some _)), 
              H1: decode_instr ?I = Some (Jump _ ?R), 
              H2: get ?Reg ?R = Some ?W@_,
              H3: get ?Mem ?W = None,
              H4: Symbolic.get_syscall stable ?W = Some ?Sc |- _] =>
              assert (EQ := jump_entry_tagged Pc Mem Reg H H1 H2 H3 H4);
              assert (EQ' := jump_tagged Pc Mem H H1); inversion EQ'; subst
          | [H: get ?Mem ?Pc = Some ?I@(INSTR (Some _)), 
                H1: decode_instr ?I = Some (Jal _ ?R), 
                H2: get ?Reg ?R = Some ?W@_,
                H3: get ?Mem ?W = Some _ |- _] =>
            assert (EQ := jal_target_tagged Pc Mem Reg H H1 H2 H3);
              assert (EQ' := jal_tagged Pc Mem H H1); inversion EQ'; subst
          | [H: get ?Mem ?Pc = Some ?I@(INSTR (Some _)), 
                H1: decode_instr ?I = Some (Jal _ ?R), 
                H2: get ?Reg ?R = Some ?W@_,
                H3: get ?Mem ?W = None,
                H4: Symbolic.get_syscall stable ?W = Some ?Sc |- _] =>
              assert (EQ := jal_entry_tagged Pc Mem Reg H H1 H2 H3 H4);
              assert (EQ' := jal_tagged Pc Mem H H1); inversion EQ'; subst
        end; 
   try  match goal with
          | [|- exists _, INSTR (Some ?W) = INSTR _ /\ valid_jmp _ _ = true] =>
            exists W; split; auto
          | [H0': get mem ?W = Some _@(INSTR (Some ?W)), 
             H': forall _, INSTR (Some ?W) = INSTR (Some _) -> _ 
                           |- valid_jmp _ _ = true] =>
            destruct (H' W erefl) as [dst' [TI' VALID']]; try (rewrite EQ in TI'); 
            inv TI'; auto
        end; eauto.
    (*these should somehow become 1, but I am not sure what's wrong*)
Admitted.
      match goal with
        | [|- exists _, INSTR (Some ?W) = INSTR _ /\ valid_jmp _ _ = true] =>
          exists W; split; auto
        | [H0': get mem ?W = Some _@(INSTR (Some ?W)), 
               H': forall _, INSTR (Some ?W) = INSTR (Some _) -> _ 
                         |- valid_jmp _ _ = true] =>
           destruct (H' W erefl) as [dst' [TI' VALID']]; try (rewrite EQ in TI'); 
           inv TI'; auto
      end.
      match goal with
        | [|- exists _, INSTR (Some ?W) = INSTR _ /\ valid_jmp _ _ = true] =>
          exists W; split; auto
        | [H0': get mem ?W = Some _@(INSTR (Some ?W)), 
               H': forall _, INSTR (Some ?W) = INSTR (Some _) -> _ 
                         |- valid_jmp _ _ = true] =>
           destruct (H' W erefl) as [dst' [TI' VALID']]; try (rewrite EQ in TI'); 
           inv TI'; auto
      end.
      match goal with
        | [|- exists _, INSTR (Some ?W) = INSTR _ /\ valid_jmp _ _ = true] =>
          exists W; split; auto
        | [H0': get mem ?W = Some _@(INSTR (Some ?W)), 
               H': forall _, INSTR (Some ?W) = INSTR (Some _) -> _ 
                         |- valid_jmp _ _ = true] =>
           destruct (H' W erefl) as [dst' [TI' VALID']]; try (rewrite EQ in TI'); 
           inv TI'; auto
      end.
      match goal with
        | [|- exists _, INSTR (Some ?W) = INSTR _ /\ valid_jmp _ _ = true] =>
          exists W; split; auto
        | [H0': get mem ?W = Some _@(INSTR (Some ?W)), 
               H': forall _, INSTR (Some ?W) = INSTR (Some _) -> _ 
                         |- valid_jmp _ _ = true] =>
           destruct (H' W erefl) as [dst' [TI' VALID']]; try (rewrite EQ in TI'); 
           inv TI'; auto
      end.
      match goal with
        | [|- exists _, INSTR (Some ?W) = INSTR _ /\ valid_jmp _ _ = true] =>
          exists W; split; auto
        | [H0': get mem ?W = Some _@(INSTR (Some ?W)), 
               H': forall _, INSTR (Some ?W) = INSTR (Some _) -> _ 
                         |- valid_jmp _ _ = true] =>
           destruct (H' W erefl) as [dst' [TI' VALID']]; try (rewrite EQ in TI'); 
           inv TI'; auto
      end.
      match goal with
        | [|- exists _, INSTR (Some ?W) = INSTR _ /\ valid_jmp _ _ = true] =>
          exists W; split; auto
        | [H0': get mem ?W = Some _@(INSTR (Some ?W)), 
               H': forall _, INSTR (Some ?W) = INSTR (Some _) -> _ 
                         |- valid_jmp _ _ = true] =>
           destruct (H' W erefl) as [dst' [TI' VALID']]; try (rewrite EQ in TI'); 
           inv TI'; auto
      end.
      match goal with
        | [|- exists _, INSTR (Some ?W) = INSTR _ /\ valid_jmp _ _ = true] =>
          exists W; split; auto
        | [H0': get mem ?W = Some _@(INSTR (Some ?W)), 
               H': forall _, INSTR (Some ?W) = INSTR (Some _) -> _ 
                         |- valid_jmp _ _ = true] =>
           destruct (H' W erefl) as [dst' [TI' VALID']]; try (rewrite EQ in TI'); 
           inv TI'; auto
      end.
      match goal with
        | [|- exists _, INSTR (Some ?W) = INSTR _ /\ valid_jmp _ _ = true] =>
          exists W; split; auto
        | [H0': get mem ?W = Some _@(INSTR (Some ?W)), 
               H': forall _, INSTR (Some ?W) = INSTR (Some _) -> _ 
                         |- valid_jmp _ _ = true] =>
           destruct (H' W erefl) as [dst' [TI' VALID']]; try (rewrite EQ in TI'); 
           inv TI'; auto
      end.           
  }
  { 
    inversion SSTEP; subst;
    destruct REF as [REFI [REFD [REFR [REFPC [CORRECTNESS SYSCORRECT]]]]];
    match goal with 
      | [H : refine_pc _ ?Pc@_, H': get _ ?Pc = Some ?I@?Ti |- _] => 
        destruct (CORRECTNESS I Ti H') as [? ABSURD]
      | [H : refine_pc _ ?Pc@_, H' : get _ ?Pc = None, 
             H'': Symbolic.get_syscall _ _ = Some _ |- _] => 
        destruct (SYSCORRECT _ H' H'') as [? ABSURD]
    end;
    (*unfoldings and case analysis on tags*)
    repeat (
        match goal with
          | [H: refine_pc _ _ |- _] => unfold refine_pc in H; simpl in H
          | [H: Symbolic.next_state_pc _ _ _ = _ |- _] =>
            unfold Symbolic.next_state_pc in H
          | [H: Symbolic.next_state_reg _ _ _ _ = _ |- _] =>
            unfold Symbolic.next_state_reg in H
          | [H: Symbolic.next_state_reg_and_pc _ _ _ _ _ = _ |- _] =>
            unfold Symbolic.next_state_reg_and_pc in H
          | [H: Symbolic.next_state _ _ _ = Some _ |- _] =>
            unfold Symbolic.next_state in H; simpl in H
          | [H: Symbolic.run_syscall _ _ = Some _ |- _] => 
            unfold Symbolic.run_syscall in H; 
            unfold Symbolic.handler in H; simpl in H
        end); match_inv; subst; assert (false = true);
    try match goal with
          | [H: _ -> false = true |- false = true] => apply H
        end;
    repeat match goal with
             | [|- forall _, _] => intros
             | [H: INSTR _ = INSTR _ |- _] => inversion H; subst; clear H
             | [H: DATA = INSTR _ |- _] => inversion H
             | [|- exists _, _] => eexists; eauto
           end; try discriminate.
  }
Grab Existential Variables.
discriminate.
discriminate.
discriminate.
discriminate.
discriminate.
discriminate.
discriminate.
discriminate.
discriminate.
discriminate.
discriminate.
discriminate.
discriminate.
discriminate.
discriminate.
discriminate.
discriminate.
discriminate.
discriminate.
discriminate.
Qed.

Definition untag_atom (a : atom (word t) (@cfi_tag t)) := common.val a.

Lemma reg_refinement_preserved_by_equiv : 
  forall areg reg reg',
    refine_registers areg reg ->
    Sym.equiv reg reg' ->
    exists areg',
      refine_registers areg' reg'.
Proof.
  intros areg reg reg' REF EQUIV.
  unfold Sym.equiv in EQUIV.
  unfold refine_registers in REF.
  assert (MAP := Map.map_correctness untag_atom reg'). 
  exists (Map.map untag_atom reg'). subst.
  intros r v.
  split.
  - intro GET. destruct GET as [ut GET].
    assert (MAP' := MAP r).
    rewrite GET in MAP'.
    simpl in MAP'. assumption.
  - intro GET'. 
    assert (MAP' := MAP r). 
    rewrite GET' in MAP'.
    remember (get reg' r) as a.
    destruct a as [[v' tg]|]. 
    + simpl in MAP'. inversion MAP'.
      eexists; eauto.
    + simpl in MAP'. discriminate.
Qed.

Lemma imem_refinement_preserved_by_equiv :
  forall imem mem mem',
    refine_imemory imem mem ->
    Sym.equiv mem mem' ->
    refine_imemory imem mem'.
Proof.
  intros imem mem mem' REF EQUIV.
  unfold Sym.equiv in EQUIV.
  intros addr v.
  split.
  - destruct (REF addr v) as [MEMSA MEMAS].
    intro GET.
    assert (EQUIV' := EQUIV addr). clear EQUIV.
    destruct (get mem addr) eqn:GET'.
    + assert (GET'' := GET).
      destruct GET as [id GET].
      rewrite GET in EQUIV'. inversion EQUIV'; subst. 
      * simpl in H0. congruence.
      * rewrite GET in GET''. apply MEMSA in GET''. assumption.
    + destruct (get mem' addr).
      * destruct EQUIV'.
      * destruct GET as [? CONTRA]. discriminate.
  - intro GET.
    assert (EQUIV' := EQUIV addr); clear EQUIV.
    destruct (get mem addr) eqn:GET'.
    + destruct (get mem' addr) eqn:GET''.
      * destruct EQUIV' as [? ? TG TG' | a' a'' id' id'' TG TG' EQ].
        { unfold refine_imemory in REF. apply REF in GET.
          destruct GET as [id GET].
          rewrite GET' in GET. destruct a as [v' tg]; subst. 
          simpl in TG. congruence. }
        { subst. apply REF in GET.  destruct GET as [id''' GET]. 
          rewrite GET' in GET. exists id'''. assumption.
        }
      * destruct EQUIV'.
    + destruct (get mem' addr) eqn:GET''.
      * destruct EQUIV'.
      * apply REF in GET. destruct GET as [? CONTRA]. congruence.
Qed.

Definition is_data (a : atom (word t) (@cfi_tag t)) := 
  match common.tag a with
    | DATA => true
    | INSTR _ => false
  end.

Lemma refine_dmemory_domains dmem mem :
  refine_dmemory dmem mem ->
  same_domain dmem (Filter.filter is_data mem).
Proof.
  intros REF addr. 
  unfold refine_dmemory in REF.
  destruct (get dmem addr) eqn:GET.
  + destruct (get (Filter.filter is_data mem) addr) eqn:GET'.
    * auto.
    * assert (FILTER := Filter.filter_correctness is_data mem).
      assert (FILTER' := FILTER addr); clear FILTER.
      apply REF in GET.
      rewrite GET in FILTER'. simpl in FILTER'. congruence.
  + destruct (get (Filter.filter is_data mem) addr) eqn:GET'.
    * assert (FILTER := Filter.filter_correctness is_data mem).
      assert (FILTER' := FILTER addr); clear FILTER.
      destruct (get mem addr) eqn:GET''.
      destruct a0 as [v tg].
      destruct tg.
      - simpl in FILTER'. congruence.
      - simpl in FILTER'. apply REF in GET''. congruence.
      - congruence.
    * auto.
Qed.

Lemma dmem_refinement_preserved_by_equiv :
  forall dmem mem mem',
    refine_dmemory dmem mem ->
    Sym.equiv mem mem' -> 
    exists dmem',
      refine_dmemory dmem' mem'.
Proof.
  intros dmem mem mem' REF EQUIV.
  assert (FILTER := Filter.filter_correctness is_data mem').
  assert (MAP := Map.map_correctness untag_atom (Filter.filter is_data mem')). 
  exists (Map.map untag_atom (Filter.filter is_data mem')). subst.
  intros addr v.
  split.
  - intro GET.
    assert (FILTER' := FILTER addr).
    rewrite GET in FILTER'. simpl in FILTER'.
    assert (MAP' := MAP addr).
    rewrite FILTER' in MAP'. simpl in MAP'. assumption.
  - intro GET. 
    assert (FILTER' := FILTER addr); clear FILTER.
    assert (MAP' := MAP addr); clear MAP. 
    destruct (get mem' addr) eqn:GET'.
    + destruct a as [v' tg].
      destruct tg; simpl in FILTER'; 
      rewrite FILTER' in MAP'; simpl in MAP'; 
      congruence.
    + rewrite FILTER' in MAP'. simpl in MAP'. congruence.
Qed.

Lemma dmem_domain_preserved_by_equiv :
  forall dmem dmem' mem mem',
    refine_dmemory dmem mem ->
    Sym.equiv mem mem' -> 
    refine_dmemory dmem' mem' ->
    same_domain dmem dmem'.
Proof.
  intros dmem dmem' mem mem' REF EQUIV REF'.
  assert (DOMAINMM' := Sym.equiv_same_domain EQUIV).
  assert (DOMAINDM' := refine_dmemory_domains REF').
  assert (DOMAINDM := refine_dmemory_domains REF).
  subst.
  assert (FILTER := Filter.filter_correctness is_data mem').
  intro addr.
    assert (FILTER' := FILTER addr); clear FILTER.
    assert (EQUIV' := EQUIV addr); clear EQUIV.
    assert (DOMAINFMFM': same_domain (Filter.filter is_data mem) (Filter.filter is_data mem')).
    { apply Filter.filter_domains with (k := addr); auto.
      destruct (get mem addr) eqn:GET.
      + destruct (get mem' addr) eqn:GET'.
        * destruct a as [v tg], a0 as [v0 tg0].
          destruct tg, tg0.
          - reflexivity.
          - destruct EQUIV' as [a a' TG TG' | a a' id id' TG TG' EQ].
            { unfold is_data. rewrite TG TG'. reflexivity. }
            { inversion EQ; auto. }
          - destruct EQUIV' as [a a' TG TG' | a a' id id' TG TG' EQ].
            { unfold is_data. rewrite TG TG'. reflexivity. }
            { inversion EQ; auto. }
          - reflexivity.
        * destruct EQUIV'.
      + destruct (get mem' addr) eqn:GET'.
        * destruct EQUIV'.
        * auto.
    }
    assert (DOMAIN: same_domain dmem dmem'). 
    { eapply same_domain_trans; eauto. apply same_domain_comm.
      eapply same_domain_trans; eauto. apply same_domain_comm;
      assumption. }
    apply DOMAIN.
Qed.

Lemma refine_reg_domains areg reg :
  refine_registers areg reg ->
  same_domain areg reg.
Proof.
  intros REF n. 
  unfold refine_registers in REF.
  destruct (get areg n) eqn:GET.
  + destruct (get reg n) eqn:GET'.
    * auto.
    * apply REF in GET. destruct GET as [? GET].
      rewrite GET in GET'. congruence.
  + destruct (get reg n) eqn:GET'.
    * destruct a as [v ut].
      assert (EGET' : exists ut, get reg n = Some v@ut) by (eexists; eauto).
      apply REF in EGET'.
      rewrite GET in EGET'. congruence.
    * constructor.
Qed.

Lemma reg_domain_preserved_by_equiv :
  forall areg areg' reg reg',
    refine_registers areg reg ->
    Sym.equiv reg reg' -> 
    refine_registers areg' reg' ->
    same_domain areg areg'.
Proof.
  intros areg areg' reg reg' REF EQUIV REF'.
  unfold same_domain. unfold pointwise.
  intro n.
  assert (DOMAIN : same_domain areg reg)
    by (apply refine_reg_domains; auto).
  assert (DOMAIN' : same_domain areg' reg')
    by (apply refine_reg_domains; auto).
  assert (EQUIV' := EQUIV n). clear EQUIV.
  destruct (get reg n) eqn:GET, (get reg' n) eqn:GET'.
  { destruct a as [v ut], a0 as [v' ut'].
    assert (EGET: exists ut, get reg n = Some v@ut) by (eexists;eauto).
    assert (EGET': exists ut, get reg' n = Some v'@ut) by (eexists;eauto).    
    apply REF in EGET. apply REF' in EGET'.
    rewrite EGET EGET'. constructor.
  }
  { destruct EQUIV'. }
  { destruct EQUIV'. }
  { destruct (get areg n) eqn:AGET, (get areg' n) eqn:AGET'.
    - constructor.
    - apply REF in AGET. destruct AGET as [? AGET].
      rewrite AGET in GET. congruence.
    - apply REF' in AGET'. destruct AGET' as [? AGET'].
      rewrite AGET' in GET'. congruence.
    - constructor.
  }
Qed.
  
Theorem backwards_simulation_attacker ast sst sst' :
  refine_state ast sst ->
  Sym.step_a sst sst' ->
  exists ast',
    Abs.step_a ast ast' /\
    refine_state ast' sst'.
Proof.
  intros REF SSTEP.
  destruct ast as [[[[imem dmem] aregs] apc] b].
  destruct b; inversion SSTEP; subst;
  unfold refine_state in REF; 
  destruct REF as [REFI [REFD [REFR [REFPC [CORRECTNESS SYSCORRECT]]]]];
  unfold refine_pc in REFPC; simpl in REFPC; destruct REFPC as [? ?]; subst.
  { destruct (reg_refinement_preserved_by_equiv REFR REQUIV) as [aregs' REFR'];
    assert (REFI' := imem_refinement_preserved_by_equiv REFI MEQUIV);
    destruct (dmem_refinement_preserved_by_equiv REFD MEQUIV) as [dmem' REFD'];
    assert (DOMAINM := dmem_domain_preserved_by_equiv REFD MEQUIV REFD').
    assert (DOMAINR := reg_domain_preserved_by_equiv REFR REQUIV REFR').
    assert (EFETCH : exists id, get mem pc = Some i@(INSTR id)) by (eexists; eauto);
    apply REFI in EFETCH;
    exists (imem, dmem', aregs', pc, true).
    split; [econstructor(eauto) | repeat (split; auto)].
    { (*proof in case of no syscall*)
      intros ? src TAG.
      unfold Sym.equiv in MEQUIV.
      assert (MEQUIV' := MEQUIV pc); clear MEQUIV.
      destruct (get mem pc) eqn:GET. 
      { destruct (get mem' pc) eqn:GET'.
        + destruct MEQUIV' as [a a' TG1 TG2 | a a0 id' id'' TG TG' EQ].
        - destruct a as [av atg].
          simpl in TG1. rewrite TG1 in GET. apply CORRECTNESS in GET.
          assert (TRUE: true = true) by reflexivity.
          destruct GET as [CORRECT ?].
          destruct tpc as [opt_id|].
          * destruct opt_id.
            { apply CORRECT with (src := s) in TRUE.
              destruct TRUE as [? [CONTRA ?]].
              discriminate.
              reflexivity.
            }
            { inversion TAG. }
          * inversion TAG.
        - subst. simpl in GET. destruct a0 as [a0_v a0_t]. 
          apply CORRECTNESS in GET. destruct GET as [CORRECT ?].
          assert (TRUE: true = true) by reflexivity.
          simpl in TG. apply CORRECT with (src0 := src) in TRUE.
          simpl in GET'. simpl in H. rewrite GET' in H. inversion H. subst a0_t.
          subst ti. assumption.
          reflexivity.
          + destruct MEQUIV'.
      }
      { destruct (get mem' pc) eqn:GET'.
        - destruct MEQUIV'.
        - simpl in H. simpl in GET'. rewrite GET' in H. discriminate.
      }
    }
    { (*proof syscall case*)
      apply REFI' in EFETCH.
      destruct EFETCH as [? CONTRA].
      rewrite CONTRA in H. congruence.
    }
  }
  { (*case a violation has happened*)
    unfold Sym.no_violation in NOV.
    destruct (CORRECTNESS i _ FETCH) as [? CONTRA].
    assert (HYPOTHESIS: (forall src : word t,
                           tpc = INSTR (Some src) ->
                           exists dst : word t,
                             INSTR id = INSTR (Some dst) /\ valid_jmp src dst = true)).
          by (intros src TPC; eapply NOV; eauto).
    apply CONTRA in HYPOTHESIS. discriminate.
  }
Qed.

(* NOTE: Do not remove*)
(*This is a helper lemma to instantiate CFI refinement between 
  symbolic and concrete*)
(*Lemma attacker_no_v : forall si sj,
                 Sym.ssucc si sj = false ->
                 Symbolic.step stable si sj ->
                 Sym.step_a si sj ->
                 False.
Proof.
  intros si sj SUCC STEP STEPA.
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
  rewrite FETCH in PC.  inversion PC; subst.
  assert (JMPTG := jump_tagged pc0 mem0 FETCH INST). inversion JMPTG; subst.
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
  assert (JMPTG := jal_tagged pc0 mem0 FETCH INST). inversion JMPTG; subst.
  congruence.
Admitted. *)


End Refinement.

End RefinementAS.
