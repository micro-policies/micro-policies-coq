Require Import Coq.Bool.Bool.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Require Import lib.utils lib.partial_maps lib.Coqlib.
Require Import common.common.
Require Import symbolic.symbolic.
Require Import cfi.abstract.
Require Import cfi.symbolic.
Require Import cfi.cfi_rules.
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

(* unused
    map_domains: forall (f : V1 -> V2) (m1 : M1) (k : K) (v : V2),
                   get (map f m1) k = Some v ->
                   exists (v' : V1), get m1 k = Some v'
*)
    }.
End Mappable. 

End Map.

Module Filter.
  Import PartMaps.

Section Filter.
  Variable M K V : Type.

  
  Class filterable (pm : partial_map M K V) := {

    filter : (V -> bool) -> M -> M;

    filter_correctness: forall (f : V -> bool) (m : M) (k : K),
                       get (filter f m) k = match get m k with 
                                              | Some v => 
                                                if f v then Some v else None
                                              | None => None
                                            end;

    filter_domains : forall (f : V -> bool) (m : M) (m' : M) (k : K),
                       same_domain(*s*) m m' ->
                       match get m k, get m' k with 
                         | Some v, Some v' => f v = f v'
                         | None, None => True
                         | _, _ => False
                       end ->
                       same_domain (filter f m) (filter f m')
                                              

    }.
End Filter. 

End Filter.

Module RefinementAS.

Section Refinement.
Import PartMaps.

Context {t : machine_types}
        {ops : machine_ops t}
        {opss : machine_ops_spec ops}
        
        {ap : Abstract.abstract_params t}
        {aps : Abstract.params_spec ap}

        {smemory : Type}
        {sm : partial_map smemory (word t) (atom (word t) (@cfi_tag t))}
        {smems : axioms sm}
        {smemory_map : Map.mappable sm (@Abstract.dmem_class t ap)}
        {smemory_filter : Filter.filterable sm}

        {sregisters : Type}
        {sr : partial_map sregisters (reg t) (atom (word t) (@cfi_tag t))}
        {sregs : axioms sr}
        {sregs_map : Map.mappable sr (@Abstract.reg_class t ap)}.

Variable valid_jmp : word t -> word t -> bool.

(* Instantiate the symbolic machine with the CFI stuff*)
Definition sym_params := SymbolicCFI.sym_cfi valid_jmp.

Variable atable : list (Abstract.syscall t).
Variable stable : list (@Symbolic.syscall t sym_params).

(*Probably not needed here*)
Definition amachine := Abstract.abstract_cfi_machine atable valid_jmp.
Definition smachine := SymbolicCFI.symbolic_cfi_machine stable.

(*Refinement related definitions*)
Definition refine_dmemory (admem : Abstract.dmemory t)
                          (smem : smemory) :=
  forall w (x : word t),
    get smem w = Some x@DATA <->
    get admem w = Some x. 

Definition refine_imemory (aimem : Abstract.imemory t)
                          (smem : smemory) :=
  forall w x,
    (exists id, get smem w = Some x@(INSTR id)) <->
    get aimem w = Some x.

Definition refine_registers (areg : Abstract.registers t)
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

Definition refine_state (ast : Abstract.state t)
                        (sst : @Symbolic.state t sym_params) :=
  let '(imem, dmem, aregs, apc, cont) := ast in
  let '(Symbolic.State smem sregs spc@tpc _) := sst in
  refine_imemory imem smem /\
  refine_dmemory dmem smem /\
  refine_registers aregs sregs /\
  refine_pc apc (spc@tpc) /\ (* not requiring anything about tpc? *)
  forall i ti,
    get smem spc = Some i@ti ->
    (cont = true <->
    (forall src, tpc = INSTR (Some src) ->
       exists dst, ti = INSTR (Some dst) /\ valid_jmp src dst = true)).

Definition refine_syscall acall scall :=
  forall ast sst ares sres,
    refine_state ast sst ->
    acall ast = Some ares ->
    scall sst = Some sres ->
    refine_state ares sres.

Definition syscall_domains
           (atbl : list (Abstract.syscall t))
           (stbl : list (@Symbolic.syscall t sym_params)) : Prop :=
  forall addr,
    (exists acall, Abstract.get_syscall atbl addr = Some acall) <->
    (exists scall, Symbolic.get_syscall stbl addr = Some scall).

Lemma same_domain_total :
  forall atbl stbl,
    syscall_domains atbl stbl ->
    forall addr', Abstract.get_syscall atbl addr' = None <-> 
                  Symbolic.get_syscall stbl addr' = None.
Proof.
  intros atbl stbl SAME addr'.
  assert (ACALL: forall addr'', Abstract.get_syscall atbl addr'' = None \/
                         exists ac, Abstract.get_syscall atbl addr'' = Some ac).
  { intros addr'';
    destruct (Abstract.get_syscall atbl addr'');
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
Definition refine_syscalls 
           (atbl : list (Abstract.syscall t))
           (stbl : list (@Symbolic.syscall t sym_params)) : Prop :=
  syscall_domains atbl stbl /\
  forall addr acall scall,
    Abstract.get_syscall atbl addr = Some acall ->
    Symbolic.get_syscall stbl addr = Some scall ->
    refine_syscall (@Abstract.sem t ap acall)
                   (@Symbolic.sem t sym_params scall).

Hypothesis refine_syscalls_correct : refine_syscalls atable stable.

Hypothesis syscalls_backwards_simulation :
  forall ast sst addr sc sst',
    refine_syscalls atable stable ->
    Symbolic.get_syscall stable addr = Some sc ->
    refine_state ast sst ->
    Symbolic.sem sc sst = Some sst' ->
    exists ac ast',
      Abstract.get_syscall atable addr = Some ac /\
      Abstract.sem ac ast = Some ast' /\
      refine_state ast' sst'.

Hypothesis syscall_sem :
  forall ac ast ast',
    Abstract.sem ac ast = Some ast' ->
       let '(imem,dmem,aregs,pc,b) := ast in
       let '(imem',dmem',aregs',pc',b') := ast' in
         imem = imem' /\ pc' = (pc + Z_to_word 1)%w /\ b' = b.

(*Various hypothesis on how instructions are tagged*)

Hypothesis id_hypothesis :
  forall pc (w : word t) (mem : @Symbolic.memory t sym_params) id, 
    get mem pc = Some w@(INSTR (Some id)) ->
    id = pc.

Hypothesis jump_tagged :
  forall pc i (mem : @Symbolic.memory t sym_params) r itg,
    get mem pc = Some i@(INSTR itg) ->
    decode_instr i = Some (Jump _ r) ->
    itg = Some pc.

Hypothesis jal_tagged :
  forall pc i (mem : @Symbolic.memory t sym_params) r itg,
    get mem pc = Some i@(INSTR itg) ->
    decode_instr i = Some (Jal _ r) ->
    itg = Some pc.

Hypothesis jump_target_tagged :
  forall pc w (mem : @Symbolic.memory t sym_params) i i0 id r reg 
         (tr ti : @Symbolic.tag t sym_params),
    get mem pc = Some i@(INSTR (Some id)) ->
    decode_instr i = Some (Jump _ r) ->
    get reg r = Some w@tr ->
    get mem w = Some i0@ti ->
    ti = INSTR (Some w).

Hypothesis jal_target_tagged :
  forall pc w (mem : @Symbolic.memory t sym_params) i i0 id r reg 
         (tr ti : @Symbolic.tag t sym_params),
    get mem pc = Some i@(INSTR (Some id)) ->
    decode_instr i = Some (Jal _ r) ->
    get reg r = Some w@tr ->
    get mem w = Some i0@ti ->
    Symbolic.get_syscall stable w = None ->
    ti = INSTR (Some w).

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

(*TODO: Syscalls and clean up of this mess*)
Theorem backwards_simulation ast sst sst' :
  refine_state ast sst ->
  Symbolic.step stable sst sst' ->
  exists ast',
    Abstract.step atable valid_jmp ast ast' /\
    refine_state ast' sst'.
Proof.
  intros REF SSTEP.
  destruct ast as [[[[imem dmem] aregs] apc] b].
  destruct b.
  (* Focus 2. *)
  (* inversion SSTEP; subst; *)
  (* destruct REF as [REFI [REFD [REFR [REFPC CORRECTNESS]]]]; *)
  (* destruct (CORRECTNESS i ti PC) as [? ABSURD]; *)
  (* (*unfoldings and case analysis on tags*) *)
  (* repeat ( *)
  (*     match goal with *)
  (*       | [H: refine_pc _ _ |- _] => unfold refine_pc in H; simpl in H *)
  (*       | [H: Symbolic.next_state_pc _ _ _ = _ |- _] => *)
  (*         unfold Symbolic.next_state_pc in H *)
  (*       | [H: Symbolic.next_state_reg _ _ _ _ = _ |- _] => *)
  (*         unfold Symbolic.next_state_reg in H *)
  (*       | [H: Symbolic.next_state_reg_and_pc _ _ _ _ _ = _ |- _] => *)
  (*         unfold Symbolic.next_state_reg_and_pc in H *)
  (*       | [H: Symbolic.next_state _ _ _ = Some _ |- _] => *)
  (*         unfold Symbolic.next_state in H; simpl in H; match_inv *)
  (*     end); subst; assert (false = true); *)
  (* try match goal with *)
  (*     | [H: _ -> false = true |- false = true] => apply H *)
  (* end; *)
  (* repeat match goal with *)
  (*     | [|- forall _, _] => intros *)
  (*     | [H: INSTR _ = INSTR _ |- _] => inversion H; subst; clear H *)
  (*     | [H: DATA = INSTR _ |- _] => inversion H *)
  (*     | [|- exists _, _] => eexists; eauto *)
  (* end; try discriminate. *)
  (* syscalls stuck *)
(*1st case*)
  - inversion SSTEP; subst;
    destruct REF as [REFI [REFD [REFR [REFPC CORRECTNESS]]]];
  (*unfoldings and case analysis on tags*)
  repeat (
      match goal with
        | [H: refine_pc _ _ |- _] => unfold refine_pc in H; simpl in H; destruct H as [? ?]
        | [H: Symbolic.next_state_pc _ _ _ = _ |- _] => 
          unfold Symbolic.next_state_pc in H
        | [H: Symbolic.next_state_reg _ _ _ _ = _ |- _] => 
          unfold Symbolic.next_state_reg in H
        | [H: Symbolic.next_state_reg_and_pc _ _ _ _ _ = _ |- _] => 
          unfold Symbolic.next_state_reg_and_pc in H
        | [H: Symbolic.next_state _ _ _ = Some _ |- _] =>
          unfold Symbolic.next_state in H; simpl in H; match_inv
      end); subst;
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
  destruct (refine_syscalls_correct) as [DOMAIN SYSCALLREF];
  (* put into context stuff required for syscalls *)
    try
      match goal with
        | [H: decode_instr _ = Some (Jal _ _ ),
           H1: Symbolic.get_syscall _ ?W = Some _
           |- _] =>
          assert (EGETCALL: exists sc, Symbolic.get_syscall stable W = Some sc)
            by (eexists; eauto);
            destruct (DOMAIN W) as [ASDOM SADOM];
            apply SADOM in EGETCALL; destruct EGETCALL;
            assert (REF: refine_state (imem,dmem,aregs,pc,true) (Symbolic.State mem reg pc@tpc int))
                     by (repeat (split; auto));
            destruct (syscalls_backwards_simulation (imem,dmem,aregs,pc,true) 
                                                    (Symbolic.State mem reg pc@tpc int)
                                                    W
                                                    refine_syscalls_correct H1
                                                    REF CALL) as
                [ac [ast' [GETCALL' [CALL' FINALREF]]]];
            destruct ast' as [[[[imem' dmem'] aregs'] apc'] b];
            destruct (syscall_sem ac (imem,dmem,aregs,pc,true) CALL') as 
                [? [? ?]];
            subst
      end;
  (*handle abstract steps*)
  repeat (match goal with 
    | [|- exists _,  _ /\ _] => eexists; split
    | [|- Abstract.step _ _ _ _] => econstructor(eassumption)
    | [H: decode_instr _ = Some (Load _ _ _) |- Abstract.step _ _ _ _] => 
      eapply Abstract.step_load; eauto
    | [H: get ?Mem ?Addr = Some ?V@?TG, H1: refine_imemory _ _, 
       H2: refine_dmemory _ _ 
       |- get _ ?Addr =  _ \/ get _ ?Addr = _] => (*for load*)
      destruct TG; 
        [left; 
          assert(MEMLOAD: exists id, get Mem Addr = Some V@(INSTR id)) 
           by (eexists; eauto); apply H1 in MEMLOAD; eassumption | 
         right; apply H2 in H; eassumption]
    | [H: decode_instr _ = Some (Store _ _ _) |- Abstract.step _ _ _ _] => 
      eapply Abstract.step_store; eauto
    | [H: decode_instr _ = Some (Jump _ _ ) |- Abstract.step _ _ _ _] => 
      eapply Abstract.step_jump; eauto
    | [H: decode_instr _ = Some (Bnz _ _ _) |- Abstract.step _ _ _ _] =>
      eapply Abstract.step_bnz; eauto
    | [H: decode_instr _ = Some (Jal _ _ ), H1: Symbolic.get_syscall _ _ = None 
       |- Abstract.step _ _ _ _] =>
      eapply Abstract.step_jal; eauto
    | [H: decode_instr _ = Some (Jal _ _ ), H1: Symbolic.get_syscall _ _ = Some _
       |- Abstract.step _ _ _ _] =>
      eapply Abstract.step_syscall; eauto
         end);
  unfold refine_state;
  (*handle final state refinement*)
  repeat (match goal with
    | [H: decode_instr _ = Some (Jump _ _) |- refine_state (_,_,_,_, valid_jmp ?Pc ?W) _] =>
      remember (valid_jmp Pc W) as b; destruct b; [left; unfold refine_normal_state; repeat (split; auto) | idtac]
    | [H: false = valid_jmp ?Pc ?W |- refine_state (_,_,_,_, false) _] =>
      idtac
    | [|- _ /\ _] => split; [eauto | idtac]
    | [H: decode_instr _ = Some (Jump _ _) |- Abstract.step _ _ _ (_,_,_,_,false)] =>
      eapply Abstract.step_jump; eauto
    | [H: refine_imemory ?Imem ?Mem |- refine_imemory ?Imem ?Mem] => assumption
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
    try 
      match goal with
        | [H: Symbolic.get_syscall _ ?W = None 
           |- Abstract.get_syscall _ ?W = None] =>
          eapply same_domain_total in DOMAIN; eapply DOMAIN; assumption
      end;
    repeat (
        match goal with
          | [H: INSTR ?V = INSTR ?V |- _] => idtac
          | [H: INSTR _ = INSTR _ |- _] => inversion H; subst
        end);
    try match goal with
          | [H: get ?Mem ?Pc = Some ?I@(INSTR (Some _)), 
             H1: decode_instr ?I = Some (Jump _ ?R), 
             H2: get ?Reg ?R = Some ?W@_,
             H3: get ?Mem ?W = Some _ 
             |- _] =>
               assert (EQ := jump_target_tagged Pc Mem Reg H H1 H2 H3);
               assert (EQ' := jump_tagged Pc Mem H H1); inversion EQ'; subst
          | [H: get ?Mem ?Pc = Some ?I@(INSTR (Some _)), 
             H1: decode_instr ?I = Some (Jal _ ?R), 
             H2: get ?Reg ?R = Some ?W@_,
             H3: get ?Mem ?W = Some _,
             H4: Symbolic.get_syscall stable ?W = None
             |- _] =>
               assert (EQ := jal_target_tagged Pc Mem Reg H H1 H2 H3 H4);
               assert (EQ' := jal_tagged Pc Mem H H1); inversion EQ'; subst
        end;
   try 
     match goal with
       | [|- exists _, INSTR (Some ?W) = INSTR _ /\ valid_jmp _ _ = true] =>
         exists W; split; auto
       | [H: forall _, INSTR (Some ?W) = INSTR (Some _) -> _ 
                              |- valid_jmp _ _ = true] =>
         assert (TRUE: INSTR (Some W) = INSTR (Some W)) by reflexivity;
         destruct (H W TRUE) as [dst [TI VALID]]; inversion TI; auto
     end. 
    (*more system calls*)
Admitted.
(*
    { eapply Abstract.step_jal; eauto. }
    { simpl.
      split; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      split; simpl; eauto.
      intros i' ti GET.
 destruct ti.
    + assert (EQ := jal_tagged pc mem PC INST).
      apply REFI; eexists; eauto.
    + simpl in ALLOWED; match_inv.
    } 
    destruct sst' as [mem' reg' [pc' tpc'] int'].
    destruct FINALREF as [REFI' [REFD' [REFR' [REFPC' CORRECTNESS']]]].
    repeat(split; auto).
    (*syscall correctness*)
     (*not sure if provable right now*)
*)
    
Definition untag_atom (a : atom (word t) (@cfi_tag t)) := common.val a.

Lemma reg_refinement_preserved_by_equiv : 
  forall areg reg reg',
    refine_registers areg reg ->
    SymbolicCFI.equiv reg reg' ->
    exists areg',
      refine_registers areg' reg'.
Proof.
  intros areg reg reg' REF EQUIV.
  unfold SymbolicCFI.equiv in EQUIV.
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
    SymbolicCFI.equiv mem mem' ->
    refine_imemory imem mem'.
Proof.
  intros imem mem mem' REF EQUIV.
  unfold SymbolicCFI.equiv in EQUIV.
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
    SymbolicCFI.equiv mem mem' -> 
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
    SymbolicCFI.equiv mem mem' -> 
    refine_dmemory dmem' mem' ->
    same_domain dmem dmem'.
Proof.
  intros dmem dmem' mem mem' REF EQUIV REF'.
  assert (DOMAINMM' := SymbolicCFI.equiv_same_domain EQUIV).
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

Lemma reg_domain_preserved_by_equiv :
  forall areg areg' reg reg',
    refine_registers areg reg ->
    SymbolicCFI.equiv reg reg' -> 
    refine_registers areg' reg' ->
    same_domain areg areg'.
Proof.
Admitted.

Theorem backwards_simulation_attacker ast sst sst' :
  refine_state ast sst ->
  SymbolicCFI.step_a sst sst' ->
  exists ast',
    Abstract.step_a ast ast' /\
    refine_state ast' sst'.
Proof.
  intros REF SSTEP.
  destruct ast as [[[[imem dmem] aregs] apc] b].
  destruct b; inversion SSTEP; subst;
  unfold refine_state in REF; 
  destruct REF as [REFI [REFD [REFR [REFPC CORRECTNESS]]]];
  unfold refine_pc in REFPC; simpl in REFPC; destruct REFPC as [? ?]; subst.
  - destruct (reg_refinement_preserved_by_equiv REFR REQUIV) as [aregs' REFR'];
    assert (REFI' := imem_refinement_preserved_by_equiv REFI MEQUIV);
    destruct (dmem_refinement_preserved_by_equiv REFD MEQUIV) as [dmem' REFD'];
    assert (DOMAINM := dmem_domain_preserved_by_equiv REFD MEQUIV REFD').
    assert (DOMAINR := reg_domain_preserved_by_equiv REFR REQUIV REFR').
    assert (EFETCH : exists id, get mem pc = Some i@(INSTR id)) by (eexists; eauto);
    apply REFI in EFETCH;
    exists (imem, dmem', aregs', pc, true).
    split; [econstructor(eauto) | repeat (split; auto)].
    intros ? src TAG.
    unfold SymbolicCFI.equiv in MEQUIV.
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
  - unfold SymbolicCFI.no_violation in NOV. 
    destruct (get mem pc) eqn:GET.
    * destruct a as [av atg]. inversion FETCH; subst.
      destruct (CORRECTNESS i (INSTR id) GET) as [? CONTRA].
      assert (HYPOTHESIS: (forall src : word t,
            tpc = INSTR (Some src) ->
            exists dst : word t,
              INSTR id = INSTR (Some dst) /\ valid_jmp src dst = true)).
      { intros src TPC. eapply NOV; eauto. }
      apply CONTRA in HYPOTHESIS. discriminate.
    * congruence.
Qed.

Lemma arith : forall w, (w+1)%w = w -> False.
Admitted.

Lemma new_assumption : forall ast ast' cst cst',
    Abstract.step atable valid_jmp ast ast' ->
    Abstract.step_a ast ast' ->
    refine_state ast cst ->
    refine_state ast' cst' ->
    SymbolicCFI.step_a cst cst' ->
    Symbolic.step stable cst cst'.
Proof.
  intros ast ast' cst cst' ASTEP ASTEPA REF REF' STEPA.
  inversion ASTEPA; subst.
  inversion ASTEP;
  try match goal with
    | [H: (pc + 1)%w = pc |- _] => apply arith in H; inversion H
  end. 
  (* jump case *)
  subst.
  destruct cst as [cmem creg [cpc tpc] int], cst' as [cmem' creg' [cpc' tpc'] int'].
  (* destruct STEPA; subst. *)
  destruct REF as [REFI [REFD [REFR [REFPC CORRECTNESS]]]].
  destruct REF' as [REFI' [REFD' [REFR' [REFPC' ?]]]].
  unfold refine_pc in REFPC. simpl in REFPC. destruct REFPC as [? TPC]; subst.
  apply REFR in RW. destruct RW as [ut RW].
  (*show that it's the same instr*)
  apply REFI in FETCH0. destruct FETCH0 as [id' FETCH0].
  eapply Symbolic.step_jump. 
  - eauto.
  - eauto.
  - eauto.
  - eauto.
  - unfold Symbolic.next_state_pc. unfold Symbolic.next_state.
    simpl.
    (*jump instr will have Some id*)
    assert (TGID := jump_tagged cpc cmem FETCH0 INST). subst.
    destruct TPC; subst.
    { (*case the pc on the tag is DATA*)
      simpl.
      Admitted.

(*This is a helper lemma to instantiate CFI refinement*)
Lemma contra : forall si sj,
                 SymbolicCFI.ssucc si sj = false ->
                 Symbolic.step stable si sj ->
                 SymbolicCFI.step_a si sj ->
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
   unfold SymbolicCFI.ssucc in SUCC; simpl in SUCC;
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
Admitted.
  




End Refinement.

End RefinementAS.
