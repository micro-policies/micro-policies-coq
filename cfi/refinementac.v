Require Import Coq.Lists.List NPeano Arith Bool.
Require Import common utils.
Require Import cfi.abstract.
Require Import concrete.concrete exec.
Require Import cfi.concrete_kernel.
Require Import cfi.concrete_cfi.
Require Import cfi.fault_handler_spec.
Require Import cfi.cfi_refinement.
Require Import cfi.cfi.

Open Scope nat_scope.

Set Implicit Arguments.

Import ListNotations.

Section Refinement.

Context {mt : machine_types}
        {ops : machine_ops mt}
        {opss : machine_ops_spec ops}
        {ap : Abstract.abstract_params mt}
        {aps : Abstract.params_spec ap}
        {cp : Concrete.concrete_params mt}
        {cps : Concrete.params_spec cp}.

Variable cfg : cfg_type. (*cfg in form of list of edges*)
Variable valid_jmp : word mt -> word mt -> bool.

Variable table : list (Abstract.syscall mt).

Definition amachine := Abstract.abstract_cfi_machine table valid_jmp.
Definition cmachine := concrete_cfi_machine ops valid_jmp masks.

Definition refine_dmemory (admem : Abstract.dmemory mt) (cmem : Concrete.memory mt) :=
  forall w x,
    Concrete.get_mem cmem w = Some x@(tag_to_word (USER DATA)) <->
    Abstract.get_dmem admem w = Some x.

Definition refine_imemory (aimem : Abstract.imemory mt) (cmem : Concrete.memory mt) :=
  forall w x it,
    Concrete.get_mem cmem w = Some x@(tag_to_word (USER (INSTR it))) <->
    Abstract.get_imem aimem w = Some x.

Definition refine_registers (areg : Abstract.registers mt) (creg : Concrete.registers mt) :=
  forall n x,
    Concrete.get_reg creg n = x@(tag_to_word (USER DATA)) <->
    Abstract.get_reg areg n = Some x.

(* not syscall or kernel*)
Let is_user_pc_tag (t : word mt) := concrete_cfi.is_user_tag ops t.

Let in_kernel st :=
  let pct := Concrete.tag (Concrete.pc st) in
  Concrete.is_kernel_tag _ pct
                         || (pct =? tag_to_word (USER (INSTR SYSCALL)))%word.
Hint Unfold in_kernel.

Let in_user st :=
  let pct := Concrete.tag (Concrete.pc st) in
  is_user_pc_tag pct.
Hint Unfold in_user.

Lemma in_user_is_user_pc_tag st :
  in_user st = true ->
  is_user_pc_tag (Concrete.tag (Concrete.pc st)) = true.
Proof.
  unfold in_user, is_user_pc_tag. auto.
Qed.

Definition cache_correct cache :=
  forall mvec rvec,
    is_user_pc_tag (Concrete.ctpc mvec) = true -> (*can change this*)
    Concrete.cache_lookup ops cache masks mvec = Some rvec -> chandler cfg mvec = Some rvec.

Definition in_mvec addr := In addr (Concrete.mvec_fields _).

Definition mvec_in_kernel cmem :=
  forall addr,
    in_mvec addr ->
    exists w, Concrete.get_mem cmem addr = Some w@(tag_to_word KERNEL).

Hypothesis kernel_tag_correct :
  Concrete.TKernel = tag_to_word KERNEL.

Lemma store_mvec_mvec_in_kernel cmem cmem' mvec :
  Concrete.store_mvec ops cmem mvec = Some cmem' ->
  mvec_in_kernel cmem'.
Proof.
  unfold Concrete.store_mvec, mvec_in_kernel, in_mvec.
  intros H addr IN.
  rewrite <- kernel_tag_correct in *.
  destruct (PartMaps.get_upd_list_in (Concrete.mem_axioms (t := mt)) _ _ _ H IN)
    as (v' & IN' & GET).
  rewrite GET.
  simpl in IN'.
  repeat match goal with
  | H : _ \/ _ |- _ => destruct H as [E | ?]; [inv E|]
  | H : False |- _ => destruct H
  end; eauto.
Qed.

Lemma mvec_in_kernel_store_mvec cmem mvec :
  mvec_in_kernel cmem ->
  exists cmem',
    Concrete.store_mvec ops cmem mvec = Some cmem'.
Proof.
  unfold mvec_in_kernel, in_mvec, Concrete.mvec_fields, Concrete.store_mvec.
  intros DEF.
  eapply (PartMaps.upd_list_defined (Concrete.mem_axioms (t := mt))).
  simpl map. intros addr IN.
  apply DEF in IN.
  destruct IN.
  eauto.
Qed.

Definition ra_in_user creg :=
  exists x, Concrete.get_reg creg ra = x@(tag_to_word (USER DATA)). 
Hint Unfold ra_in_user.

(* CH: kernel_invariant only holds when kernel starts executing, can
   be broken during kernel execution, but has to be restored before
   returning to user mode. It doesn't necessarily have to hold at all
   intermediate kernel steps. Right? *)
(* CH: I find the way the "kernel invariant" is stated rather
   indirect. Is there no direct way to define this? *)
(* AAA: We need to add the cache as an argument here, since we don't
   assume anything about ground rules right now *)

Record kernel_invariant : Type := {
  kernel_invariant_statement :> Concrete.memory mt ->
                                Concrete.registers mt ->
                                Concrete.rules (word mt) -> Prop;

  kernel_invariant_upd_mem :
    forall regs mem1 mem2 cache addr w1 w2
           (KINV : kernel_invariant_statement mem1 regs cache)
           (GET : Concrete.get_mem mem1 addr = Some w1@(tag_to_word (USER DATA)))
           (UPD : Concrete.upd_mem mem1 addr w2 = Some mem2),
      kernel_invariant_statement mem2 regs cache;

  kernel_invariant_upd_reg :
    forall mem regs cache r w1 w2
           (KINV : kernel_invariant_statement mem regs cache)
           (GET : Concrete.get_reg regs r = w1@(tag_to_word (USER DATA))),
      kernel_invariant_statement mem (Concrete.upd_reg regs r w2@(tag_to_word (USER DATA))) cache;

  kernel_invariant_store_mvec :
    forall mem mem' mvec regs cache
           (KINV : kernel_invariant_statement mem regs cache)
           (MVEC : Concrete.store_mvec ops mem mvec = Some mem'),
      kernel_invariant_statement mem' regs cache
}.

Hint Resolve kernel_invariant_upd_mem.
Hint Resolve kernel_invariant_upd_reg.
Hint Resolve kernel_invariant_store_mvec.

Variable ki : kernel_invariant.

Lemma is_user_pc_tag_is_kernel_tag tg :
  is_user_pc_tag tg = true -> Concrete.is_kernel_tag _ tg = false.
Proof.
  unfold is_user_pc_tag, Concrete.is_kernel_tag, is_user_tag.
  remember (word_to_tag tg) as tag. destruct tag.
  - destruct t.
    + intros.  rewrite kernel_tag_correct.
      destruct (eq_wordP tg (tag_to_word KERNEL)) as [CONTRA | TRUE]; subst;
      [ rewrite tag_to_word_to_tag in Heqtag; inversion Heqtag | reflexivity].
    + intro CONTRA; inversion CONTRA.
    + intro CONTRA; inversion CONTRA.
  - intro CONTRA; inversion CONTRA.
Qed.
  
Lemma in_user_in_kernel :
  forall st, in_user st = true -> in_kernel st = false.
Proof.
  unfold in_kernel.
  intros st H.
  rewrite orb_false_iff. 
  apply in_user_is_user_pc_tag in H.
  split.
  * (*pc tag*)
    destruct (is_user_pc_tag_is_kernel_tag (Concrete.tag (Concrete.pc st)) H); reflexivity. 
  * unfold is_user_pc_tag in H. unfold is_user_tag in H.
    destruct (eq_wordP (Concrete.tag (Concrete.pc st)) (tag_to_word KERNEL)) as [CONTRA | ?].
    - rewrite CONTRA in H;
      rewrite tag_to_word_to_tag in H; inversion H.
    - destruct (eq_wordP (Concrete.tag (Concrete.pc st)) (tag_to_word (USER (INSTR SYSCALL)))) as [CONTRA | ?].
      + rewrite CONTRA in H. rewrite tag_to_word_to_tag in H; inversion H.
      + reflexivity.
Qed.

Definition wf_entry_points cmem :=
  forall addr,
    (exists sc, Abstract.get_syscall table addr = Some sc) <->
    (exists w, Concrete.get_mem cmem addr = Some w@(tag_to_word ENTRY)).

(* CH: This mixes the refinement relation with invariants on the
       concrete state, while I see them as two separate concepts *)
Definition refine_user_state (st : Abstract.state mt) (st' : Concrete.state mt) :=
  in_user st' = true /\
  let '(imem,dmem,regs,pc,_) := st in
  let 'Concrete.mkState mem' regs' cache pc'@tpc epc := st' in
  refine_imemory imem mem' /\
  refine_dmemory dmem mem' /\
  refine_registers regs regs' /\
  cache_correct cache /\
  mvec_in_kernel mem' /\
  ra_in_user regs' /\
  wf_entry_points mem' /\
  ki mem' regs' cache /\
  pc = pc'.

Definition kernel_user_exec kst st : Prop :=
  exec_until (Concrete.step _ masks)
             (fun s => in_user s = true)
             (fun s => in_kernel s = false)
             kst st.

Definition refine_kernel_state (st : @state mt amachine) (st' : @state mt cmachine) :=
  in_kernel st' = true /\
  exists (ust : @state mt cmachine), 
    in_user ust = true /\
    exists kst, cfi_step cmachine ust kst /\ 
                restricted_exec (fun s s' => cfi_step cmachine s s') (fun s => in_kernel s = true) kst st' /\
                refine_user_state st ust.

Inductive jump_or_jal : Type :=
  | jump
  | jal
  | nothing.

Definition nfields (op : opcode) : option (nat * nat * jump_or_jal) :=
  match op with
  | NOP => Some (0, 0, nothing)
  | CONST => Some (1, 1, nothing)
  | MOV => Some (2, 1, nothing)
  | BINOP => Some (3, 1, nothing)
  | LOAD => Some (3, 1, nothing)
  | STORE => Some (3, 1, nothing)
  | JUMP => Some (1, 0, jump)
  | BNZ => Some (1, 0, nothing)
  | JAL => Some (2, 1, jal)
  | _ => None
  end.

Definition user_mvec_rvec (ns : option (nat * nat * jump_or_jal))
                          (mvec : Concrete.MVec (word mt))
                          (rvec : Concrete.RVec (word mt)) : Prop :=
  match ns with
  | Some (n, m, b) =>
    is_user_pc_tag (Concrete.ctpc mvec) = true /\
    match b with
      | jump => Concrete.ctrpc rvec = Concrete.cti mvec /\ 
                exists n, Concrete.cti mvec = tag_to_word (USER (INSTR (NODE n)))
      | jal => Concrete.ctrpc rvec = Concrete.cti mvec /\
               Concrete.cti mvec = tag_to_word (USER (INSTR SYSCALL)) \/ 
               exists n, Concrete.cti mvec = tag_to_word (USER (INSTR NODE n)))
      | nothing => Conctrete.ctrpc rvec = tag_to_word (USER DATA) /\
                   Concrete.cti mvec = tag_to_word (USER (INSTR NONE))
      end /\
    match n with
      | 1 | 2 | 3 => exists cft, Concrete.ct1 mvec = tag_to_word (USER cft)
      | _ => True
    end /\
    match n with
      | 2 | 3 => exists cft, Concrete.ct2 mvec = tag_to_word (USER cft)
      | _ => True
    end /\
    match n with 
      | 3 => exists 

    match b with
    | true => Concrete.cti mvec
    | false => tag_to_word (USER DATA)
    end /\
    Concrete.cti mvec = tag_to_word USER /\
    match n with
    | 1 | 2 | 3 => Concrete.ct1 mvec = tag_to_word USER
    | _ => True
    end /\
    match n with
    | 2 | 3 => Concrete.ct2 mvec = tag_to_word USER
    | _ => True
    end /\
    match n with
    | 3 => Concrete.ct3 mvec = tag_to_word USER
    | _ => True
    end /\
    match m with
    | 1 => Concrete.ctr rvec = tag_to_word USER
    | _ => True
    end
  | None => False
  end.

Lemma user_chandler_inv :
  forall mvec rvec (H : chandler mvec = Some rvec) (op : opcode),
    Concrete.cop mvec = op_to_word op ->
    user_mvec_rvec (nfields op) mvec rvec.
Proof.
  intros.
  unfold chandler, cmvec_to_mvec, handler, srule_denote in *.
  match_inv.
  simpl in *. subst.
  rewrite op_to_wordK in H. inversion H. subst op0. clear H.
  unfold user_mvec_rvec, is_user_pc_tag. simpl.
  repeat match goal with
  | H : word_to_tag _ = Some _ |- _ =>
    apply word_to_tag_to_word in H;
    rewrite <- H in *
  end.
  destruct op; simpl in *;
  repeat match goal with
  | H : _ && _ = true |- _ =>
    rewrite andb_true_iff in H;
    destruct H
  | H : _ || _ = true |- _ =>
    rewrite orb_true_iff in H;
    destruct H
  end;
  match_inv; try discriminate;
  repeat match goal with
  | |- context[(?X =? ?X)%word] =>
    rewrite eqb_refl; try apply eq_wordP; simpl
  | |- context[?X || true = true] =>
    rewrite orb_true_r
  end; auto 10.
Qed.












Hypothesis backwards_refinement_single : 
  forall ast cst cst',
    refine_state ast cst ->
    cfi_step cmachine cst cst' ->
    exists ast', singlestep amachine ast ast' /\ refine_state ast' cst'.

Program Instance AC_refinement : machine_refinement amachine cmachine:=
{| refine_state := refine_state
|}.
Next Obligation.
  Proof. eapply backwards_refinement_single; eauto. Qed.

Lemma backwards_refinement_user_normal : 
  forall (ast : @state mt amachine) (cst cst' : @state mt cmachine),
    in_user cst = true ->
    in_user cst' = true ->
    refine_state ast cst ->
    step cst cst' ->
    exists ast', step ast ast' /\ refine_state ast' cst'.
Admitted.

Lemma user_refine_pc (ast : @state mt amachine) (cst : @state mt cmachine) :
  refine_state ast cst ->
  in_user cst = true ->
  get_pc ast = get_pc cst.
Proof.
  intros REF USER.
  unfold refine_state in REF.
  remember cst as cst'.
  destruct ast as [[[[aimem admem] aregs] apc] ?], cst' as [cmem cregs cache [cpc cpct] cepc]. simpl.
  destruct REF as (? & ? & ? & ? & ? & ? & ? & ? & REF_PC).
  destruct REF_PC as [[? PCEQ] | CONTRA].
  - assumption.
  - assert (KERNEL: in_kernel cst = true). 
    { unfold in_kernel. rewrite orb_true_iff. left. 
      destruct cst as [cmem' cregs' cache' [cpc' cpct'] cepc']. inversion Heqcst'; subst. apply CONTRA.
    }
    rewrite Heqcst' in USER.
    apply in_user_in_kernel in USER. congruence.
Qed.

Lemma word_contra w : w = (w + Z_to_word 1)%word -> False.
Admitted.


(*Lemma valid_pcs st st' :
  Concrete.step _ masks st st' ->
  cache_correct (Concrete.cache st) ->
  in_user st = true ->
  let pct := Concrete.tag (Concrete.pc st') in
  ((pct =? tag_to_word USER) ||
   (pct =? tag_to_word CALL) ||
   (pct =? tag_to_word KERNEL))%word = true.
Proof.
  intros STEP CACHE INUSER. simpl.
  inv STEP;
  unfold Concrete.next_state_reg, Concrete.next_state_reg_and_pc,
         Concrete.next_state_pc, Concrete.next_state,
         Concrete.miss_state in *;
  simpl in *;

  match_inv;

  match goal with
  | LOOKUP : Concrete.cache_lookup _ _ _ ?mvec = Some ?rvec,
    PC : Concrete.get_mem _ _ = Some ?i@_,
    INST : decode_instr ?i = Some _ |- _ =>
    unfold in_user in INUSER; simpl in INUSER; rewrite PC in INUSER;
    let cache_hit := constr:(CACHE mvec rvec INUSER LOOKUP) in
    let all_user := constr:(user_chandler_inv _ cache_hit _ eq_refl) in
    try solve [destruct all_user];
    destruct all_user as (? & ? & ? & ? & ? & ? & ?);
    destruct rvec; subst mvec; simpl in *; subst;
    repeat rewrite tag_to_word_eq; reflexivity
  | _ =>
    simpl; rewrite kernel_tag_correct in *;
    repeat rewrite tag_to_word_eq; reflexivity
  end.*)


(* XXX : Handler behavior? 
Definition nfields (op : opcode) : option (nat * nat * bool) :=
  match op with
  | NOP => Some (0, 0, false)
  | CONST => Some (1, 1, false)
  | MOV => Some (2, 1, false)
  | BINOP => Some (3, 1, false)
  | LOAD => Some (3, 1, false)
  | STORE => Some (3, 1, false)
  | JUMP => Some (1, 0, false)
  | BNZ => Some (1, 0, false)
  | JAL => Some (2, 1, true)
  | _ => None
  end.

Definition user_mvec_rvec (ns : option (nat * nat * bool))
                          (mvec : Concrete.MVec (word mt))
                          (rvec : Concrete.RVec (word mt)) : Prop :=
  match ns with
  | Some (n, m, b) =>
    is_user_pc_tag (Concrete.ctpc mvec) = true /\
    Concrete.ctrpc rvec =
    match b with
    | true => tag_to_word CALL
    | false => tag_to_word USER
    end /\
    Concrete.cti mvec = tag_to_word USER /\
    match n with
    | 1 | 2 | 3 => Concrete.ct1 mvec = tag_to_word USER
    | _ => True
    end /\
    match n with
    | 2 | 3 => Concrete.ct2 mvec = tag_to_word USER
    | _ => True
    end /\
    match n with
    | 3 => Concrete.ct3 mvec = tag_to_word USER
    | _ => True
    end /\
    match m with
    | 1 => Concrete.ctr rvec = tag_to_word USER
    | _ => True
    end
  | None => False
  end.

Lemma user_chandler_inv :
  forall mvec rvec (H : chandler mvec = Some rvec) (op : opcode),
    Concrete.cop mvec = op_to_word op ->
    user_mvec_rvec (nfields op) mvec rvec.
Proof.

*)

Lemma jump_lookup cache (tpc ti t1 t2 t3 tr : word mt) : 
  cache_correct cache ->
  Concrete.cache_lookup ops cache masks (Concrete.mkMVec (op_to_word JUMP) tpc ti t1 t2 t3) = 
  Some (Concrete.mkRVec ti tr) \/
  Concrete.cache_lookup ops cache masks (Concrete.mkMVec (op_to_word JUMP) tpc ti t1 t2 t3) = None.
Proof. Admitted.

Lemma jump_pctag_hit mem reg cache pc tpc epc pc' tpc' i ti r t1 : 
  is_user_pc_tag tpc = true -> 
  cache_correct cache ->
  Concrete.get_mem mem pc = Some i@ti ->
  decode_instr i = Some (Jump mt r) -> 
  Concrete.get_reg reg r = pc'@t1 ->
  Concrete.step ops masks (Concrete.mkState mem reg cache pc@tpc epc) 
                (Concrete.mkState mem reg cache pc'@tpc' epc) ->
  tpc' = ti \/ tpc' = Concrete.TKernel.
Proof.
  intros USER CACHE FETCH DECODE REG STEP.
  inv STEP; inversion ST; subst; rewrite PC in FETCH; inversion FETCH; subst ti i;
  rewrite INST in DECODE; inversion DECODE. subst r.
  unfold Concrete.next_state_reg, Concrete.next_state_reg_and_pc,
             Concrete.next_state_pc, Concrete.next_state in NEXT. simpl in NEXT.
  match_inv.
Admitted.

Lemma cfg_equiv0 (asi : @state mt amachine) (csi csj : @state mt cmachine) :
  refine_state asi csi ->
  refine_state asi csj ->
  step csi csj ->
  succ csi csj = true \/ (step csj csj /\ step asi asi).
Proof.
  intros REFI REFJ CSTEP.
  remember (in_user csi) as useri.
  remember (in_user csj) as userj.
  destruct useri. 
  - (*csi in user mode*)
    destruct userj.
    + (*csj in user mode*)
      right.
      symmetry in Hequseri, Hequserj.
      destruct (backwards_refinement_user_normal asi Hequseri Hequserj REFI CSTEP) as [asi' [ASTEP REF']].
      apply refine_unique with (asi:=asi) in REF'; auto; subst asi'. split.
      assert (PCI : get_pc asi = get_pc csi) by (eapply user_refine_pc; eauto).
      assert (PCJ : get_pc asi = get_pc csj) by (eapply user_refine_pc; eauto).
      rewrite PCI in PCJ. clear PCI.
      clear Hequseri.
      (*inv CSTEP.
      unfold Concrete.next_state_reg, Concrete.next_state_reg_and_pc,
             Concrete.next_state_pc, Concrete.next_state in NEXT;
      match_inv. simpl in PCJ. apply word_contra in PCJ. destruct PCJ.
      unfold Concrete.miss_state in NEXT. match_inv.
      simpl in PCJ. subst.  unfold in_user in Hequserj. unfold is_user_pc_tag in Hequserj. unfold is_user_tag in Hequserj*)
      inversion CSTEP; subst.
      Focus 7. 
      unfold Concrete.next_state_reg, Concrete.next_state_reg_and_pc,
             Concrete.next_state_pc, Concrete.next_state in NEXT;
      match_inv. 
      - (*hit*) 
        simpl in PCJ. subst w. 
      eapply Concrete.step_jump; eauto.
      unfold Concrete.next_state_reg, Concrete.next_state_reg_and_pc,
             Concrete.next_state_pc, Concrete.next_state. simpl.
      destruct asi as [[[[aimem admem] aregs] apc] ?].
      destruct REFJ as (? & ? & ? & CACHE & ? & ? & ? & ? & REF_PC).
      remember (Concrete.mkMVec (op_to_word JUMP) ti ti t1 Concrete.TNone Concrete.TNone) as mvec'.
      remember (Concrete.cache_lookup ops cache masks mvec') as LOOKUP.
      destruct (jump_lookup tpc ti t1 Concrete.TNone Concrete.TNone Concrete.TNone CACHE) as [RVEC | CONTRA].
        + (* csi lookup hit *)
          simpl in Heqo. fold mvec in RVEC. rewrite RVEC in Heqo. inversion Heqo. simpl. 
          destruct (jump_lookup ti ti t1 Concrete.TNone Concrete.TNone Concrete.TNone CACHE) as [RVEC' | RVEC'].
          rewrite RVEC'. simpl. reflexivity.
          rewrite RVEC'. subst r0. simpl in *.

          destruct LOOKUP.
          { (*lookup success*)
      rewrite <- Heqmvec' in RVEC'; rewrite <- HeqLOOKUP in RVEC';
      inversion RVEC';
      simpl. reflexivity.
      
     
      eapply jump_lookup with (tpc := tpc) (ti := ti) (t1 := t1) (t2 := Concrete.TNone) (t3 := Concrete.TNone) 
          in CACHE; eauto.
      rewrite RVEC in Heqo.
        


      inv CSTEP;
      unfold Concrete.next_state_reg, Concrete.next_state_reg_and_pc,
             Concrete.next_state_pc, Concrete.next_state in NEXT;
      match_inv; 
      repeat match goal with 
        | H : get_pc _ = get_pc _ |- _  => simpl in H
        | H : ?pc = (?pc + Z_to_word 1)%word |- _ => apply word_contra in H; destruct H
        | H : Concrete.miss_state _ _ _ = Some ?cst |-_ => unfold Concrete.miss_state in H; match_inv;
                                                           simpl in H; inversion H; subst cst
        | H : in_user _ = true |- _ => unfold in_user in H; simpl in H; unfold is_user_pc_tag in H;
                                       unfold is_user_tag in H
        | H : match _ with _ => _ end = true |- _ => rewrite kernel_tag_correct in H;
                                                      rewrite tag_to_word_to_tag in H
        | H : false = true |- _ => discriminate
             end.
      (*jump r case*)
      subst w. simpl. eapply Concrete.step_jump; eauto. 
      unfold Concrete.next_state_reg, Concrete.next_state_reg_and_pc,
             Concrete.next_state_pc, Concrete.next_state. 

   
Lemma refine_in_kernel (asi : @state mt amachine) (csi csj : @state mt cmachine) :
  refine_state asi csi ->
  refine_state asi csj ->
  step csi csj ->
  Concrete.is_kernel_tag ops (Concrete.tag (Concrete.pc csi)) = true \/
  Concrete.is_kernel_tag ops (Concrete.tag (Concrete.pc csj)) = true \/
  (
Proof.
  intros REFI REFJ STEP.
  remember (in_user csi) as useri.
  remember (in_user csj) as userj.
  destruct useri.
  - destruct userj.
    + symmetry in Hequseri.
      assert (PCI : get_pc asi = get_pc csi) by (eapply user_refine_pc; eauto).
      assert (PCJ : get_pc asi = get_pc csj) by (eapply user_refine_pc; eauto).
      rewrite PCI in PCJ. clear PCI.
      inv STEP;
      unfold Concrete.next_state_reg, Concrete.next_state_reg_and_pc,
             Concrete.next_state_pc, Concrete.next_state in NEXT;
      match_inv; 
      repeat match goal with 
        | H : get_pc _ = get_pc _ |- _  => simpl in H
        | H : ?pc = (?pc + Z_to_word 1)%word |- _ => apply word_contra in H; destruct H
        | H : Concrete.miss_state _ _ _ = Some ?cst |-_ => unfold Concrete.miss_state in H; match_inv;
                                                           simpl in H; inversion H; subst cst
        | H : true = in_user _ |- _ => unfold in_user in H; simpl in H; unfold is_user_pc_tag in H;
                                       unfold is_user_tag in H
        | H : true = match _ with _ => _ end  |- _ => rewrite kernel_tag_correct in H;
                                                      rewrite tag_to_word_to_tag in H
        | H : true = false |- _ => discriminate
             end. 
      
  end.






intros REF [INUSER INUSER' STEP].
  assert (KER := in_user_in_kernel _ INUSER).
  assert (KER' := in_user_in_kernel _ INUSER').
  destruct ast as [[amem areg] apc].
  inv STEP; simpl in REF;
  destruct REF
    as (_ & ? & REFM & REFR & CACHE & MVEC & RA & WFENTRYPOINTS & KINV);
  subst apc;
  unfold Concrete.next_state_reg, Concrete.next_state_reg_and_pc,
         Concrete.next_state_pc, Concrete.next_state in *;
  simpl in *;
  try rewrite KER in NEXT; simpl in *;

  match_inv;

  match goal with
  | LOOKUP : Concrete.cache_lookup _ _ _ ?mvec = Some ?rvec,
    PC : Concrete.get_mem _ _ = Some ?i@_,
    INST : decode_instr ?i = Some _ |- _ =>
    unfold in_user in INUSER; simpl in INUSER; rewrite PC in INUSER;
    let cache_hit := constr:(CACHE mvec rvec INUSER LOOKUP) in
    let all_user := constr:(user_chandler_inv _ cache_hit _ eq_refl) in
    try solve [destruct all_user];
    destruct all_user as (? & ? & ? & ? & ? & ? & ?);
    destruct rvec; subst mvec; simpl in *; subst
  | _ =>
    (* Solve miss cases *)
    unfold Concrete.miss_state, in_kernel, Concrete.is_kernel_tag in *;
    rewrite orb_false_iff in KER'; destruct KER' as [KER' _];
    match_inv;
    simpl in KER';
    rewrite eqb_refl in KER'; try apply eq_wordP; discriminate
  end;

  repeat match goal with
  | MEM : Concrete.get_mem ?cmem ?addr = Some _ |- _ =>
    match goal with
    | _ : Abstract.get_mem _ addr = Some _ |- _ => fail 1
    | |- _ => idtac
    end;
    pose proof (proj1 (REFM _ _) MEM)
  end;

  try match goal with
  | OLD : Concrete.get_reg ?reg ?r = _
    |- context[Concrete.upd_reg ?reg ?r ?v@_] =>
    (destruct (refine_registers_upd _ v REFR OLD) as (? & ? & ?);
     pose proof (kernel_invariant_upd_reg ki _ _ _ _ v KINV OLD))
    || let op := current_instr_opcode in fail 3 op
  end;

  try match goal with
  | GET : Concrete.get_mem _ ?addr = Some _,
    UPD : Concrete.upd_mem _ ?addr _ = Some _ |- _ =>
    (destruct (refine_memory_upd _ _ REFM GET UPD) as (? & ? & ?);
     pose proof (wf_entry_points_user_upd _ _ WFENTRYPOINTS GET UPD);
     pose proof (mvec_in_kernel_user_upd _ _ MVEC GET UPD))
    || let op := current_instr_opcode in fail 3 op
  end;

  repeat match goal with
  | creg : Concrete.registers mt,
    H : Concrete.get_reg ?creg ?r = _ |- _ =>
    apply REFR in H
  end;


  destruct asi as [[[[aimem admem] aregs] apc] ?], csi as [cmem cregs cache [cpc cpct] cepc],
           csj as [cmem' cregs' cache' [cpc' cpct'] cepc'].
  inv STEP.
  inversion H.
  
  remember (Concrete.is_kernel_tag ops (Concrete.tag (Concrete.pc csi))) as tpc.
  destruct tpc.
  - reflexivity.
  -simpl in REFI.
  


(*
Lemma refine_dmemory_upd admem cmem cmem' addr val w :
  refine_dmemory admem cmem ->
  Concrete.get_mem cmem addr = Some val@(tag_to_word (USER DATA)) ->
  Concrete.upd_mem cmem addr w@(tag_to_word (USER DATA)) = Some cmem' ->
  exists admem',
    Abstract.upd_dmem admem addr w = Some admem' /\
    refine_dmemory admem' cmem'.
Proof.
  intros MEM GET UPD.
  assert (GET' := proj1 (MEM _ _) GET).
  assert (NEW := PartMaps.upd_defined (Abstract.dmem_axioms (t := mt)) _ _ w GET').
  destruct NEW as (amem' & UPD').
  do 2 eexists; eauto.
  intros addr' w'.
  destruct (eq_wordP addr' addr) as [EQ | NEQ]; subst.
  - apply MEM in GET.
    rewrite (PartMaps.get_upd_eq (Concrete.mem_axioms (t := mt)) _ _ _ UPD).
    rewrite (PartMaps.get_upd_eq (Abstract.dmem_axioms (t := mt)) _ _ _ UPD').
    split; congruence.
  - rewrite (PartMaps.get_upd_neq (Abstract.dmem_axioms (t := mt)) _ _ NEQ UPD').
    rewrite (PartMaps.get_upd_neq (Concrete.mem_axioms (t := mt)) _ _ NEQ UPD).
    now apply MEM.
Qed.

Lemma wf_entry_points_user_upd cmem cmem' addr val w :
  wf_entry_points cmem ->
  Concrete.get_mem cmem addr = Some val@(tag_to_word (USER DATA)) ->
  Concrete.upd_mem cmem addr w@(tag_to_word (USER DATA)) = Some cmem' ->
  wf_entry_points cmem'.
Proof.
  unfold wf_entry_points.
  intros WF GET UPD addr'.
  split; intros H.
  - rewrite WF in H.
    destruct H as [w' GET'].
    eexists w'. rewrite <- GET'.
    eapply (PartMaps.get_upd_neq (Concrete.mem_axioms (t := mt))); eauto.
    intros ?. subst addr'.
    assert (EQ : tag_to_word (USER DATA) = tag_to_word ENTRY) by congruence.
    apply tag_to_word_inj in EQ. inversion EQ.
  - destruct H as [w' GET'].
    rewrite WF.
    erewrite (PartMaps.get_upd_neq (Concrete.mem_axioms (t := mt))) in GET'; eauto.
    intros ?. subst addr'.
    erewrite (PartMaps.get_upd_eq (Concrete.mem_axioms (t := mt))) in GET'; eauto.
    assert (EQ : tag_to_word (USER DATA) = tag_to_word ENTRY) by congruence.
    apply tag_to_word_inj in EQ. inversion EQ.
Qed.

Lemma mvec_in_kernel_user_upd cmem cmem' addr val w :
  mvec_in_kernel cmem ->
  Concrete.get_mem cmem addr = Some val@(tag_to_word USER) ->
  Concrete.upd_mem cmem addr w@(tag_to_word USER) = Some cmem' ->
  mvec_in_kernel cmem'.
Proof.
  intros MVEC GET UPD.
  intros addr' H.
  specialize (MVEC addr' H). destruct MVEC as [w' KER].
  assert (NEQ : addr' <> addr).
  { destruct (eq_wordP addr' addr); trivial.
    cut (KERNEL = USER); try discriminate.
    apply tag_to_word_inj; congruence. }
  rewrite (PartMaps.get_upd_neq (Concrete.mem_axioms (t := mt)) _ _ NEQ UPD).
  eauto.
Qed.

Lemma mvec_in_kernel_kernel_upd cmem cmem' addr w :
  mvec_in_kernel cmem ->
  Concrete.upd_mem cmem addr w@Concrete.TKernel = Some cmem' ->
  mvec_in_kernel cmem'.
Proof.
  intros MVEC UPD addr' IN.
  destruct (eq_wordP addr' addr) as [? | NEQ]; subst.
  - rewrite <- kernel_tag_correct.
    erewrite (PartMaps.get_upd_eq (Concrete.mem_axioms (t := mt))); eauto.
  - erewrite (PartMaps.get_upd_neq (Concrete.mem_axioms (t := mt)) _ _ NEQ UPD).
    now apply MVEC.
Qed.

Lemma refine_memory_upd' amem amem' cmem addr w :
  refine_memory amem cmem ->
  Abstract.upd_mem amem addr w = Some amem' ->
  exists cmem',
    Concrete.upd_mem cmem addr w@(tag_to_word USER) = Some cmem' /\
    refine_memory amem' cmem'.
Proof.
  intros MEM UPD.
  destruct (PartMaps.upd_inv (Abstract.mem_axioms (t := mt)) _ _ _ UPD) as [w' GET].
  apply MEM in GET.
  eapply (PartMaps.upd_defined (Concrete.mem_axioms (t := mt))) in GET.
  destruct GET as [cmem' UPD'].
  eexists. split; eauto.
  intros addr' w''.
  destruct (eq_wordP addr' addr) as [EQ | NEQ]; subst.
  - rewrite (PartMaps.get_upd_eq (Concrete.mem_axioms (t := mt)) _ _ _ UPD').
    rewrite (PartMaps.get_upd_eq (Abstract.mem_axioms (t := mt)) _ _ _ UPD).
    split; congruence.
  - rewrite (PartMaps.get_upd_neq (Abstract.mem_axioms (t := mt)) _ _ NEQ UPD).
    rewrite (PartMaps.get_upd_neq (Concrete.mem_axioms (t := mt)) _ _ NEQ UPD').
    now apply MEM.
Qed.

Lemma refine_registers_upd areg creg r val w :
  refine_registers areg creg ->
  Concrete.get_reg creg r = val@(tag_to_word USER) ->
  exists areg',
    Abstract.upd_reg areg r w = Some areg' /\
    refine_registers areg' (Concrete.upd_reg creg r w@(tag_to_word USER)).
Proof.
  intros REG GET.
  assert (GET' := proj1 (REG _ _) GET).
  assert (NEW := PartMaps.upd_defined (Abstract.reg_axioms (t := mt)) _ _ w GET').
  destruct NEW as [areg' UPD].
  eexists. split; eauto.
  intros r' w'.
  destruct (eq_regP r' r) as [EQ | NEQ]; subst.
  - rewrite (TotalMaps.get_upd_eq (Concrete.reg_axioms (t := mt))).
    rewrite (PartMaps.get_upd_eq (Abstract.reg_axioms (t := mt)) _ _ _ UPD).
    split; congruence.
  - rewrite (TotalMaps.get_upd_neq (Concrete.reg_axioms (t := mt))); trivial.
    rewrite (PartMaps.get_upd_neq (Abstract.reg_axioms (t := mt)) _ _ NEQ UPD).
    now apply REG.
Qed.

Lemma refine_registers_upd' areg areg' creg r w :
  refine_registers areg creg ->
  Abstract.upd_reg areg r w = Some areg' ->
  refine_registers areg' (Concrete.upd_reg creg r w@(tag_to_word USER)).
Proof.
  intros REF UPD r' w'.
  destruct (eq_regP r' r) as [|NEQ].
  - subst r'.
    rewrite (TotalMaps.get_upd_eq (Concrete.reg_axioms (t := mt))).
    rewrite (PartMaps.get_upd_eq (Abstract.reg_axioms (t := mt)) _ _ _ UPD).
    split; congruence.
  - rewrite (TotalMaps.get_upd_neq (Concrete.reg_axioms (t := mt))); trivial.
    rewrite (PartMaps.get_upd_neq (Abstract.reg_axioms (t := mt)) _ _ NEQ UPD).
    now apply REF.
Qed.

Lemma ra_in_user_upd creg r w :
  ra_in_user creg ->
  ra_in_user (Concrete.upd_reg creg r w@(tag_to_word USER)).
Proof.
  intros (x & H).
  destruct (eq_regP r ra) as [|NEQ]; autounfold.
  - subst r.
    rewrite (TotalMaps.get_upd_eq (Concrete.reg_axioms (t := mt))).
    eauto.
  - rewrite (TotalMaps.get_upd_neq (Concrete.reg_axioms (t := mt))); try congruence.
    eauto.
Qed.

Inductive hit_step cst cst' : Prop :=
| hs_intro (USER : in_user cst = true)
           (USER' : in_user cst' = true)
           (STEP : Concrete.step _ masks cst cst').

Definition kernel_exec kst kst' :=
  restricted_exec (Concrete.step _ masks)
                  (fun s => in_kernel s = true)
                  kst kst'.
Hint Unfold kernel_exec.

Definition kernel_user_exec kst st : Prop :=
  exec_until (Concrete.step _ masks)
             (fun s => in_kernel s = true)
             (fun s => in_kernel s = false)
             kst st.

Inductive miss_step cst cst' : Prop :=
| ks_intro kst
           (USER : in_user cst = true)
           (STEP : Concrete.step _ masks cst kst)
           (EXEC : kernel_user_exec kst cst').

Definition user_step cst cst' :=
  hit_step cst cst' \/ miss_step cst cst'.

Definition nfields (op : opcode) : option (nat * nat * bool) :=
  match op with
  | NOP => Some (0, 0, false)
  | CONST => Some (1, 1, false)
  | MOV => Some (2, 1, false)
  | BINOP => Some (3, 1, false)
  | LOAD => Some (3, 1, false)
  | STORE => Some (3, 1, false)
  | JUMP => Some (1, 0, false)
  | BNZ => Some (1, 0, false)
  | JAL => Some (2, 1, true)
  | _ => None
  end.

Definition user_mvec_rvec (ns : option (nat * nat * bool))
                          (mvec : Concrete.MVec (word mt))
                          (rvec : Concrete.RVec (word mt)) : Prop :=
  match ns with
  | Some (n, m, b) =>
    is_user_pc_tag (Concrete.ctpc mvec) = true /\
    Concrete.ctrpc rvec =
    match b with
    | true => tag_to_word CALL
    | false => tag_to_word USER
    end /\
    Concrete.cti mvec = tag_to_word USER /\
    match n with
    | 1 | 2 | 3 => Concrete.ct1 mvec = tag_to_word USER
    | _ => True
    end /\
    match n with
    | 2 | 3 => Concrete.ct2 mvec = tag_to_word USER
    | _ => True
    end /\
    match n with
    | 3 => Concrete.ct3 mvec = tag_to_word USER
    | _ => True
    end /\
    match m with
    | 1 => Concrete.ctr rvec = tag_to_word USER
    | _ => True
    end
  | None => False
  end.

Lemma user_chandler_inv :
  forall mvec rvec (H : chandler mvec = Some rvec) (op : opcode),
    Concrete.cop mvec = op_to_word op ->
    user_mvec_rvec (nfields op) mvec rvec.
Proof.
  intros.
  unfold chandler, cmvec_to_mvec, handler, srule_denote in *.
  match_inv.
  simpl in *. subst.
  rewrite op_to_wordK in H. inversion H. subst op0. clear H.
  unfold user_mvec_rvec, is_user_pc_tag. simpl.
  repeat match goal with
  | H : word_to_tag _ = Some _ |- _ =>
    apply word_to_tag_to_word in H;
    rewrite <- H in *
  end.
  destruct op; simpl in *;
  repeat match goal with
  | H : _ && _ = true |- _ =>
    rewrite andb_true_iff in H;
    destruct H
  | H : _ || _ = true |- _ =>
    rewrite orb_true_iff in H;
    destruct H
  end;
  match_inv; try discriminate;
  repeat match goal with
  | |- context[(?X =? ?X)%word] =>
    rewrite eqb_refl; try apply eq_wordP; simpl
  | |- context[?X || true = true] =>
    rewrite orb_true_r
  end; auto 10.
Qed.

Lemma valid_pcs st st' :
  Concrete.step _ masks st st' ->
  cache_correct (Concrete.cache st) ->
  in_user st = true ->
  let pct := Concrete.tag (Concrete.pc st') in
  ((pct =? tag_to_word USER) ||
   (pct =? tag_to_word CALL) ||
   (pct =? tag_to_word KERNEL))%word = true.
Proof.
  intros STEP CACHE INUSER. simpl.
  inv STEP;
  unfold Concrete.next_state_reg, Concrete.next_state_reg_and_pc,
         Concrete.next_state_pc, Concrete.next_state,
         Concrete.miss_state in *;
  simpl in *;

  match_inv;

  match goal with
  | LOOKUP : Concrete.cache_lookup _ _ _ ?mvec = Some ?rvec,
    PC : Concrete.get_mem _ _ = Some ?i@_,
    INST : decode_instr ?i = Some _ |- _ =>
    unfold in_user in INUSER; simpl in INUSER; rewrite PC in INUSER;
    let cache_hit := constr:(CACHE mvec rvec INUSER LOOKUP) in
    let all_user := constr:(user_chandler_inv _ cache_hit _ eq_refl) in
    try solve [destruct all_user];
    destruct all_user as (? & ? & ? & ? & ? & ? & ?);
    destruct rvec; subst mvec; simpl in *; subst;
    repeat rewrite tag_to_word_eq; reflexivity
  | _ =>
    simpl; rewrite kernel_tag_correct in *;
    repeat rewrite tag_to_word_eq; reflexivity
  end.
Qed.

Ltac current_instr_opcode :=
  match goal with
  | H : decode_instr _ = Some ?instr |- _ =>
    let op := (eval compute in (opcode_of instr)) in
    op
  end.

Lemma in_user_no_system_call st :
  in_user st = true ->
  Concrete.tag (Concrete.pc st) = tag_to_word CALL ->
  wf_entry_points (Concrete.mem st) ->
  Abstract.get_syscall table (Concrete.val (Concrete.pc st)) = None.
Proof.
  unfold in_user.
  intros INUSER ISCALL WF.
  rewrite ISCALL in INUSER.
  destruct (Abstract.get_syscall table (Concrete.val (Concrete.pc st)))
    as [sc|] eqn:EQ; trivial.
  assert (H := proj1 (WF (Concrete.val (Concrete.pc st))) (ex_intro _ _ EQ)).
  destruct H as (w & EQ'). rewrite EQ' in INUSER.
  now repeat rewrite tag_to_word_eq in INUSER.
Qed.

Lemma hit_simulation ast cst cst' :
  refine_state ast cst ->
  hit_step cst cst' ->
  exists ast',
    Abstract.step table ast ast' /\
    refine_state ast' cst'.
Proof.
  intros REF [INUSER INUSER' STEP].
  assert (KER := in_user_in_kernel _ INUSER).
  assert (KER' := in_user_in_kernel _ INUSER').
  destruct ast as [[amem areg] apc].
  inv STEP; simpl in REF;
  destruct REF
    as (_ & ? & REFM & REFR & CACHE & MVEC & RA & WFENTRYPOINTS & KINV);
  subst apc;
  unfold Concrete.next_state_reg, Concrete.next_state_reg_and_pc,
         Concrete.next_state_pc, Concrete.next_state in *;
  simpl in *;
  try rewrite KER in NEXT; simpl in *;

  match_inv;

  match goal with
  | LOOKUP : Concrete.cache_lookup _ _ _ ?mvec = Some ?rvec,
    PC : Concrete.get_mem _ _ = Some ?i@_,
    INST : decode_instr ?i = Some _ |- _ =>
    unfold in_user in INUSER; simpl in INUSER; rewrite PC in INUSER;
    let cache_hit := constr:(CACHE mvec rvec INUSER LOOKUP) in
    let all_user := constr:(user_chandler_inv _ cache_hit _ eq_refl) in
    try solve [destruct all_user];
    destruct all_user as (? & ? & ? & ? & ? & ? & ?);
    destruct rvec; subst mvec; simpl in *; subst
  | _ =>
    (* Solve miss cases *)
    unfold Concrete.miss_state, in_kernel, Concrete.is_kernel_tag in *;
    rewrite orb_false_iff in KER'; destruct KER' as [KER' _];
    match_inv;
    simpl in KER';
    rewrite eqb_refl in KER'; try apply eq_wordP; discriminate
  end;

  repeat match goal with
  | MEM : Concrete.get_mem ?cmem ?addr = Some _ |- _ =>
    match goal with
    | _ : Abstract.get_mem _ addr = Some _ |- _ => fail 1
    | |- _ => idtac
    end;
    pose proof (proj1 (REFM _ _) MEM)
  end;

  try match goal with
  | OLD : Concrete.get_reg ?reg ?r = _
    |- context[Concrete.upd_reg ?reg ?r ?v@_] =>
    (destruct (refine_registers_upd _ v REFR OLD) as (? & ? & ?);
     pose proof (kernel_invariant_upd_reg ki _ _ _ _ v KINV OLD))
    || let op := current_instr_opcode in fail 3 op
  end;

  try match goal with
  | GET : Concrete.get_mem _ ?addr = Some _,
    UPD : Concrete.upd_mem _ ?addr _ = Some _ |- _ =>
    (destruct (refine_memory_upd _ _ REFM GET UPD) as (? & ? & ?);
     pose proof (wf_entry_points_user_upd _ _ WFENTRYPOINTS GET UPD);
     pose proof (mvec_in_kernel_user_upd _ _ MVEC GET UPD))
    || let op := current_instr_opcode in fail 3 op
  end;

  repeat match goal with
  | creg : Concrete.registers mt,
    H : Concrete.get_reg ?creg ?r = _ |- _ =>
    apply REFR in H
  end;

  try match goal with
  | INST : decode_instr _ = Some (Jal _ _) |- _ =>
    pose proof (in_user_no_system_call _ INUSER' eq_refl WFENTRYPOINTS)
  end;

  solve [eexists; split; (try econstructor (solve [eauto]));
         repeat (split; eauto using ra_in_user_upd)].
Qed.

Lemma initial_handler_state cst kst :
  forall (ISUSER : in_user cst = true)
         (NUSER : is_user_pc_tag (Concrete.tag (Concrete.pc kst)) = false)
         (CACHE : cache_correct (Concrete.cache cst))
         (STEP : Concrete.step _ masks cst kst),
    exists cmem' mvec,
      Concrete.store_mvec ops (Concrete.mem cst) mvec = Some cmem' /\
      kst = Concrete.mkState cmem'
                             (Concrete.regs cst)
                             (Concrete.cache cst)
                             (Concrete.fault_handler_start (t := mt))@Concrete.TKernel
                             (Concrete.pc cst).
Proof.
  intros.
  inv STEP;
  unfold Concrete.next_state_reg, Concrete.next_state_reg_and_pc,
         Concrete.next_state_pc, Concrete.next_state,
         Concrete.miss_state in *;
  match_inv;

  match goal with
  | LOOKUP : Concrete.cache_lookup _ _ _ ?mvec = Some ?rvec,
    PC : Concrete.get_mem _ _ = Some _ |- _ =>
    unfold in_user in ISUSER; simpl in ISUSER; rewrite PC in ISUSER;
    let op := current_instr_opcode in
    let cache_hit := constr:(CACHE mvec rvec ISUSER LOOKUP) in
    let all_user := constr:(user_chandler_inv _ cache_hit _ eq_refl) in
    try solve [destruct all_user];
    destruct all_user as (? & ? & ? & ? & ? & ? & ?);
    destruct rvec; subst mvec; simpl in *; subst;
    unfold in_user, is_user_pc_tag in *; simpl in ISUSER, NUSER;
    try rewrite (eqb_refl _ eq_wordP) in NUSER; simpl in NUSER;
    try rewrite orb_true_r in NUSER;
    congruence
  | _ => solve [eauto]
  end.
Qed.

Definition user_mem_unchanged cmem cmem' :=
  forall addr w,
    Concrete.get_mem cmem addr = Some w@(tag_to_word USER) <->
    Concrete.get_mem cmem' addr = Some w@(tag_to_word USER).

Definition user_regs_unchanged cregs cregs' :=
  forall r w,
    Concrete.get_reg cregs r = w@(tag_to_word USER) <->
    Concrete.get_reg cregs' r = w@(tag_to_word USER).

Hypothesis handler_correct_allowed_case :
  forall mem mem' cmvec crvec reg cache old_pc,
    ki mem reg cache ->
    chandler cmvec = Some crvec ->
    Concrete.store_mvec ops mem cmvec = Some mem' ->
    cache_correct cache ->
    exists st',
      kernel_user_exec
        (Concrete.mkState mem' reg cache
                          (Concrete.fault_handler_start (t := mt))@Concrete.TKernel
                          old_pc)
        st' /\
      cache_correct (Concrete.cache st') /\
      Concrete.cache_lookup _ (Concrete.cache st') masks cmvec = Some crvec /\
      mvec_in_kernel (Concrete.mem st') /\
      user_mem_unchanged mem (Concrete.mem st') /\
      user_regs_unchanged reg (Concrete.regs st') /\
      Concrete.pc st' = old_pc /\
      wf_entry_points (Concrete.mem st') /\
      ki (Concrete.mem st') (Concrete.regs st') (Concrete.cache st').

Hypothesis handler_correct_disallowed_case :
  forall mem mem' cmvec reg cache old_pc st',
    ki mem reg cache ->
    chandler cmvec = None ->
    Concrete.store_mvec ops mem cmvec = Some mem' ->
    in_kernel st' = false ->
    ~ exec (Concrete.step _ masks)
      (Concrete.mkState mem' reg cache
                        (Concrete.fault_handler_start (t := mt))@Concrete.TKernel
                        old_pc)
      st'.

Hypothesis syscalls_correct_allowed_case :
  forall amem areg apc amem' areg' apc' cmem creg cache old_pc epc addr sc,
    ki cmem creg cache ->
    refine_memory amem cmem ->
    refine_registers areg creg ->
    cache_correct cache ->
    mvec_in_kernel cmem ->
    wf_entry_points cmem ->
    Abstract.get_syscall table addr = Some sc ->
    Abstract.sem sc (amem, areg, apc) = Some (amem', areg', apc') ->
    exists cmem' creg' cache' epc',
      kernel_user_exec (Concrete.mkState cmem
                                         (Concrete.upd_reg creg ra
                                                           (old_pc + Z_to_word 1)%word@(tag_to_word USER))
                                         cache
                                         addr@(tag_to_word CALL) epc)
                       (Concrete.mkState cmem' creg' cache'
                                         apc'@(tag_to_word USER)
                                         epc') /\
      refine_memory amem' cmem' /\
      refine_registers areg' creg' /\
      cache_correct cache' /\
      mvec_in_kernel cmem' /\
      ra_in_user creg' /\
      wf_entry_points cmem' /\
      ki cmem' creg' cache'.

Hypothesis syscalls_correct_disallowed_case :
  forall ast cst cst' cst'' addr sc,
    refine_state ast cst ->
    Abstract.get_syscall table addr = Some sc ->
    Abstract.sem sc ast = None ->
    Concrete.step _ masks cst cst' ->
    Concrete.val (Concrete.pc cst') = addr ->
    ~ kernel_user_exec cst' cst''.

Lemma user_regs_unchanged_ra_in_user creg creg' :
  ra_in_user creg ->
  user_regs_unchanged creg creg' ->
  ra_in_user creg'.
Proof.
  intros [x H] H'. autounfold. eexists.
  rewrite <- (H' ra). eauto.
Qed.

Lemma kernel_user_exec_determ k s1 s2 :
  kernel_user_exec k s1 ->
  kernel_user_exec k s2 ->
  s1 = s2.
Proof.
  unfold kernel_user_exec. intros EXEC1 EXEC2.
  eapply exec_until_determ; eauto.
  - clear. intros s s1 s2.
    do 2 rewrite <- stepP in *. congruence.
  - clear. intros s H1 H2. simpl in *. congruence.
  - clear. intros s H1 H2. simpl in *. congruence.
Qed.

Lemma state_on_syscalls st st' :
  forall (ISUSER : in_user st = true)
         (CACHE : cache_correct (Concrete.cache st))
         (ISCALL : (Concrete.tag (Concrete.pc st') =? tag_to_word CALL)%word = true)
         (STEP : Concrete.step _ masks st st'),
    Concrete.mem st' = Concrete.mem st /\
    Concrete.regs st' = Concrete.upd_reg (Concrete.regs st) ra
                                         (Concrete.val (Concrete.pc st) + Z_to_word 1)%word@(tag_to_word USER) /\
    Concrete.cache st' = Concrete.cache st /\
    exists r i,
      Concrete.get_mem (Concrete.mem st) (Concrete.val (Concrete.pc st)) =
      Some i@(tag_to_word USER) /\
      decode_instr i = Some (Jal _ r) /\
      Concrete.get_reg (Concrete.regs st) r = (Concrete.val (Concrete.pc st'))@(tag_to_word USER).
Proof.
  intros.
  inv STEP;
  unfold Concrete.next_state_reg, Concrete.next_state_reg_and_pc,
         Concrete.next_state_pc, Concrete.next_state,
         Concrete.miss_state in *;
  match_inv;

  match goal with
  | LOOKUP : Concrete.cache_lookup _ _ _ ?mvec = Some ?rvec,
    PC : Concrete.get_mem _ _ = Some _ |- _ =>
    unfold in_user in ISUSER; simpl in ISUSER; rewrite PC in ISUSER;
    let op := current_instr_opcode in
    let cache_hit := constr:(CACHE mvec rvec ISUSER LOOKUP) in
    let all_user := constr:(user_chandler_inv _ cache_hit _ eq_refl) in
    try solve [destruct all_user];
    destruct all_user as (? & ? & ? & ? & ? & ? & ?);
    destruct rvec; subst mvec; simpl in *; subst;
    solve [
        rewrite <- (reflect_iff _ _ (eq_wordP _ _)) in ISCALL;
        apply tag_to_word_inj in ISCALL; inv ISCALL
      |
      eauto 8
      ]
  | LOOKUP : Concrete.cache_lookup _ _ _ ?mvec = None |- _ =>
    simpl in *; solve [
          rewrite kernel_tag_correct in ISCALL;
          rewrite <- (reflect_iff _ _ (eq_wordP _ _)) in ISCALL;
          apply tag_to_word_inj in ISCALL; inv ISCALL
        ]
  end.
Qed.

Lemma miss_simulation ast cst cst' :
  refine_state ast cst ->
  miss_step cst cst' ->
  refine_state ast cst' \/
  exists ast', Abstract.step table ast ast' /\
               refine_state ast' cst'.
Proof.
  intros REF [kst ISUSER STEP KEXEC].
  assert (KER : in_kernel kst = true).
  { destruct KEXEC as [? EXEC]. exact (restricted_exec_fst EXEC). }
  destruct ast as [[amem areg] apc], cst as [cmem cregs cache [cpc cpct] cepc].
  assert (REF' := REF).
  destruct REF' as (_ & ? & REFM & REFR & CACHE & MVEC & RA & WFENTRYPOINTS & KINV).
  unfold in_kernel in KER.
  apply orb_true_iff in KER.
  destruct KER as [FAULT | SYSCALL].
  - left.
    assert (NUSER : is_user_pc_tag (Concrete.tag (Concrete.pc kst)) = false).
    { destruct (is_user_pc_tag (Concrete.tag (Concrete.pc kst))) eqn:EQ; trivial.
      apply is_user_pc_tag_is_kernel_tag in EQ. congruence. }
    destruct (initial_handler_state ISUSER NUSER CACHE STEP)
      as (cmem' & mvec & STORE & ?). subst. simpl in *.
    destruct (chandler mvec) as [rvec|] eqn:HANDLER.
    + destruct (handler_correct_allowed_case cmem mvec cregs cpc@cpct KINV HANDLER STORE CACHE)
        as (cst'' & KEXEC' & CACHE' & LOOKUP & MVEC' &
            HMEM & HREGS & HPC & WFENTRYPOINTS' & KINV').
      assert (EQ := kernel_user_exec_determ KEXEC' KEXEC). subst cst''.
      destruct cst' as [cmem'' cregs'' cache' ? ?]. simpl in *. subst.
      unfold refine_state.
      repeat match goal with
      | |- _ /\ _ => split; eauto using user_regs_unchanged_ra_in_user
      end.
      * unfold in_user in *. simpl in *. trivial.
        rewrite orb_true_iff in ISUSER.
        destruct ISUSER as [ISUSER | ISUSER].
        { rewrite ISUSER. trivial. }
        rewrite andb_true_iff in ISUSER. destruct ISUSER as [U1 U2].
        rewrite U1. simpl.
        destruct (Concrete.get_mem cmem'' cpc) as [[i it]|] eqn:GET;
          [|apply orb_true_r].
        destruct (eq_wordP it (tag_to_word ENTRY)%word); [|apply orb_true_r]; subst.
        generalize (proj2 (WFENTRYPOINTS' cpc) (ex_intro _ _ GET)).
        intros DEF. apply WFENTRYPOINTS in DEF.
        destruct DEF as [w DEF]. rewrite DEF in U2.
        rewrite tag_to_word_eq in U2. inv U2.
      * clear - ISUSER MVEC STORE REFM HMEM.
        intros addr w. unfold user_mem_unchanged in *.
        rewrite <- HMEM. apply REFM.
      * clear - REFR HREGS.
        intros r w. unfold user_regs_unchanged in *.
        rewrite <- HREGS.
        apply REFR.
    + assert (EXEC : forall st st',
                       kernel_user_exec st st' ->
                       exec (Concrete.step _ masks) st st').
      { clear. intros st st' EXEC. destruct EXEC as [kst' EXEC].
        apply restricted_exec_weaken in EXEC.
        apply restricted_exec_trans with kst'; eauto. }
      assert (ISUSER' : in_kernel cst' = false).
      { destruct KEXEC. eauto. }
      apply EXEC in KEXEC.
      destruct (handler_correct_disallowed_case cmem mvec KINV HANDLER STORE ISUSER' KEXEC).
  - right. rewrite andb_true_iff in SYSCALL. destruct SYSCALL as [S1 S2].
    destruct (Concrete.get_mem (Concrete.mem kst) (Concrete.val (Concrete.pc kst)))
      as [[i it]|] eqn:GET; try discriminate.
    destruct (eq_wordP it (tag_to_word ENTRY)); try discriminate.
    subst. clear S2.
    exploit state_on_syscalls; eauto. simpl.
    intros (EM & ER & EC & r & w & MEM & DEC & REG).
    rewrite EM in GET.
    assert (SYSCALL : exists sc, Abstract.get_syscall table (Concrete.val (Concrete.pc kst)) = Some sc).
    { unfold wf_entry_points in WFENTRYPOINTS. rewrite WFENTRYPOINTS. eauto. }
    destruct SYSCALL as [sc GETSC].
    destruct (Abstract.sem sc (amem, areg, cpc)) as [ast'|] eqn:SCEXEC.
    + destruct ast' as [[amem' areg'] apc'].
      destruct kst as [kmem kregs kcache [kpc kpct] kepc]. simpl in *.
      apply (reflect_iff _ _ (eq_wordP _ _)) in S1. subst.
      exploit syscalls_correct_allowed_case; eauto.
      intros H.
      specialize (H MVEC WFENTRYPOINTS GETSC SCEXEC).
      destruct H as (cmem' & creg' & cache' & pct' & EXEC' &
                     REFM' & REFR' & CACHE' & MVEC' & RA' & WFENTRYPOINTS' & KINV').
      generalize (kernel_user_exec_determ KEXEC EXEC'). intros ?. subst.
      exists (amem', areg', apc'). split; eauto.
      eapply Abstract.step_syscall; eauto.
      * apply REFM in MEM; eauto.
      * now apply REFR.
      * unfold refine_state, in_user. simpl.
        rewrite tag_to_word_eq. simpl.
        repeat (split; eauto).
    + destruct (syscalls_correct_disallowed_case REF GETSC SCEXEC STEP eq_refl KEXEC).
Qed.

Lemma user_step_simulation ast cst cst' :
  refine_state ast cst ->
  user_step cst cst' ->
  exists ast',
    exec (Abstract.step table) ast ast' /\
    refine_state ast' cst'.
Proof.
  intros REF [HIT | MISS].
  - exploit hit_simulation; eauto.
    intros (ast' & STEP & REF').
    autounfold; eauto.
  - exploit miss_simulation; eauto.
    intros [H | H]; eauto.
    destruct H as (ast' & H1 & H2).
    eauto using exec_one.
Qed.

Lemma user_exec_refinement ast cst cst' :
  refine_state ast cst ->
  exec user_step cst cst' ->
  exists ast',
    exec (Abstract.step table) ast ast' /\
    refine_state ast' cst'.
Proof.
  intros REF EXEC.
  gdep ast. induction EXEC as [|? ? ? _ STEP EXEC IH]; autounfold; eauto.
  intros.
  exploit user_step_simulation; eauto. intros (? & ? & ?).
  exploit IH; eauto. intros (ast' & ? & ?).
  eexists ast'. split; eauto.
Qed.

Lemma user_into_kernel ast cst cst' :
  refine_state ast cst ->
  Concrete.step _ masks cst cst' ->
  in_user cst' = false ->
  in_kernel cst' = true.
Proof.
  destruct ast as [[? ?] ?], cst as [? ? ? [? ?] ?].
  intros REF STEP NUSER.
  destruct (in_kernel cst') eqn:NKERNEL; trivial.
  unfold in_user in NUSER.
  unfold in_kernel, Concrete.is_kernel_tag in NKERNEL.
  rewrite kernel_tag_correct in NKERNEL.
  destruct REF as (INUSER & ? & ? & ? & CACHE & ?).
  assert (PCS := valid_pcs STEP CACHE INUSER). simpl in PCS.
  repeat rewrite orb_true_iff in PCS.
  destruct PCS as [[HPC | HPC] | HPC].
  - now rewrite HPC in NUSER.
  - rewrite HPC in NUSER, NKERNEL. simpl in NUSER, NKERNEL.
    rewrite orb_false_iff in NUSER, NKERNEL.
    destruct NUSER as [_ NUSER], NKERNEL as [_ NKERNEL].
    destruct (Concrete.get_mem (Concrete.mem cst') (Concrete.val (Concrete.pc cst')))
      as [[? it]|]; try discriminate.
    now rewrite NKERNEL in NUSER.
  - now rewrite HPC in NKERNEL.
Qed.

Lemma backwards_refinement_aux cst cst' (EXEC : exec (Concrete.step _ masks) cst cst') :
  in_user cst' = true ->
  (in_user cst = true ->
   forall ast,
     refine_state ast cst ->
     exists ast',
       exec (Abstract.step table) ast ast' /\
       refine_state ast' cst') /\
  (in_kernel cst = true ->
   forall ast cst0 kst,
     refine_state ast cst0 ->
     Concrete.step _ masks cst0 kst ->
     kernel_exec kst cst ->
     exists ast',
       exec (Abstract.step table) ast ast' /\
       refine_state ast' cst').
Proof.
  induction EXEC as [cst _|cst cst'' cst' _ STEP EXEC IH];
  intros USER'.
  - split; eauto.
    intros KERNEL.
    apply in_user_in_kernel in USER'. congruence.
  - specialize (IH USER').
    split.
    + intros USER ast REF.
      destruct (in_user cst'') eqn:USER''.
      { assert (USTEP := hs_intro USER USER'' STEP).
        eapply hit_simulation in USTEP; eauto.
        destruct USTEP as (ast' & ASTEP & REF').
        destruct IH as [IH _]; eauto.
        specialize (IH eq_refl _ REF').
        destruct IH as (ast'' & AEXEC & REF'').
        now eauto. }
      exploit user_into_kernel; eauto. intros KERNEL''.
      destruct IH as [_ IH].
      specialize (IH KERNEL'' ast cst cst'' REF STEP (re_refl _ _ _ KERNEL'')).
      destruct IH as (ast' & AEXEC & REF').
      eauto.
    + intros KERNEL ast cst0 kst REF STEP0 KEXEC.
      destruct (in_kernel cst'') eqn:KERNEL''.
      { assert (KEXEC'' : kernel_exec kst cst'').
        { apply restricted_exec_trans with cst; eauto. }
        destruct IH as [_ IH].
        specialize (IH eq_refl ast cst0 kst REF STEP0 KEXEC'').
        destruct IH as (ast' & AEXEC & REF').
        eexists ast'.
        split; eauto. }
      assert (USER0 : in_user cst0 = true) by (destruct REF; eauto).
      assert (KUEXEC := eu_intro (fun s => in_kernel s = false) _ KEXEC KERNEL'' STEP).
      assert (MSTEP := ks_intro USER0 STEP0 KUEXEC).
      eapply miss_simulation in MSTEP; eauto.
      destruct MSTEP as [MSTEP | MSTEP].
      * assert (USER'' : in_user cst'' = true) by now destruct MSTEP.
        destruct IH as [IH _].
        specialize (IH USER'' ast MSTEP).
        destruct IH as (ast' & AEXEC & REF').
        eexists ast'.
        split; eauto.
      * destruct MSTEP as (ast' & ASTEP & REF').
        assert (USER'' : in_user cst'' = true) by now destruct REF'.
        destruct IH as [IH _].
        specialize (IH USER'' _ REF').
        destruct IH as (ast'' & AEXEC & REF'').
        eauto.
Qed.

Theorem backwards_refinement ast cst cst' :
  refine_state ast cst ->
  exec (Concrete.step _ masks) cst cst' ->
  in_user cst' = true ->
  exists ast',
    exec (Abstract.step table) ast ast' /\
    refine_state ast' cst'.
Proof.
  intros REF EXEC USER'.
  assert (USER : in_user cst = true) by (destruct REF; trivial).
  exploit backwards_refinement_aux; eauto.
  intros [H _]. eauto.
Qed.

Hypothesis tnone_correct :
  exists t, word_to_tag Concrete.TNone = Some t.

Lemma find_rvec :
  forall op tg,
    is_user_pc_tag tg = true ->
    let ut := tag_to_word USER in
    let nt := Concrete.TNone in
    let mkmvec := Concrete.mkMVec (op_to_word op) tg ut in
    let mkrvec := Concrete.mkRVec ut in
    match nfields op with
    | Some (input, output, iscall) =>
      let mvec :=
          match input with
          | 0 => mkmvec nt nt nt
          | 1 => mkmvec ut nt nt
          | 2 => mkmvec ut ut nt
          | _ => mkmvec ut ut ut
          end in
      let newpc := if iscall then CALL else USER in
      chandler mvec = Some (Concrete.mkRVec (tag_to_word newpc) ut)
    | None => True
    end.
Proof.
  destruct tnone_correct as [t E].
  unfold is_user_pc_tag.
  intros op tg H.
  rewrite orb_true_iff in H.
  rewrite <- (reflect_iff _ _ (eq_wordP tg (tag_to_word USER))) in H.
  rewrite <- (reflect_iff _ _ (eq_wordP tg (tag_to_word CALL))) in H.
  assert (HU : word_to_tag (tag_to_word USER) = Some USER).
  { erewrite tag_to_word_to_tag; eauto. }
  assert (HC : word_to_tag (tag_to_word CALL) = Some CALL).
  { erewrite tag_to_word_to_tag; eauto. }
  destruct op, H; subst;
  unfold chandler, cmvec_to_mvec; simpl;
  rewrite E in *; try rewrite HU in *; try rewrite HC in *;
  try rewrite op_to_wordK in *; simpl; trivial.
Qed.

Hint Unfold Concrete.next_state_reg.
Hint Unfold Concrete.next_state_reg_and_pc.
Hint Unfold Concrete.next_state_pc.
Hint Unfold Concrete.next_state.
Hint Unfold Concrete.miss_state.

Let in_kernel_user : Concrete.is_kernel_tag ops (tag_to_word USER) = false.
Proof.
  unfold Concrete.is_kernel_tag.
  rewrite kernel_tag_correct.
  destruct (eq_wordP (tag_to_word USER) (tag_to_word KERNEL)) as [EQ | NEQ]; trivial.
  apply tag_to_word_inj in EQ. discriminate.
Qed.

Lemma user_mem_unchanged_refine_memory amem cmem cmem' :
  refine_memory amem cmem ->
  user_mem_unchanged cmem cmem' ->
  refine_memory amem cmem'.
Proof.
  intros REF USERMEM addr x.
  rewrite <- (USERMEM addr).
  apply REF.
Qed.

Lemma user_regs_unchanged_refine_registers areg creg creg' :
  refine_registers areg creg ->
  user_regs_unchanged creg creg' ->
  refine_registers areg creg'.
Proof.
  intros REF USERREG r x.
  rewrite <- (USERREG r).
  apply REF.
Qed.

Ltac match_data :=
  repeat match goal with
  | H : Abstract.get_mem ?amem ?addr = Some ?w,
    REFM : refine_memory ?amem ?cmem |- _ =>
    apply REFM in H

  | H : Abstract.upd_mem ?amem ?addr _ = _,
    REFM : refine_memory ?amem ?cmem |- _ =>
    match goal with
      | _ : Concrete.upd_mem cmem addr _ = _ |- _ => fail 1
      | |- _ => idtac
    end;
    let old := fresh "old" in
    let Hold := fresh "Hold" in
    let cmem' := fresh "cmem'" in
    let UPD' := fresh "UPD'" in
    let REFM' := fresh "REFM'" in
    destruct (PartMaps.upd_inv (Abstract.mem_axioms (t := mt)) _ _ _ H) as [old Hold];
    apply REFM in Hold;
    destruct (refine_memory_upd' _ _ REFM H) as (cmem' & UPD' & REFM')

  | H : Abstract.get_reg ?aregs ?r = Some _,
    REFR : refine_registers ?aregs ?cregs |- _ =>
    apply REFR in H

  | UPD : Abstract.upd_reg ?aregs ?r _ = Some _,
    REFR : refine_registers ?aregs ?cregs |- _ =>
    match goal with
    | _ : Concrete.get_reg cregs r = _ |- _ => fail 1
    | |- _ => idtac
    end;
    let old := fresh "old" in
    let Hold := fresh "Hold" in
    let UPD' := fresh "UPD'" in
    destruct (PartMaps.upd_inv (Abstract.reg_axioms (t := mt)) _ _ _ UPD) as [old Hold];
    apply REFR in Hold;
    assert (UPD' := refine_registers_upd' _ _ REFR UPD)
  end.

Ltac user_data_unchanged :=
  match goal with
  | GET : Concrete.get_mem _ ?addr = Some _,
    USERMEM : user_mem_unchanged _ _
    |- Concrete.get_mem _ ?addr = Some _ =>
    simpl in GET, USERMEM;
    rewrite <- (USERMEM addr); eassumption

  | GET : Concrete.get_reg _ ?r = _,
    USERREGS : user_regs_unchanged _ _
    |- Concrete.get_reg _ ?r = _ =>
    simpl in GET, USERREGS;
    rewrite <- (USERREGS r); eauto
  end.

Lemma no_syscall_no_entry_point mem addr :
  wf_entry_points mem ->
  Abstract.get_syscall table addr = None ->
  match Concrete.get_mem mem addr with
  | Some _@it => negb (it =? tag_to_word ENTRY)%word
  | None => true
  end = true.
Proof.
  intros WF GETSC.
  destruct (Concrete.get_mem mem addr) as [[pc' pct']|] eqn:NEWPC; trivial.
  destruct (eq_wordP pct' (tag_to_word ENTRY)); trivial. subst.
  assert (NEWPC' : exists pc', Concrete.get_mem mem addr = Some pc'@(tag_to_word ENTRY)) by eauto.
  apply WF in NEWPC'.
  destruct NEWPC'. congruence.
Qed.

(* Just for automation *)
Let kernel_invariant_ra_upd mem regs cache w :
  ki mem regs cache ->
  ra_in_user regs ->
  ki mem (Concrete.upd_reg regs ra w@(tag_to_word USER)) cache.
Proof.
  intros KINV RA.
  destruct RA.
  eauto using kernel_invariant_upd_reg.
Qed.

Lemma forward_simulation ast ast' cst :
  refine_state ast cst ->
  Abstract.step table ast ast' ->
  exists cst',
    exec (Concrete.step _ masks) cst cst' /\
    refine_state ast' cst'.
Proof.
  destruct ast as [[amem aregs] apc], cst as [cmem cregs cache [cpc cpct] epc].
  unfold refine_state. simpl.
  intros REF STEP.
  assert (REF' := REF). (* Not good that we need to duplicate this. Should clean the syscall correctness assumptions *)
  destruct REF' as (KER & ? & REFM & REFR & CACHE & MVEC & RA & WFENTRYPOINTS & KINV).
  assert (RA' := RA). destruct RA'. (* Same here *)
  subst.
  assert (is_user_pc_tag (tag_to_word USER) = true).
  { unfold is_user_pc_tag.
    now rewrite eqb_refl; try apply eq_wordP. }
  assert (KER' := in_user_is_user_pc_tag _ KER).
  unfold in_user in KER. simpl in *.
  inv STEP;
  match_data;
  match goal with
  | H : Concrete.get_mem cmem cpc = Some _ |- _ =>
    rewrite H in KER
  end;
  let op := current_instr_opcode in
  assert (HANDLER := find_rvec op _ KER'); simpl in HANDLER;

  match type of HANDLER with
  | chandler ?mvec = Some ?rvec =>
    destruct (Concrete.cache_lookup _ cache masks mvec)
      as [rvec' | ] eqn:LOOKUP;

    [
      (* Cache hit case *)
      assert (HANDLER' := CACHE mvec rvec' KER LOOKUP);
      rewrite HANDLER in HANDLER'; inv HANDLER';
      try solve [eexists; split;
      [apply exec_one;
       econstructor (solve [eauto; repeat autounfold; simpl;
                            rewrite LOOKUP; simpl; match_inv; eauto])|
       unfold in_user in *; simpl in *;
       repeat rewrite tag_to_word_eq; simpl in *;
       repeat match goal with
       | |- _ /\ _ =>
         split; eauto using mvec_in_kernel_user_upd, ra_in_user_upd,
                            wf_entry_points_user_upd, no_syscall_no_entry_point,
                            refine_registers_upd'
       end]]
        (* || let op := current_instr_opcode in fail 3 "failed hit case" op *)
    |
      (* Cache miss case, fault handler will execute *)
      let STORE := fresh "STORE" in
      destruct (mvec_in_kernel_store_mvec mvec MVEC) as [? STORE];
      pose proof (store_mvec_mvec_in_kernel _ _ STORE);
      pose proof (kernel_invariant_store_mvec ki _ _ _ _ KINV STORE);
      destruct (handler_correct_allowed_case _ mvec _ cpc@cpct KINV HANDLER STORE CACHE)
        as ([? ? ? [? ?] ?] &
            KEXEC & CACHE' & LOOKUP' & MVEC' & USERMEM & USERREGS & PC' & WFENTRYPOINTS' & KINV'');
      simpl in PC'; inv PC';
      generalize (user_mem_unchanged_refine_memory REFM USERMEM); intros; match_data;
      try solve [eexists; split;
      [
        eapply re_step; trivial;
        [try econstructor (solve [eauto; repeat autounfold; simpl; rewrite LOOKUP, STORE; eauto])|]; try (
        eapply restricted_exec_trans;
        try solve [eapply exec_until_weaken; eapply KEXEC];
        try solve [
          eapply exec_one;
          econstructor (solve [eauto; try solve [user_data_unchanged];
                               repeat autounfold; simpl; simpl in LOOKUP'; rewrite LOOKUP';
                               simpl in *; match_inv; reflexivity])])
      |
        unfold in_user in *; simpl in *;
        repeat rewrite tag_to_word_eq; simpl in *;
        try match goal with
        | USERREGS : user_regs_unchanged ?cregs _,
          H : Concrete.get_reg ?cregs ?r = _ |- _ =>
          simpl in USERREGS; rewrite (USERREGS r) in H
        end;
        try solve [
          repeat match goal with
          | |- _ /\ _ =>
            split;
            eauto using user_mem_unchanged_refine_memory,
                        refine_registers_upd', user_regs_unchanged_refine_registers,
                        user_regs_unchanged_ra_in_user, ra_in_user_upd,
                        mvec_in_kernel_user_upd, wf_entry_points_user_upd,
                        no_syscall_no_entry_point, kernel_invariant_ra_upd
          end
        ]
      ]] (* || let op := current_instr_opcode in fail 3 "failed miss case" op *)
    ]
  end.

  destruct ast' as [[amem' aregs'] apc'].
  generalize (syscalls_correct_allowed_case _ cpc epc _ KINV REFM REFR CACHE MVEC WFENTRYPOINTS GETCALL CALL).
  intros (cmem' & creg' & cache' & epc' & KEXEC' & REFM' & REFR' & CACHE' & MVEC' & RA' & WFENTRYPOINTS' & KINV').
  eexists.
  split.
  eapply re_step; trivial.
  eapply Concrete.step_jal; eauto.
  repeat autounfold. simpl. rewrite LOOKUP. reflexivity.
  eapply exec_until_weaken. simpl. eapply KEXEC'.
  unfold in_user. simpl. rewrite tag_to_word_eq. simpl.
  repeat (split; trivial).

  destruct ast' as [[amem' aregs'] apc']. simpl in *.
  assert (refine_registers aregs regs) by eauto using user_regs_unchanged_refine_registers.
  generalize (syscalls_correct_allowed_case _ cpc epc0 _ KINV'' H3 H4 CACHE' MVEC' WFENTRYPOINTS' GETCALL CALL).
  intros (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?).
  eexists. split.
  eapply re_step; trivial.
  eapply Concrete.step_jal; eauto.
  repeat autounfold. simpl in *. rewrite LOOKUP, STORE. reflexivity.
  eapply restricted_exec_trans.
  eapply exec_until_weaken. apply KEXEC.
  eapply re_step; trivial.
  eapply Concrete.step_jal; eauto.
  eapply USERMEM in PC. eauto.
  eapply USERREGS in RW. eauto.
  eapply USERREGS in H0. eauto.
  repeat autounfold. simpl. rewrite LOOKUP'. reflexivity.
  eapply exec_until_weaken. simpl. apply H5.
  unfold in_user. simpl. rewrite tag_to_word_eq. simpl.
  repeat (split; trivial).
Qed.*)

End Refinement.
