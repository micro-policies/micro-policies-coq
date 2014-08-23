(* Parametric evaluation of concrete machine semantics *)

Require Import ZArith.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Require Import lib.Integers lib.utils lib.partial_maps lib.Coqlib common.common concrete.concrete.
Require Import List. 

Import ListNotations. 
Import Concrete. Import DoNotation.

Open Scope Z_scope.

Section WithClasses. 


Context (mt : machine_types).
Context {ops : machine_ops mt}.

Open Scope word_scope.

Local Notation "x .+1" := (x + Word.one).


Inductive cat :=
| MP  (* memory payload *)
| MT  (* memory tag *)
| RP  (* register payload *)
| RT  (* register tag *)
.

Inductive pvalue :=
| V : cat * word mt -> pvalue (* initial contents of a named category, address *)
| C : word mt -> pvalue
| E : binop -> pvalue -> pvalue -> pvalue
.

Let patom := atom pvalue pvalue.

Let atom := atom (word mt) (word mt). 

Definition known  (pv:pvalue): option (word mt)  :=
match pv with
| C a => Some a
| _ => None  (* could try to be smarter if it proves useful *)
end. 
 
Local Notation memory := (word_map mt patom).
Local Notation registers := (reg_map mt patom). 
Local Notation rules := (rules pvalue). 

Record pstate := mkPState {
  pmem   : memory;  
  pregs  : registers; 
  pcache : rules;
  ppc    : atom; 
  pepc   : patom
}.

Inductive tstate :=
| St : pstate -> tstate
| Ch : pvalue (* Zero? *) -> tstate -> tstate -> tstate.

(* Some cut-and-paste for adding rules in the pvalue world. *)

Definition mask_dc (dcm : DCMask) (mv : MVec pvalue) : MVec pvalue :=
  let '(mkMVec op tpc ti t1 t2 t3) := mv in
  mkMVec op
    (if dcm mvp_tpc then C TNone else tpc)
    (if dcm mvp_ti  then C TNone else ti)
    (if dcm mvp_t1  then C TNone else t1)
    (if dcm mvp_t2  then C TNone else t2)
    (if dcm mvp_t3  then C TNone else t3).


Definition add_rule (cache : rules) (masks: Masks) (mem : memory) : option rules :=
  do! aop   <- PartMaps.get mem (Mop mt);
  do! atpc  <- PartMaps.get mem (Mtpc mt);
  do! ati   <- PartMaps.get mem (Mti mt);
  do! at1   <- PartMaps.get mem (Mt1 mt);
  do! at2   <- PartMaps.get mem (Mt2 mt);
  do! at3   <- PartMaps.get mem (Mt3 mt);
  do! atrpc <- PartMaps.get mem (Mtrpc mt);
  do! atr   <- PartMaps.get mem (Mtr mt); 
  do! aop'  <- known (val aop); (* for now; this may not really work though *)
  do! op    <- word_to_op aop';
  let dcm := dc (masks false op) in
  Some ((mask_dc dcm (@mkMVec pvalue (val aop) (val atpc)
                              (val ati) (val at1) (val at2) (val at3)),
         @mkRVec pvalue (val atrpc) (val atr)) :: cache).

(* For now, we assume that our parametric machine is always
running with pc tag = Kernel, and that its own cache lookups
behave like the ground rules. *)

Definition next_tr (mvec : MVec pvalue) : option pvalue :=
  do! opw <- known (cop mvec);
  do! opcode <- word_to_op opw;
  match opcode with
    | NOP => Some (C TNone)
    | CONST => Some (C TKernel)
    | MOV => Some (ct1 mvec)
    | BINOP _ => Some (C TKernel)
    | LOAD =>  Some (ct2 mvec)
    | STORE => Some (ct2 mvec)
    | JUMP => Some (C TNone)
    | BNZ => Some (C TNone)
    | JAL => Some (ctpc mvec)
    | JUMPEPC => Some (C TNone)
    | ADDRULE => Some (C TNone)
    | GETTAG => Some (C TKernel)
    | PUTTAG => Some (C TNone)
    | HALT => None
    | SERVICE => None
  end.


Definition next_pstate (mvec : MVec pvalue)
                       (k : word mt -> pvalue -> option pstate) : option pstate :=
  do! tr <- next_tr mvec;
  k TKernel tr. 

Definition next_pstate_reg_and_pc (st : pstate) (mvec : MVec pvalue) r x pc' : option pstate :=
  next_pstate mvec (fun trpc tr =>
    do! reg' <- PartMaps.upd (pregs st) r x@tr;
    Some (mkPState (pmem st) reg' (pcache st) pc'@trpc (pepc st))).

Definition next_pstate_reg (st : pstate) (mvec : MVec pvalue) r x : option pstate :=
  next_pstate_reg_and_pc st mvec r x (val (ppc st)).+1.

Definition next_pstate_pc (st : pstate) (mvec : MVec pvalue) x : option pstate :=
  next_pstate mvec (fun trpc _ =>
    Some (mkPState (pmem st) (pregs st) (pcache st) x@trpc  (pepc st))).


Section WithMasks.

Variable masks: Masks.

(* Evaluation stepping can occur as long as we know
   the PC and the instruction it points to precisely,
   (and, for memory operations, the precise address involved) *)


Definition pstep (st : pstate) : option tstate :=
  let 'mkPState mem reg cache pc@tpc epc := st in
  do! i : patom <- PartMaps.get mem pc;  
  do! v : word mt <- known (val i);
  do! instr <- decode_instr v;
  let mvec := mkMVec (C (op_to_word (opcode_of instr))) (C tpc) (tag i) in
  match instr with
  | Nop =>
    let mvec := mvec (C TNone) (C TNone) (C TNone) in
    do! st' <- next_pstate_pc st mvec (pc.+1);
    Some (St st')
  | Const n r => 
    do! old <- PartMaps.get reg r;
    let mvec := mvec (tag old) (C TNone) (C TNone) in
    do! st' <- next_pstate_reg st mvec r (C (Word.casts n));
    Some (St st')  
  | Mov r1 r2 =>
    do! v1 <- PartMaps.get reg r1;
    do! old <- PartMaps.get reg r2;
    let mvec := mvec (tag v1) (tag old) (C TNone) in
    do! st' <- next_pstate_reg st mvec r2 (val v1);
    Some (St st')
  | Binop f r1 r2 r3 =>
    do! v1 <- PartMaps.get reg r1;
    do! v2 <- PartMaps.get reg r2;
    do! old <- PartMaps.get reg r3;
    let mvec := mvec (tag v1) (tag v2) (tag old) in
    do! st' <- next_pstate_reg st mvec r3 (E f (val v1) (val v2));
    Some (St st')
  | Load r1 r2 =>
    do! v1 <- PartMaps.get reg r1;
    do! a <- known (val v1);
    do! v2 <- PartMaps.get mem a;
    do! old <- PartMaps.get reg r2;
    let mvec := mvec (tag v1) (tag v2) (tag old) in
    do! st' <- next_pstate_reg st mvec r2 (val v2);
    Some (St st')
  | Store r1 r2 =>
    do! v1 <- PartMaps.get reg r1;
    do! v2 <- PartMaps.get reg r2;
    do! a <- known (val v1);
    do! v3 <- PartMaps.get mem a;
    let mvec := mvec (tag v1) (tag v2) (tag v3) in
    do! st' <- 
      next_pstate mvec 
      (fun trpc tr =>
         do! mem' <- PartMaps.upd mem a (val v2)@tr;
         Some (mkPState mem' reg cache (pc.+1)@trpc epc));
    Some (St st')
  | Jump r =>
    do! v <- PartMaps.get reg r;
    let mvec := mvec (tag v) (C TNone) (C TNone) in
    do! pc' <- known (val v);
    do! st' <- next_pstate_pc st mvec pc';
    Some (St st')
  | Bnz r n =>
    do! v <- PartMaps.get reg r;
    let mvec := mvec (tag v) (C TNone) (C TNone) in
    do! st1' <- next_pstate_pc st mvec (pc.+1);
    do! stn' <- next_pstate_pc st mvec (pc + Word.casts n);
    Some (Ch (val v) (St st1') (St stn'))
  | Jal r =>
    do! v <- PartMaps.get reg r;
    do! old <- PartMaps.get reg ra;
    let mvec := mvec (tag v) (tag old) (C TNone) in
    do! pc' <- known (val v);
    do! st' <- next_pstate_reg_and_pc st mvec ra (C (pc.+1)) pc';
    Some (St st')
  | JumpEpc => None  (* For now at least, let's just say we can't do this. *)
  | AddRule =>
    let mvec := mvec (C TNone) (C TNone) (C TNone) in
    do! st' <- 
      next_pstate mvec 
      (fun trpc _ =>
         do! cache' <- add_rule cache masks mem;
         Some (mkPState mem reg cache' (pc.+1)@trpc epc));
    Some (St st')
  | GetTag r1 r2 =>
    do! v1 <- PartMaps.get reg r1;
    do! old <- PartMaps.get reg r2;
    let mvec := mvec (tag v1) (tag old) (C TNone) in
    do! st' <- next_pstate_reg st mvec r2 (tag v1);
    Some (St st')
  | PutTag r1 r2 r3 =>
    do! v1 <- PartMaps.get reg r1;
    do! v2 <- PartMaps.get reg r2;
    do! old <- PartMaps.get reg r3;
    let mvec := mvec (tag v1) (tag v2) (tag old) in
    do! st' <- 
      next_pstate mvec 
      (fun trpc _ =>
         do! reg' <- PartMaps.upd reg r3 (val v1)@(val v2);
         Some (mkPState mem reg' cache (pc.+1)@trpc epc));
    Some (St st')
  | Halt => None
end.

Fixpoint tstep (ts: tstate) : option tstate :=
  match ts with
  | St s => pstep s
  | Ch z s1 s2 =>
      do! ts1 <- tstep s1;
      do! ts2 <- tstep s2;
      Some (Ch z ts1 ts2)
  end.

Fixpoint teval (fuel:nat) (ts: tstate) : option tstate :=
  match fuel with
  | O => Some ts
  | S fuel' => 
       do! ts' <- tstep ts;
       teval fuel' ts'
  end.

End WithMasks.

Definition environment := cat * word mt -> word mt. 

Section WithEnvironment.

Variable env: environment.

Fixpoint concretize_pvalue (pv:pvalue) : word mt :=
  match pv with
  | V a => env a 
  | C w => w
  | E f v1 v2 => binop_denote f (concretize_pvalue v1) (concretize_pvalue v2) 
  end.

Lemma concretize_known: forall pv w,
  known pv = Some w ->
  concretize_pvalue pv = w. 
Proof.
  induction pv; intros; inv H; auto. 
Qed.

Definition concretize_atom (a:patom) : atom :=
 Atom (concretize_pvalue (val a)) (concretize_pvalue (tag a)).

Definition concretize_mvec (mvec: MVec pvalue) : MVec (word mt) :=
 mkMVec (concretize_pvalue (cop mvec))
        (concretize_pvalue (ctpc mvec)) 
        (concretize_pvalue (cti mvec))
        (concretize_pvalue (ct1 mvec))
        (concretize_pvalue (ct2 mvec))
        (concretize_pvalue (ct3 mvec)).

Definition concretize_rvec (rvec: RVec pvalue): RVec (word mt) :=
  mkRVec (concretize_pvalue (ctrpc rvec))
         (concretize_pvalue (ctr rvec)).


Definition concretize_rule (pr: rule pvalue) : rule (word mt) :=
 let (mvec,rvec) := pr in
 (concretize_mvec mvec, concretize_rvec rvec).

Definition concretize_pstate (ps:pstate) : state mt :=
  mkState (PartMaps.map concretize_atom (pmem ps))
          (PartMaps.map concretize_atom (pregs ps))
          (map concretize_rule (pcache ps))
          (ppc ps)
          (concretize_atom (pepc ps)).


Fixpoint concretize_tstate (ts:tstate) : state mt :=
  match ts with
  | St ps => concretize_pstate ps
  | Ch z ts1 ts2 =>
        if concretize_pvalue z == Word.zero then
          concretize_tstate ts1
        else
          concretize_tstate ts2
  end.

End WithEnvironment.

End WithClasses.

(* must think hard about initial memory, regs states! *)

Require Import concrete.exec.

Section WithStuff.

Variable masks: Masks.

Context (mt: machine_types).
Context {ops: machine_ops mt}. 

Ltac inv H := (inversion H; subst; clear H). 

Ltac undo := 
  repeat match goal with
           | STEP : (do! x <- ?t; _) = Some _ |- _ =>
               destruct t eqn:?; simpl in STEP; try discriminate
           | STEP : Some _ = (do! x <- ?t; _) |- _ => 
               destruct t eqn:?; simpl in STEP; try discriminate
           | H : Some _ = Some _ |- _ =>
               inv H
         end.


Hypothesis sound_next_tr : forall env cache (mvec: MVec (pvalue mt)) (tr:pvalue mt),
  ctpc mvec = C mt TKernel ->                         
  Some tr = next_tr mt mvec ->
  Some (mkRVec TKernel (concretize_pvalue mt env tr)) = cache_lookup cache masks (concretize_mvec mt env mvec). 

Lemma sound_next_pstate : forall env ps mvec k kk ps',
  ctpc mvec = C mt TKernel ->
  (forall tr ps', Some ps' = k TKernel tr -> Some (concretize_pstate mt env ps') = kk (mkRVec TKernel (concretize_pvalue mt env tr))) -> 
  Some ps' = next_pstate mt mvec k ->
  Some (concretize_pstate mt env ps') = next_state masks (concretize_pstate mt env ps) (concretize_mvec mt env mvec) kk.
Proof.
  intros. 
  unfold next_state.   
  unfold next_pstate in H1. 
  undo.
  erewrite <- sound_next_tr.
  3: rewrite Heqo; auto. 
  erewrite <- H0. 
  2: rewrite <- H1; auto.
  auto.
  auto.
Qed.

(* Not sure if these are true.
   If so, should only have to prove once and instantiate. *)
Lemma upd_map_reg_map : forall env (pregs pregs':reg_map mt (atom (pvalue mt) (pvalue mt))) r a,
       PartMaps.upd pregs r a = Some pregs' ->
       PartMaps.upd (PartMaps.map (concretize_atom mt env) pregs) 
                    r (concretize_atom mt env a) = 
          Some (PartMaps.map (concretize_atom mt env) pregs'). 
Admitted.

Lemma upd_map_word_map : forall env (pmem pmem': word_map mt (atom (pvalue mt) (pvalue mt))) r a,
       PartMaps.upd pmem r a = Some pmem' ->
       PartMaps.upd (PartMaps.map (concretize_atom mt env) pmem) 
                    r (concretize_atom mt env a) = 
          Some (PartMaps.map (concretize_atom mt env) pmem'). 
Admitted.

Lemma sound_add_rule: forall env 
                             (pcache pcache' : rules (pvalue mt)) 
                             (pmem : word_map mt (atom (pvalue mt) (pvalue mt))),
       add_rule mt pcache masks pmem = Some pcache' ->
       Concrete.add_rule (map (concretize_rule mt env) pcache) masks
                         (PartMaps.map (concretize_atom mt env) pmem) =
       Some (map (concretize_rule mt env) pcache'). 
Proof.
  unfold Concrete.add_rule, add_rule. 
  intros.
  undo.
  repeat rewrite PartMaps.map_correctness.
  rewrite Heqo Heqo0 Heqo1 Heqo2 Heqo3 Heqo4 Heqo5 Heqo6. simpl. 
  unfold concretize_mvec, concretize_rvec. simpl. 
  rewrite (concretize_known _ env _ _ Heqo7). 
  rewrite Heqo8. 
  simpl. 
  destruct (dc (masks false o) mvp_tpc);
  destruct (dc (masks false o) mvp_ti);
  destruct (dc (masks false o) mvp_t1);
  destruct (dc (masks false o) mvp_t2);
  destruct (dc (masks false o) mvp_t3);
  destruct (dc (masks false o) mvp_tpc);
  destruct (dc (masks false o) mvp_tpc);
  auto.
Qed.

Lemma sound_next_pstate_reg_and_pc: forall env ps mvec r x pc' ps',
  ctpc mvec = C mt TKernel ->
  Some ps' = next_pstate_reg_and_pc mt ps mvec r x pc' ->
  Some (concretize_pstate mt env ps') = next_state_reg_and_pc masks (concretize_pstate mt env ps) (concretize_mvec mt env mvec) r (concretize_pvalue mt env x) pc'.
Proof.
  intros.  
  unfold next_state_reg_and_pc. 
  unfold next_pstate_reg_and_pc in H0. 
  eapply sound_next_pstate. eauto.
  2: apply H0. 
  intros. 
  simpl in H1. undo.
  simpl.  
  rename r0 into pregs'. 
  replace ((concretize_pvalue mt env x)@(concretize_pvalue mt env tr))
          with (concretize_atom mt env (x@tr)) by auto.
  erewrite upd_map_reg_map; eauto. simpl.
  auto.
Qed.

Lemma sound_next_pstate_reg: forall env ps mvec r x ps',
  ctpc mvec = C mt TKernel -> 
  Some ps' = next_pstate_reg mt ps mvec r x -> 
  Some (concretize_pstate mt env ps') = next_state_reg masks (concretize_pstate mt env ps) (concretize_mvec mt env mvec) r (concretize_pvalue mt env x). 
Proof.
  intros.
  unfold next_state_reg. 
  eapply sound_next_pstate_reg_and_pc; eauto. 
Qed.

Lemma sound_next_pstate_pc : forall env ps mvec pc' ps',
  ctpc mvec = C mt TKernel -> 
  Some ps' = next_pstate_pc mt ps mvec pc' -> 
  Some (concretize_pstate mt env ps') = next_state_pc masks (concretize_pstate mt env ps) (concretize_mvec mt env mvec) pc'.
Proof.
  intros.
  unfold next_state_pc. 
  eapply sound_next_pstate; eauto.
  intros. simpl in H1. undo. 
  auto.
Qed.


Lemma sound_step : forall env ps ts,
  tag (ppc mt ps) = TKernel -> 
  Some ts = pstep mt masks ps -> 
  Some (concretize_tstate mt env ts) = step masks mt (concretize_pstate mt env ps). 
Proof.  
  intros. 
  unfold step. (* unfold concretize_pstate.  *)
  unfold pstep in H0. 
  destruct ps. simpl. 
  destruct ppc0. 
  simpl in H. subst tag.
  undo. 
  replace (PartMaps.get (PartMaps.map (concretize_atom mt env) pmem0) val)
          with (option_map (concretize_atom mt env) (PartMaps.get pmem0 val))
                 by (rewrite <- PartMaps.map_correctness; auto).
  rewrite Heqo.  simpl. 
  rewrite (concretize_known _ env _ _ Heqo0). 
  rewrite Heqo1.  simpl. 
  destruct i. 

  undo. 
  simpl. 
  symmetry in Heqo2.
  erewrite (sound_next_pstate_pc _ _ _ _ _ _ Heqo2); eauto. 

  undo.     
  rewrite PartMaps.map_correctness. rewrite Heqo2. simpl. 
  symmetry in Heqo3.
  erewrite (sound_next_pstate_reg _ _ _ _ _ _ _ Heqo3); eauto.

  undo. 
  repeat rewrite PartMaps.map_correctness. rewrite Heqo2. rewrite Heqo3. simpl. 
  symmetry in Heqo4.
  erewrite (sound_next_pstate_reg _ _ _ _ _ _ _ Heqo4); eauto.

  undo. 
  repeat rewrite PartMaps.map_correctness.
  rewrite Heqo2. rewrite Heqo3. rewrite Heqo4. simpl. 
  symmetry in Heqo5.
  erewrite (sound_next_pstate_reg _ _ _ _ _ _ _ Heqo5); eauto.

  undo.
  repeat rewrite PartMaps.map_correctness.
  rewrite Heqo2. simpl. rewrite (concretize_known _ env _ _ Heqo3).
  repeat rewrite PartMaps.map_correctness.
  rewrite Heqo4. rewrite Heqo5. simpl. 
  symmetry in Heqo6.
  erewrite (sound_next_pstate_reg _ _ _ _ _ _ _ Heqo6); eauto.

  undo.
  repeat rewrite PartMaps.map_correctness.
  rewrite Heqo2. rewrite Heqo3. simpl. 
  rewrite (concretize_known _ env _ _ Heqo4). 
  rewrite PartMaps.map_correctness. rewrite Heqo5. simpl. 
  replace 
   ({|
    cop := op_to_word STORE;
    ctpc := TKernel;
    cti := concretize_pvalue mt env (tag a);
    ct1 := concretize_pvalue mt env (tag a0);
    ct2 := concretize_pvalue mt env (tag a1);
    ct3 := concretize_pvalue mt env (tag a2) |})
   with
    (concretize_mvec mt env 
       {| 
         cop := (C mt (op_to_word STORE));
         ctpc := (C mt TKernel);
         cti := tag a;
         ct1 := tag a0;
         ct2 := tag a1;
         ct3 := tag a2 |}) by auto.  (* why is this needed? *)
  eapply sound_next_pstate; eauto.
  intros. simpl in H. undo. simpl. 
  replace 
   ((concretize_pvalue mt env (common.val a1))@(concretize_pvalue mt env tr)) with
  (concretize_atom mt env ((common.val a1)@tr)) by auto.
  erewrite upd_map_word_map; eauto.
  simpl. auto.

  undo. 
  repeat rewrite PartMaps.map_correctness.
  rewrite Heqo2. simpl. 
  rewrite (concretize_known _ env _ _ Heqo3). 
  symmetry in Heqo4.
  erewrite (sound_next_pstate_pc _ _ _ _ _ _ Heqo4); eauto. 
  
  undo.
  repeat rewrite PartMaps.map_correctness.
  rewrite Heqo2. simpl. 
  have [zer|nonzer] := altP (concretize_pvalue mt env (common.val a0) =P Word.zero).
  symmetry in Heqo3. 
  erewrite (sound_next_pstate_pc _ _ _ _ _ _ Heqo3); eauto. 
  symmetry in Heqo4.
  erewrite (sound_next_pstate_pc _ _ _ _ _ _ Heqo4); eauto. 

  undo.
  repeat rewrite PartMaps.map_correctness.
  rewrite Heqo2. rewrite Heqo3. simpl.
  rewrite (concretize_known _ env _ _ Heqo4). 
  symmetry in Heqo5.
  erewrite (sound_next_pstate_reg_and_pc _ _ _ _ _ _ _ _ Heqo5); eauto.

  undo. discriminate.

  undo. simpl. 
  replace 
   ({|
    cop := op_to_word ADDRULE;
    ctpc := TKernel;
    cti := concretize_pvalue mt env (tag a);
    ct1 := TNone;
    ct2 := TNone;
    ct3 := TNone |})
   with
    (concretize_mvec mt env 
       {| 
         cop := (C mt (op_to_word ADDRULE));
         ctpc := (C mt TKernel);
         cti := tag a;
         ct1 := (C mt TNone);
         ct2 := (C mt TNone);
         ct3 := (C mt TNone) |}) by auto.  (* why is this needed? *)
  eapply sound_next_pstate; eauto.
  intros. simpl in H. 
  undo.
  erewrite sound_add_rule; eauto.
  simpl.  auto.

  undo.
  repeat rewrite PartMaps.map_correctness.
  rewrite Heqo2.  rewrite Heqo3. simpl. 
  symmetry in Heqo4. 
  erewrite (sound_next_pstate_reg _ _ _ _ _ _ _ Heqo4); eauto.
  
  undo.
  repeat rewrite PartMaps.map_correctness.
  rewrite Heqo2.  rewrite Heqo3. rewrite Heqo4. simpl. 
  symmetry in Heqo5.
  replace 
   ({|
    cop := op_to_word PUTTAG;
    ctpc := TKernel;
    cti := concretize_pvalue mt env (tag a);
    ct1 := concretize_pvalue mt env (tag a0);
    ct2 := concretize_pvalue mt env (tag a1);
    ct3 := concretize_pvalue mt env (tag a2) |})
   with
    (concretize_mvec mt env 
       {| 
         cop := (C mt (op_to_word PUTTAG));
         ctpc := (C mt TKernel);
         cti := tag a;
         ct1 := tag a0;
         ct2 := tag a1;
         ct3 := tag a2 |}) by auto.  (* why is this needed? *)
  eapply sound_next_pstate; eauto.
  intros. simpl in H. 
  undo.
  replace 
   ((concretize_pvalue mt env (common.val a0))@(concretize_pvalue mt env (common.val a1))) with
  (concretize_atom mt env ((common.val a0)@(common.val a1))) by auto.
  erewrite upd_map_reg_map; eauto.
  auto.

  discriminate.

  Grab Existential Variables. (* ??? !!! *)

  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.
Qed.


End WithStuff.


