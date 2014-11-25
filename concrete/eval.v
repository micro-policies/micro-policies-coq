(* Parametric evaluation of concrete machine semantics *)

Require Import ZArith.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Require Import lib.Integers lib.utils lib.partial_maps lib.Coqlib common.common concrete.concrete.
Require Import List.

Import ListNotations.
Import Concrete. Import DoNotation.

Open Scope Z_scope.

Ltac inv H := (inversion H; subst; clear H).

Ltac undo :=
  repeat match goal with
           | STEP : (do! x <- ?t; _) = Some _ |- _ =>
               destruct t eqn:?; simpl in STEP; try discriminate
           | STEP : Some _ = (do! x <- ?t; _) |- _ =>
               destruct t eqn:?; simpl in STEP; try discriminate
           | H : Some _ = Some _ |- _ =>
               inv H
           | H : Some _ = None |- _ =>  discriminate
           | H : None = Some |- _ =>  discriminate
         end.

Section WithClasses.

Context (mt : machine_types).
Context {ops : machine_ops mt}.

Open Scope word_scope.

Local Notation "x .+1" := (x + Word.one).


Inductive var :=
| MP : word mt -> var (* memory payload *)
| MT : word mt -> var  (* memory tag *)
| RP : reg mt -> var  (* register payload *)
| RT : reg mt -> var  (* register tag *)
.

Inductive pvalue :=
| V : var -> pvalue (* initial contents of a named category, address *)
| C : word mt -> pvalue
| E : binop -> pvalue -> pvalue -> pvalue
.

Let patom := atom pvalue pvalue.

Let atom := atom (word mt) (word mt).

Fixpoint known  (pv:pvalue): option (word mt)  :=
match pv with
| C a => Some a
| E f a b =>  (* not clear whether this makes any difference *)
    match known a,known b with
    | Some a', Some b' => Some (binop_denote f a' b')
    | _,_ => None
    end
| _ => None  
end.

Local Notation memory := (word_map mt patom).
Local Notation registers := (reg_map mt patom).
Local Notation rules := (rules pvalue).

(* Idea: to keep the pmem component of the state small, let's parameterize the whole 
machine by a fixed concrete initial memory, referenced if an address doesn't appear in pmem. *)

Variable basemem : (word_map mt atom). 

Definition pget_with_base (m:memory) (k:word mt) : option patom :=
  match PartMaps.get m k with
  | Some v => Some v 
  | None => 
      match PartMaps.get basemem k with
      | Some (cv@ct) => Some ((C cv)@(C ct))
      | None => None
      end
  end.

Record pstate := mkPState {
  pmem   : memory;
  pregs  : registers;
  pcache : rules;
  ppc    : patom;
  pepc   : patom
}.


Inductive tstate :=
| Halted : tstate
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
  do! aop   <- pget_with_base mem (Mop mt);
  do! atpc  <- pget_with_base mem (Mtpc mt);
  do! ati   <- pget_with_base mem (Mti mt);
  do! at1   <- pget_with_base mem (Mt1 mt);
  do! at2   <- pget_with_base mem (Mt2 mt);
  do! at3   <- pget_with_base mem (Mt3 mt);
  do! atrpc <- pget_with_base mem (Mtrpc mt);
  do! atr   <- pget_with_base mem (Mtr mt);
(* 
  do! aop'  <- known (val aop); (* for now; this may not really work though *)
TEMPORARY TEST HACK: *)
  let aop' : word mt := op_to_word NOP in
  do! op    <- word_to_op aop';
  let dcm := dc (masks false op) in
  Some ((mask_dc dcm (@mkMVec pvalue (val aop) (val atpc)
                              (val ati) (val at1) (val at2) (val at3)),
         @mkRVec pvalue (val atrpc) (val atr)) :: cache).

(* For now, we assume that our parametric machine is always
stepping from a state with pc tag = Kernel, and that its own 
cache lookups behave like the ground rules. *)

Definition next_rvec (mvec : MVec pvalue) : option (RVec pvalue) :=
  do! opw <- known (cop mvec);
  do! opcode <- word_to_op opw;
  match opcode with
    | NOP => Some (mkRVec (ctpc mvec) (C TNone))
    | CONST => Some (mkRVec (ctpc mvec) (C TKernel))
    | MOV => Some (mkRVec (ctpc mvec) (ct1 mvec))
    | BINOP _ => Some (mkRVec (ctpc mvec) (C TKernel))
    | LOAD =>  Some (mkRVec (ctpc mvec) (ct2 mvec))
    | STORE => Some (mkRVec (ctpc mvec) (ct2 mvec))
    | JUMP => Some (mkRVec (ct1 mvec) (C TNone))
    | BNZ => Some (mkRVec (ctpc mvec) (C TNone))
    | JAL => Some (mkRVec (ct1 mvec) (ctpc mvec))
    | JUMPEPC => Some (mkRVec (ct1 mvec) (C TNone))
    | ADDRULE => Some (mkRVec (ctpc mvec) (C TNone))
    | GETTAG => Some (mkRVec (ctpc mvec) (C TKernel))
    | PUTTAG => Some (mkRVec (ctpc mvec) (C TNone))
    | HALT => None
    | SERVICE => None
  end.


Definition next_pstate (mvec : MVec pvalue)
                       (k : RVec pvalue -> option pstate) : option pstate :=
  do! rv  <- next_rvec mvec;
  k rv.

Definition next_pstate_reg_and_pc (st : pstate) (mvec : MVec pvalue) r x pc' : option pstate :=
  next_pstate mvec (fun rvec =>
    do! reg' <- PartMaps.upd (pregs st) r x@(ctr rvec);
    Some (mkPState (pmem st) reg' (pcache st) pc'@(ctrpc rvec) (pepc st))).

Definition next_pstate_reg (st : pstate) (mvec : MVec pvalue) r x : option pstate :=
  do! pc <- known (val(ppc st));
  next_pstate_reg_and_pc st mvec r x (C (pc.+1)).

Definition next_pstate_pc (st : pstate) (mvec : MVec pvalue) x : option pstate :=
  next_pstate mvec (fun rvec =>
    Some (mkPState (pmem st) (pregs st) (pcache st) x@(ctrpc rvec) (pepc st))).

Section WithMasks.

Variable masks: Masks.

(* Evaluation stepping can occur as long as we know
   the PC and the instruction it points to precisely,
   (and, for memory operations, the precise address involved) *)
Definition pstep (st : pstate) : option tstate :=
  let 'mkPState mem reg cache pc@tpc epc := st in
  do! pcw <- known pc;
  do! i : patom <- pget_with_base mem pcw;
  do! v : word mt <- known (val i);
  do! instr <- decode_instr v;
  let mvec := mkMVec (C (op_to_word (opcode_of instr))) tpc (tag i) in
  match instr with
  | Nop =>
    let mvec := mvec (C TNone) (C TNone) (C TNone) in
    do! st' <- next_pstate_pc st mvec (C (pcw.+1));
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
    do! v2 <- pget_with_base mem a;
    do! old <- PartMaps.get reg r2;
    let mvec := mvec (tag v1) (tag v2) (tag old) in
    do! st' <- next_pstate_reg st mvec r2 (val v2);
    Some (St st')
  | Store r1 r2 =>
    do! v1 <- PartMaps.get reg r1;
    do! v2 <- PartMaps.get reg r2;
    do! a <- known (val v1);
    do! v3 <- pget_with_base mem a;
    let mvec := mvec (tag v1) (tag v2) (tag v3) in
    do! st' <-
      next_pstate mvec
      (fun rvec =>
         do! mem' <- PartMaps.upd mem a (val v2)@(ctr rvec);
         Some (mkPState mem' reg cache (C (pcw.+1))@(ctrpc rvec) epc));
    Some (St st')
  | Jump r =>
    do! v <- PartMaps.get reg r;
    let mvec := mvec (tag v) (C TNone) (C TNone) in
    do! st' <- next_pstate_pc st mvec (val v);
    Some (St st')
  | Bnz r n =>
    do! v <- PartMaps.get reg r;
    let mvec := mvec (tag v) (C TNone) (C TNone) in
    do! st1' <- next_pstate_pc st mvec (C(pcw.+1));
    do! stn' <- next_pstate_pc st mvec (C(pcw + Word.casts n));
    Some (Ch (val v) (St st1') (St stn'))
  | Jal r =>
    do! v <- PartMaps.get reg r;
    do! old <- PartMaps.get reg ra;
    let mvec := mvec (tag v) (tag old) (C TNone) in
    do! st' <- next_pstate_reg_and_pc st mvec ra (C (pcw.+1)) (val v);
    Some (St st')
  | JumpEpc =>  
    let mvec := mvec (tag epc) (C TNone) (C TNone) in
    do! st' <- next_pstate_pc st mvec (val epc);
    Some (St st')
  | AddRule =>
    let mvec := mvec (C TNone) (C TNone) (C TNone) in
    do! st' <-
      next_pstate mvec
      (fun rvec =>
         do! cache' <- add_rule cache masks mem;
         Some (mkPState mem reg cache' (C (pcw.+1))@(ctrpc rvec) epc));
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
      (fun rvec =>
         do! reg' <- PartMaps.upd reg r3 (val v1)@(val v2);
         Some (mkPState mem reg' cache (C (pcw.+1))@(ctrpc rvec) epc));
    Some (St st')
  | Halt => Some Halted
end.


(* A simple-minded stepper *)
Fixpoint tstep (ts: tstate) : option tstate :=
  match ts with
  | Halted => Some Halted
  | St s => pstep s
  | Ch z s1 s2 =>
      do! ts1 <- tstep s1;
      do! ts2 <- tstep s2;
      Some (Ch z ts1 ts2)
  end.

Definition teval := stepn tstep. 

(* Building block for more sophisticated steppers *)
Fixpoint tdistr (f: pstate -> option tstate) (ts: tstate) : option tstate :=
  match ts with
  | Halted => Some Halted
  | St s => f s
  | Ch z s1 s2 =>
      match tdistr f s1,tdistr f s2 with
      | Some l,Some r => Some (Ch z l r)
      | _,_ => None
      end
   end.


End WithMasks.

Definition environment := var -> word mt.

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
  destruct (known pv1) eqn:?.
  destruct (known pv2) eqn:?.
  inv H1. 
  erewrite <- (IHpv1 w0); auto.
  erewrite <- (IHpv2 w1); auto. 
  inv H1. 
  inv H1. 
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
          (concretize_atom (ppc ps))
          (concretize_atom (pepc ps)).


Fixpoint concretize_tstate (ts:tstate) : option (state mt) :=
  match ts with
  | Halted => None
  | St ps => Some (concretize_pstate ps)
  | Ch z ts1 ts2 =>
        if concretize_pvalue z == Word.zero then
          concretize_tstate ts1
        else
          concretize_tstate ts2
  end.

End WithEnvironment.

End WithClasses.

(* Relationship to concrete execution. *)

Section WithExec.

Variable masks: Masks.

Context (mt: machine_types).
Context {ops: machine_ops mt}.


Variable basemem : memory mt. 

Require Import concrete.execb.


 (* tstate is in kernel mode if all possible pstates are *)
Fixpoint kernel_tstate (ts: tstate mt) : Prop :=
  match ts with
  | Halted => True
  | St ps => known _ (tag (ppc mt ps)) = Some TKernel
  | Ch _ ts1 ts2 => kernel_tstate ts1 /\ kernel_tstate ts2
  end.

(* 
(* following is false: parametric evaluation stays in kernel mode *)
Lemma kernel_pstep: forall ps ts,
  known _ (tag (ppc mt ps)) = Some TKernel  -> 
  Some ts = pstep mt masks ps -> 
  kernel_tstate ts.
Proof.
  intros. unfold pstep in H0.  
  destruct ps.  simpl in H. destruct ppc0. simpl in H. undo. 
  destruct i; 
  undo;
  try unfold next_pstate_pc in *;
  try unfold next_pstate_reg in *;
  try unfold next_pstate_reg_and_pc in *; 
  try unfold next_pstate in *; 
  try unfold next_rvec in *; 
  undo; simpl in *; undo;
  try match goal with 
      H: word_to_op (op_to_word ?X) = Some _ |- _ => rewrite op_to_wordK in H; inv H
  end; undo; auto.

(* remaining cases expose falsity for Jmp, Jal, JumpEPC *)
*)

(* Also false, obviously:

Lemma kernel_tstep: forall ts ts',
  kernel_tstate ts -> 
  Some ts' = tstep mt masks ts -> 
  kernel_tstate ts'. 

*)

(* A heavy assumption that next_rvec correctly describes the behavior of the cache in kernel mode.
   We could prove that this is true initially (i.e. that next_rvec corresponds to the ground rules)
   but this assumption holds at all times, which would be much more work to show(I think). *)

Hypothesis sound_next_rvec : forall env cache (mvec: MVec (pvalue mt)) (rvec: RVec (pvalue mt)),
  known _ (ctpc mvec) = Some TKernel ->
  Some rvec = next_rvec mt mvec ->
  Some (mkRVec (concretize_pvalue mt env (ctrpc rvec))
               (concretize_pvalue mt env (ctr rvec))) = cache_lookup cache masks (concretize_mvec mt env mvec).

Lemma sound_next_pstate : forall env ps mvec k kk ps',
  known _ (ctpc mvec) = Some TKernel ->
  (forall rvec ps', Some ps' = k rvec -> Some (concretize_pstate mt env ps') = 
                               kk (mkRVec (concretize_pvalue mt env (ctrpc rvec))
                                          (concretize_pvalue mt env (ctr rvec)))) ->
  Some ps' = next_pstate mt mvec k ->
  Some (concretize_pstate mt env ps') = next_state masks (concretize_pstate mt env ps) (concretize_mvec mt env mvec) kk.
Proof.
  intros.
  unfold next_state.
  unfold next_pstate in H1.
  undo.
  erewrite <- sound_next_rvec.
  3: rewrite Heqo; eauto.
  erewrite <- H0.
  eauto.
  auto.
  auto.
Qed.


Lemma concretize_pget_with_base: forall env pmem x,
    get_with_base mt basemem (PartMaps.map (concretize_atom mt env) pmem) x = 
      omap (concretize_atom mt env) (pget_with_base mt basemem pmem x).
Proof.
  intros. unfold get_with_base, pget_with_base.
  rewrite PartMaps.map_correctness. 
  destruct (PartMaps.get pmem0 x); simpl; auto.
  destruct (PartMaps.get basemem x); simpl; auto.  
  destruct a; auto.
Qed.                                                                                  
                                                                                  Lemma sound_add_rule: forall env
                             (pcache pcache' : rules (pvalue mt))
                             (pmem : word_map mt (atom (pvalue mt) (pvalue mt))),
       add_rule mt basemem pcache masks pmem = Some pcache' ->
       add_rule_b mt basemem (map (concretize_rule mt env) pcache) masks
                         (PartMaps.map (concretize_atom mt env) pmem) =
       Some (map (concretize_rule mt env) pcache').
Proof.
  unfold add_rule, add_rule_b.
  intros.
  undo.
  repeat rewrite concretize_pget_with_base. 
  rewrite Heqo Heqo0 Heqo1 Heqo2 Heqo3 Heqo4 Heqo5 Heqo6. simpl.
  unfold concretize_mvec, concretize_rvec. simpl.
Admitted.
(* TEST HACK ...
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
*)

Lemma sound_next_pstate_reg_and_pc: forall env ps mvec r x pc' ps',
  known _ (ctpc mvec) = Some TKernel -> 
  Some ps' = next_pstate_reg_and_pc mt ps mvec r x pc' ->
  Some (concretize_pstate mt env ps') = 
           next_state_reg_and_pc masks 
           (concretize_pstate mt env ps) (concretize_mvec mt env mvec) r (concretize_pvalue mt env x) (concretize_pvalue mt env pc').
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
  change ((concretize_pvalue mt env x)@(concretize_pvalue mt env (ctr rvec)))
          with (concretize_atom mt env (x@(ctr rvec))). 
  erewrite PartMaps.map_upd; eauto. simpl.
  auto.
Qed.


Lemma sound_next_pstate_reg: forall env ps mvec r x ps',
  known _ (ctpc mvec) = Some TKernel ->
  Some ps' = next_pstate_reg mt ps mvec r x ->
  Some (concretize_pstate mt env ps') = next_state_reg masks (concretize_pstate mt env ps) (concretize_mvec mt env mvec) r (concretize_pvalue mt env x).
Proof.
  intros.
  unfold next_pstate_reg in H0. undo.
  unfold next_state_reg.
  replace ((val (pc (concretize_pstate mt env ps))+1)%w)
          with (concretize_pvalue mt env (C mt (w+1)%w)). 
  eapply sound_next_pstate_reg_and_pc; eauto.
  change (val (pc (concretize_pstate mt env ps))) with
       (concretize_pvalue mt env (val (ppc mt ps))).
  rewrite (concretize_known _ env _ _ Heqo). auto.
Qed.

Lemma sound_next_pstate_pc : forall env ps mvec pc' ps',
  known _ (ctpc mvec) = Some TKernel ->
  Some ps' = next_pstate_pc mt ps mvec pc' ->
  Some (concretize_pstate mt env ps') = next_state_pc masks (concretize_pstate mt env ps) (concretize_mvec mt env mvec) (concretize_pvalue mt env pc').
Proof.
  intros.
  unfold next_state_pc.
  eapply sound_next_pstate; eauto.
  intros. simpl in H1. undo.
  auto.
Qed.


(* One step evaluation is sound in the two cases of interest *)

(* Normal steps *)


Lemma sound_normal_step : forall env ps ts,
  known _ (tag (ppc mt ps)) = Some TKernel -> 
  forall NS: ts <> Halted _, 
  Some ts = pstep mt basemem masks ps ->
  concretize_tstate mt env ts = step masks mt basemem (concretize_pstate mt env ps).
Proof.
  intros.
  unfold step. 
  unfold pstep in H0.
  destruct ps. simpl.
  destruct ppc0.
  simpl in H. 
  undo.
  simpl. 
  rewrite (concretize_known _ env _ _ Heqo). 
  rewrite concretize_pget_with_base. 
  rewrite Heqo0.  simpl.
  rewrite (concretize_known _ env _ _ Heqo1).
  rewrite Heqo2.  simpl.
  destruct i.

  (* Nop *)
  undo.
  simpl.
  symmetry in Heqo3.
  erewrite (sound_next_pstate_pc _ _ _ _ _ _ Heqo3); eauto.

  (* Const *)
  undo.
  rewrite PartMaps.map_correctness. rewrite Heqo3. simpl.
  symmetry in Heqo4.
  erewrite (sound_next_pstate_reg _ _ _ _ _ _ _ Heqo4); eauto.

  (* Mov *)
  undo.
  repeat rewrite PartMaps.map_correctness. rewrite Heqo3. rewrite Heqo4. simpl.
  symmetry in Heqo5.
  erewrite (sound_next_pstate_reg _ _ _ _ _ _ _ Heqo5); eauto.

  (* Binop *)
  undo.
  repeat rewrite PartMaps.map_correctness.
  rewrite Heqo3. rewrite Heqo4. rewrite Heqo5. simpl.
  symmetry in Heqo6.
  erewrite (sound_next_pstate_reg _ _ _ _ _ _ _ Heqo6); eauto.

  (* Load *)
  undo.
  repeat rewrite PartMaps.map_correctness.
  rewrite Heqo3. simpl. rewrite (concretize_known _ env _ _ Heqo4).
  rewrite concretize_pget_with_base.
  rewrite Heqo5. rewrite Heqo6. simpl.
  symmetry in Heqo7.
  erewrite (sound_next_pstate_reg _ _ _ _ _ _ _ Heqo7); eauto.

  (* Store *)
  undo.
  repeat rewrite PartMaps.map_correctness.
  rewrite Heqo3. rewrite Heqo4. simpl.
  rewrite (concretize_known _ env _ _ Heqo5).
  rewrite concretize_pget_with_base; eauto.  rewrite Heqo6.  simpl.
  change
   ({|
    cop := op_to_word STORE;
    ctpc := concretize_pvalue mt env tag;
    cti := concretize_pvalue mt env (common.tag a);
    ct1 := concretize_pvalue mt env (common.tag a0);
    ct2 := concretize_pvalue mt env (common.tag a1);
    ct3 := concretize_pvalue mt env (common.tag a2) |})
   with
    (concretize_mvec mt env
       {|
         cop := (C mt (op_to_word STORE));
         ctpc := tag;
         cti := common.tag a;
         ct1 := common.tag a0;
         ct2 := common.tag a1;
         ct3 := common.tag a2 |}).  (* why is this needed? *)
  symmetry in Heqo7.
  eapply sound_next_pstate; eauto. 
  intros. simpl in H0. undo. simpl. 
  change
   ((concretize_pvalue mt env (common.val a1))@(concretize_pvalue mt env (ctr rvec))) with
  (concretize_atom mt env ((common.val a1)@(ctr rvec))).
  erewrite PartMaps.map_upd; eauto. 
  simpl; auto.

  (* Jump *)
  undo.
  repeat rewrite PartMaps.map_correctness.
  rewrite Heqo3. simpl.
  symmetry in Heqo4.
  erewrite (sound_next_pstate_pc _ _ _ _ _ _ Heqo4); eauto.

  
  (* Bnz *)
  undo.
  repeat rewrite PartMaps.map_correctness.
  rewrite Heqo3. simpl.
  have [zer|nonzer] := altP (concretize_pvalue mt env (common.val a0) =P Word.zero).
  symmetry in Heqo4.
  erewrite (sound_next_pstate_pc _ _ _ _ _ _ Heqo4); eauto.
  symmetry in Heqo5.
  erewrite (sound_next_pstate_pc _ _ _ _ _ _ Heqo5); eauto.

  (* Jal *)
  undo.
  repeat rewrite PartMaps.map_correctness.
  rewrite Heqo3. rewrite Heqo4. simpl.
  symmetry in Heqo5. 
  erewrite (sound_next_pstate_reg_and_pc _ _ _ _ _ _ _ _ Heqo5); eauto.

  (* JumpEPC *)
  undo. simpl. 
  symmetry in Heqo3. 
  erewrite (sound_next_pstate_pc _ _ _ _ _ _ Heqo3); eauto.

  (* AddRule *)
  undo. simpl.
  change
   ({|
    cop := op_to_word ADDRULE;
    ctpc := concretize_pvalue mt env tag;
    cti := concretize_pvalue mt env (common.tag a);
    ct1 := TNone;
    ct2 := TNone;
    ct3 := TNone |})
   with
    (concretize_mvec mt env
       {|
         cop := (C mt (op_to_word ADDRULE));
         ctpc := tag;
         cti := common.tag a;
         ct1 := (C mt TNone);
         ct2 := (C mt TNone);
         ct3 := (C mt TNone) |}).  (* why is this needed? *)
  eapply sound_next_pstate; eauto.
  intros. simpl in H0.
  undo.
  erewrite sound_add_rule; eauto. 
  simpl.  auto.

  (* GetTag *)
  undo.
  repeat rewrite PartMaps.map_correctness.
  rewrite Heqo3.  rewrite Heqo4. simpl.
  symmetry in Heqo5.
  erewrite (sound_next_pstate_reg _ _ _ _ _ _ _ Heqo5); eauto.

  (* PutTag *)
  undo.
  repeat rewrite PartMaps.map_correctness.
  rewrite Heqo3.  rewrite Heqo4. rewrite Heqo5. simpl.
  symmetry in Heqo6.
  change
   ({|
    cop := op_to_word PUTTAG;
    ctpc := concretize_pvalue mt env tag;
    cti := concretize_pvalue mt env (common.tag a);
    ct1 := concretize_pvalue mt env (common.tag a0);
    ct2 := concretize_pvalue mt env (common.tag a1);
    ct3 := concretize_pvalue mt env (common.tag a2) |})
   with
    (concretize_mvec mt env
       {|
         cop := (C mt (op_to_word PUTTAG));
         ctpc := tag;
         cti := common.tag a;
         ct1 := common.tag a0;
         ct2 := common.tag a1;
         ct3 := common.tag a2 |}).  (* why is this needed? *)
  eapply sound_next_pstate; eauto.
  intros. simpl in H0.
  undo.
  change
   ((concretize_pvalue mt env (common.val a0))@(concretize_pvalue mt env (common.val a1))) with
  (concretize_atom mt env ((common.val a0)@(common.val a1))).  
  erewrite PartMaps.map_upd; eauto.
  auto.

  (* Halt *)
  inv H0. exfalso; apply NS; auto.


  Grab Existential Variables. 

  apply H. 
  apply H. 
  apply H. 
  apply H. 
  apply H. 
  apply H. 
  apply H. 
  apply H. 
  apply H. 
  apply H. 
  apply H. 
Qed.


(* Halting case.  *)

Set Printing Depth 20.

Lemma sound_halt_step : forall env ps,
  Some (Halted mt) = pstep mt basemem masks ps ->
  None = step masks mt basemem (concretize_pstate mt env ps).
Proof.
  intros.
  unfold step. 
  unfold pstep in H.
  destruct ps. simpl.
  destruct ppc0.
  undo.
  rewrite (concretize_known _ env _ _ Heqo). 
  rewrite concretize_pget_with_base; eauto. 
  rewrite Heqo0.  simpl.
  rewrite (concretize_known _ env _ _ Heqo1).
  rewrite Heqo2.  simpl.
  destruct i; undo.
  auto.
Qed.

(* Somewhat generic facts about the somewhat generic tdistr funcion. *)
Lemma sound_tdistr: forall pf f env
  (SOUNDF: forall ps ts s,
     Some ts = pf ps ->
     Some s = concretize_tstate _ env ts -> 
     Some s = f (concretize_pstate _  env ps)),
  forall ts0 ts s0 s,
  Some ts = tdistr mt pf ts0 ->
  Some s0 = concretize_tstate _  env ts0 -> 
  Some s = concretize_tstate _ env ts ->
  Some s = f s0.
Proof.
  intros until ts0. induction ts0; intros.  
  inv H0. 
  simpl in *. inv H0. eauto. 
  inv H0.
  destruct (concretize_pvalue mt env p == Word.zero) eqn:?;
    inv H; destruct (tdistr mt pf ts0_1) eqn:?; destruct (tdistr mt pf ts0_2) eqn:?; 
    inv H2; simpl in *; rewrite Heqb in H1; eauto.
Qed.

Lemma sound_tdistr_none: forall env f t ts, 
       concretize_tstate mt env t = None -> 
       Some ts = tdistr mt f t -> 
       concretize_tstate mt env ts = None.
Proof.
  induction t; intros. 
  inv H0. auto. 
  inv H. 
  simpl in H.  simpl in H0. 
  destruct (concretize_pvalue mt env p == Word.zero) eqn:?; 
    destruct (tdistr mt f t1) eqn:?; destruct (tdistr mt f t2) eqn:?;
    inv H0; simpl; rewrite Heqb; eauto.
Qed.


(*  An older version of tdistr:

Fixpoint tdistr (f: pstate mt -> option (tstate mt)) (ts: tstate mt) : option (tstate mt) :=
  match ts with
  | Halted => None
  | St s => f s
  | Ch z s1 s2 =>
      match tdistr f s1,tdistr f s2 with
      | Some l,Some r => Some (Ch _ z l r)
      | Some l,None => Some l
      | None,Some r => Some r
      | None,None => None
      end
   end.

Lemma sound_tdistr: forall pf f env
  (SOUNDF: forall ps ts,
     Some ts = pf ps ->
     concretize_tstate _ env ts = f (concretize_pstate _ env ps)),
  forall ts0 ts s0,
  Some ts = tdistr pf ts0 ->
  Some s0 = concretize_tstate _ env ts0 -> 
  concretize_tstate _ env ts = f s0.
Proof.
  intros until ts0. induction ts0; intros.  
  inv H. 
  simpl in *. inv H0. auto.
  inv H0.
  destruct (concretize_pvalue mt env p == Word.zero) eqn:?. 
    inv H; destruct (tdistr pf ts0_1) eqn:?; destruct (tdistr pf ts0_2) eqn:?.
    inv H1. simpl. rewrite Heqb.  eauto.
    inv H1. eauto.
    inv H1. (* halted on left, but env sends us left.  we must also halt... *)  admit.
    inv H1. 

    inv H; destruct (tdistr pf ts0_1) eqn:?; destruct (tdistr pf ts0_2) eqn:?.
    inv H1. simpl. rewrite Heqb.  eauto.
    inv H1. admit.
    inv H1. eauto.
    inv H1. 
*)

(* Should try to fill in some facts about more tstep and teval, but
   not clear that there is anything useful to say in general, since
   properties break as soon as we leave kernel mode.

Here's a very old sample of the kind of thing we might want:
Lemma sound_eval : forall env fuel ts ts' s, 
  kernel_tstate ts -> 
  Some ts' = teval mt masks fuel ts -> 
  kernel_tstate ts' -> 
  Some s = concretize_tstate mt env ts -> 
  concretize_tstate mt env ts' = eval fuel s.
Proof.
  induction fuel; intros. 
    inv H0. auto.
    simpl. simpl in H0. undo. 
    symmetry in Heqo. 
    erewrite <- sound_tstep; eauto. . simpl. 
    eapply IHfuel; eauto. 
    eapply kernel_tstep; eauto.
Qed. 
*)


End WithExec.

(* Specific applications to refinement specs. *)

Section WithRefinement.

Context (mt : machine_types).
Context {ops : machine_ops mt}.

Variable basemem : memory mt. 

Require Import symbolic.rules.
Require Import symbolic.refinement_common.

(* Repeated from an earlier section, above *)
Hypothesis sound_next_rvec : forall env cache (mvec: MVec (pvalue mt)) (rvec: RVec (pvalue mt)),
  known _ (ctpc mvec) = Some TKernel ->
  Some rvec = next_rvec mt mvec ->
  Some (mkRVec (concretize_pvalue mt env (ctrpc rvec))
               (concretize_pvalue mt env (ctr rvec))) = cache_lookup cache masks (concretize_mvec mt env mvec).

(* Parametric equivalents of the kue functions. *)
Fixpoint pkuer (max_steps:nat) (k:pstate mt -> option (tstate mt)) (ps:(pstate mt)) : option (tstate mt) :=
  do! t <- known _ (common.tag (ppc mt ps));
  if is_kernel_tag t then
    match max_steps with
    | O => None
    | S max_steps' =>
      do! ts <- pstep _ basemem masks ps;
      tdistr mt (pkuer max_steps' (fun ps => Some(St _ ps))) ts
    end
  else k ps.

Definition pkue (max_steps:nat) (ps:pstate mt) : option (tstate mt) :=
  pkuer max_steps (fun _ => None) ps.  


Lemma sound_pkuer : forall env n pk k,
  (forall ps, match pk ps with
              | None => k (concretize_pstate mt env ps) = None
              | Some ps' => forall s', Some s' = concretize_tstate mt  env ps' -> 
                                       Some s' = k (concretize_pstate mt env ps)
              end) -> 
   forall ps ts s,
   Some ts = pkuer n pk ps -> 
   Some s = concretize_tstate mt env ts ->
   Some s = kuer basemem n k (concretize_pstate mt env ps).
Proof.
  induction n; intros.

  simpl. simpl in H0. undo. rewrite (concretize_known _ env _ _ Heqo).
   destruct (is_kernel_tag w); inv H0. 
   pose proof (H ps).  rewrite <- H3 in H0.  eapply H0; eauto.

  unfold kuer; fold kuer. 
  simpl in H0. undo.
  replace (common.tag (pc (concretize_pstate mt env ps))) with w. 
  2: clear - Heqo; destruct ps; simpl in *; rewrite (concretize_known _ env _ _ Heqo); auto.
  destruct (is_kernel_tag w) eqn:?. 
  undo.  symmetry in Heqo0; eapply sound_normal_step with (env:=env) in Heqo0.
  rewrite <- Heqo0. clear Heqo0. 
  assert (forall ps : pstate mt,
            match (fun ps : pstate mt => Some (St mt ps)) ps with
            | Some ps' =>
               forall s' : state mt,
               Some s' = concretize_tstate mt env ps' ->
               Some s' = Some (concretize_pstate mt env ps)
           | None => Some (concretize_pstate mt env ps) = None
           end).
    clear. intros. simpl in H. inv H. auto. 
  pose proof (sound_tdistr _ (pkuer n _) (kuer basemem n _) env (IHn (fun ps : pstate mt => Some (St mt ps)) Some H2)).
  destruct (concretize_tstate mt env t) eqn:?.
    eapply H3; eauto.  
    pose proof (sound_tdistr_none _ _ _ _ _ Heqo0 H0). rewrite H4 in H1. inv H1. 

  apply sound_next_rvec. 

  simpl. rewrite Heqo. unfold is_kernel_tag in Heqb. f_equal.  apply (eqP Heqb).

  intro. subst t. inv H0.  inv H1. 
  pose proof (H ps). rewrite <- H0 in H2. eauto.
Qed.

(* kue can fail if we don't match kernel pattern within n steps (by halting or wrong modes)
   pkue can fail if 
      (a) approximation fails on any path
      (b) we don't match kernel pattern within n steps (by wrong modes)
   concretize_tstate (pkue) can fail iff we halt on actual path
*)
Lemma sound_pkue : forall env n st ts s,
  Some ts = pkue n st ->
  Some s = concretize_tstate mt env ts ->
  Some s = kue basemem n (concretize_pstate mt env st).
Proof.
  unfold pkue, kue. intros. 
  eapply sound_pkuer; eauto.
  intros. reflexivity. 
Qed.


End WithRefinement.
