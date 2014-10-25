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

Record pstate := mkPState {
  pmem   : memory;
  pregs  : registers;
  pcache : rules;
  ppc    : atom;
  pepc   : patom
}.


Inductive tstate :=
| Halted : tstate
| UnknownUserSt : tstate 
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
stepping from a state with pc tag = Kernel, and that its own 
cache lookups behave like the ground rules. *)

Definition next_tpc_tr (mvec : MVec pvalue) : option (word mt * pvalue) :=
  do! opw <- known (cop mvec);
  do! opcode <- word_to_op opw;
  let f (tpcp:pvalue) (trp:pvalue) :=
      do! tpc <- known tpcp;
      Some (tpc,trp) in
  match opcode with
    | NOP => f (ctpc mvec) (C TNone)
    | CONST => f (ctpc mvec) (C TKernel)
    | MOV => f (ctpc mvec) (ct1 mvec)
    | BINOP _ => f (ctpc mvec) (C TKernel)
    | LOAD =>  f (ctpc mvec) (ct2 mvec)
    | STORE => f (ctpc mvec) (ct2 mvec)
    | JUMP => f (ct1 mvec) (C TNone)
    | BNZ => f (ctpc mvec) (C TNone)
    | JAL => f (ct1 mvec) (ctpc mvec)
    | JUMPEPC => f (ct1 mvec) (C TNone)
    | ADDRULE => f (ctpc mvec) (C TNone)
    | GETTAG => f (ctpc mvec) (C TKernel)
    | PUTTAG => f (ctpc mvec) (C TNone)
    | HALT => None
    | SERVICE => None
  end.


Definition next_pstate (mvec : MVec pvalue)
                       (k : word mt  -> pvalue -> option pstate) : option pstate :=
  do! tpc_tr : word mt*pvalue <- next_tpc_tr mvec;
  let (tpc,tr) := tpc_tr in 
  k tpc tr.

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

Definition next_pstate_pc' st mvec v :=
    do! t <- known(tag v);
    match known (val v),is_kernel_tag t with
      Some p,true =>
        do! st' <- next_pstate_pc st mvec p;
        Some (St st')
    | None,false => 
        Some UnknownUserSt
    | _,_ => None
    end.


Definition next_pstate_reg_and_pc' st mvec ra x v  :=
    do! t <- known(tag v);
    match known (val v),is_kernel_tag t with
      Some p,true =>
        do! st' <- next_pstate_reg_and_pc st mvec ra x p;
        Some (St st')
    | None,false => 
        Some UnknownUserSt 
    | _,_ => None
    end.
  

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
    next_pstate_pc' st mvec v
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
    next_pstate_reg_and_pc' st mvec ra (C (pc.+1)) v
  | JumpEpc =>  
    let mvec := mvec (tag epc) (C TNone) (C TNone) in
    next_pstate_pc' st mvec epc
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
  | Halt => Some Halted
end.


Fixpoint tstep (ts: tstate) : option tstate :=
  match ts with
  | Halted => Some Halted
  | UnknownUserSt => Some UnknownUserSt
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
          (ppc ps)
          (concretize_atom (pepc ps)).


Fixpoint concretize_tstate (ts:tstate) : option (state mt) :=
  match ts with
  | Halted => None
  | UnknownUserSt => None
  | St ps => Some (concretize_pstate ps)
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

Fixpoint eval (fuel:nat) (s:state mt) : option (state mt) :=
  match fuel with
  | O => Some s
  | S fuel' =>
       do! s' <- step masks mt s;
       eval fuel' s'
  end.


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


(* parametric evaluation stays in kernel mode *)

Fixpoint kernel_tstate (ts: tstate mt) : Prop :=
  match ts with
  | Halted => False (* ?? *)
  | UnknownUserSt => False
  | St ps => tag (ppc mt ps) = TKernel 
  | Ch _ ts1 ts2 => kernel_tstate ts1 /\ kernel_tstate ts2
  end.

Fixpoint normal_tstate (ts: tstate mt) : Prop :=
  match ts with
  | St _ => True
  | Ch _ ts1 ts2 => normal_tstate ts1 /\ normal_tstate ts2
  | _ => False
  end.


Lemma kernel_pstep: forall ps ts,
  tag (ppc mt ps) = TKernel  -> 
  Some ts = pstep mt masks ps -> normal_tstate ts -> 
  kernel_tstate ts.
Proof.
  intros. unfold pstep in H0.  
  destruct ps.  simpl in H. subst. destruct ppc0. undo. 
  destruct i; 
  undo; 
  try unfold next_pstate_pc in *;
  try unfold next_pstate_reg in *;
  try unfold next_pstate_reg_and_pc in *; 
  try unfold next_pstate in *; 
  try unfold next_tpc_tr in *; 
  undo; simpl in *; undo;
  try match goal with 
      H: word_to_op (op_to_word ?X) = Some _ |- _ => rewrite op_to_wordK in H; inv H
  end; undo; auto.

  try unfold next_pstate_pc' in *. undo. 
  destruct (known mt (common.val a0)) eqn:?; undo; 
  destruct (is_kernel_tag w0) eqn:?; undo.
  try unfold next_pstate_pc in *;
  try unfold next_pstate_reg in *;
  try unfold next_pstate_reg_and_pc in *; 
  try unfold next_pstate in *; 
  try unfold next_tpc_tr in *; 
  undo; simpl in *; undo;
  try match goal with 
      H: word_to_op (op_to_word ?X) = Some _ |- _ => rewrite op_to_wordK in H; inv H
  end; undo; auto.
  unfold is_kernel_tag in Heqb. simpl. 
  have [eq|neq] := altP (w0 =P TKernel).  auto.
  apply negb_true_iff in neq. rewrite neq in Heqb; discriminate.
  inv H1. 

  try unfold next_pstate_reg_and_pc' in *. undo. 
  destruct (known mt (common.val a0)) eqn:?; undo; 
  destruct (is_kernel_tag w0) eqn:?; undo.
  try unfold next_pstate_pc in *;
  try unfold next_pstate_reg in *;
  try unfold next_pstate_reg_and_pc in *; 
  try unfold next_pstate in *; 
  try unfold next_tpc_tr in *; 
  undo; simpl in *; undo;
  try match goal with 
      H: word_to_op (op_to_word ?X) = Some _ |- _ => rewrite op_to_wordK in H; inv H
  end; undo; auto.
  unfold is_kernel_tag in Heqb. simpl.
  have [eq|neq] := altP (w0 =P TKernel).  auto.
  apply negb_true_iff in neq. rewrite neq in Heqb; discriminate.
  inv H1. 

  try unfold next_pstate_pc' in *. undo. 
  destruct (known mt (common.val pepc0)) eqn:?; undo; 
  destruct (is_kernel_tag w0) eqn:?; undo.
  try unfold next_pstate_pc in *;
  try unfold next_pstate_reg in *;
  try unfold next_pstate_reg_and_pc in *; 
  try unfold next_pstate in *; 
  try unfold next_tpc_tr in *; 
  undo; simpl in *; undo;
  try match goal with 
      H: word_to_op (op_to_word ?X) = Some _ |- _ => rewrite op_to_wordK in H; inv H
  end; undo; auto.
  unfold is_kernel_tag in Heqb. simpl. 
  have [eq|neq] := altP (w0 =P TKernel).  auto.
  apply negb_true_iff in neq. rewrite neq in Heqb; discriminate.
  inv H1. 
Qed.

Lemma kernel_tstep: forall ts ts',
  kernel_tstate ts -> 
  Some ts' = tstep mt masks ts -> normal_tstate ts' -> 
  kernel_tstate ts'. 
Proof.
  induction ts; intros.   
  inv H0. inv H1. 
  inv H0. inv H1.
  simpl in *. eapply kernel_pstep; eauto.
  simpl in *. inv H. undo. inv H1. 
  simpl; split; eauto.  
Qed.

(* parametric evaluation is sound in the three cases of interest *)

Hypothesis sound_next_tpc_tr : forall env cache (mvec: MVec (pvalue mt)) (tpc:word mt) (tr:pvalue mt),
  ctpc mvec = C mt TKernel ->
  Some (tpc,tr) = next_tpc_tr mt mvec ->
  Some (mkRVec tpc (concretize_pvalue mt env tr)) = cache_lookup cache masks (concretize_mvec mt env mvec).

Lemma sound_next_pstate : forall env ps mvec k kk ps',
  ctpc mvec = C mt TKernel ->
  (forall tpc tr ps', Some ps' = k tpc  tr -> Some (concretize_pstate mt env ps') = kk (mkRVec tpc (concretize_pvalue mt env tr))) ->
  Some ps' = next_pstate mt mvec k ->
  Some (concretize_pstate mt env ps') = next_state masks (concretize_pstate mt env ps) (concretize_mvec mt env mvec) kk.
Proof.
  intros.
  unfold next_state.
  unfold next_pstate in H1.
  undo.
  destruct p. 
  erewrite <- sound_next_tpc_tr.
  3: rewrite Heqo; eauto.
  erewrite <- H0.
  eauto.
  auto.
  auto.
Qed.


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
  erewrite PartMaps.map_upd; eauto. simpl.
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

(* First case: a normal step *)

Lemma sound_normal_step : forall env ps ts,
  tag (ppc mt ps) = TKernel ->
  forall NS: normal_tstate ts,
  Some ts = pstep mt masks ps ->
  concretize_tstate mt env ts = step masks mt (concretize_pstate mt env ps).
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

  (* Nop *)
  undo.
  simpl.
  symmetry in Heqo2.
  erewrite (sound_next_pstate_pc _ _ _ _ _ _ Heqo2); eauto.

  (* Const *)
  undo.
  rewrite PartMaps.map_correctness. rewrite Heqo2. simpl.
  symmetry in Heqo3.
  erewrite (sound_next_pstate_reg _ _ _ _ _ _ _ Heqo3); eauto.

  (* Mov *)
  undo.
  repeat rewrite PartMaps.map_correctness. rewrite Heqo2. rewrite Heqo3. simpl.
  symmetry in Heqo4.
  erewrite (sound_next_pstate_reg _ _ _ _ _ _ _ Heqo4); eauto.

  (* Binop *)
  undo.
  repeat rewrite PartMaps.map_correctness.
  rewrite Heqo2. rewrite Heqo3. rewrite Heqo4. simpl.
  symmetry in Heqo5.
  erewrite (sound_next_pstate_reg _ _ _ _ _ _ _ Heqo5); eauto.

  (* Load *)
  undo.
  repeat rewrite PartMaps.map_correctness.
  rewrite Heqo2. simpl. rewrite (concretize_known _ env _ _ Heqo3).
  repeat rewrite PartMaps.map_correctness.
  rewrite Heqo4. rewrite Heqo5. simpl.
  symmetry in Heqo6.
  erewrite (sound_next_pstate_reg _ _ _ _ _ _ _ Heqo6); eauto.

  (* Store *)
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
  erewrite PartMaps.map_upd; eauto.
  simpl. auto.

  (* Jump *)
  undo.
  repeat rewrite PartMaps.map_correctness.
  rewrite Heqo2. simpl.
  unfold next_pstate_pc' in H0. undo. 
  destruct (known mt (common.val a0)) eqn:?;
  destruct (is_kernel_tag w0) eqn:?; try discriminate. 
  undo.
  simpl. 
  rewrite (concretize_known _ env _ _ Heqo4).
  symmetry in Heqo5.
  erewrite (sound_next_pstate_pc _ _ _ _ _ _ Heqo5); eauto.
  undo.
  inv NS. 

  (* Bnz *)
  undo.
  repeat rewrite PartMaps.map_correctness.
  rewrite Heqo2. simpl.
  have [zer|nonzer] := altP (concretize_pvalue mt env (common.val a0) =P Word.zero).
  symmetry in Heqo3.
  erewrite (sound_next_pstate_pc _ _ _ _ _ _ Heqo3); eauto.
  symmetry in Heqo4.
  erewrite (sound_next_pstate_pc _ _ _ _ _ _ Heqo4); eauto.

  (* Jal *)
  undo.
  repeat rewrite PartMaps.map_correctness.
  rewrite Heqo2. rewrite Heqo3. simpl.
  unfold next_pstate_reg_and_pc' in H0.  undo. 
  destruct (known mt (common.val a0)) eqn:?;
  destruct (is_kernel_tag w0) eqn:?; try discriminate. 
  undo.
  simpl. 
  rewrite (concretize_known _ env _ _ Heqo5).
  symmetry in Heqo6.
  erewrite (sound_next_pstate_reg_and_pc _ _ _ _ _ _ _ _ Heqo6); eauto.
  undo. inv NS. 


  (* JumpEPC *)
  unfold next_pstate_pc' in H0. undo.
  destruct (known mt (common.val pepc0)) eqn:?;
  destruct (is_kernel_tag w0) eqn:?; try discriminate. 
  undo.
  simpl.
  rewrite (concretize_known _ env _ _ Heqo3). 
  symmetry in Heqo4. 
  erewrite (sound_next_pstate_pc _ _ _ _ _ _ Heqo4); eauto.
  undo. inv NS. 


  (* AddRule *)
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

  (* GetTag *)
  undo.
  repeat rewrite PartMaps.map_correctness.
  rewrite Heqo2.  rewrite Heqo3. simpl.
  symmetry in Heqo4.
  erewrite (sound_next_pstate_reg _ _ _ _ _ _ _ Heqo4); eauto.

  (* PutTag *)
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
  erewrite PartMaps.map_upd; eauto.
  auto.

  (* Halt *)
  inv H0. inv NS.


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
  reflexivity. 
Qed.


(* Second case: a step back to user mode. 
   There should be a matching step  *)

Lemma sound_unknown_user_step : forall env ps,
  tag (ppc mt ps) = TKernel ->
  Some (UnknownUserSt mt) = pstep mt masks ps ->
  exists (s:state mt),
  Some s = step masks mt (concretize_pstate mt env ps)
  /\ not (is_kernel_tag (tag (pc s))).

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
  destruct i; undo.

  (* Jump *)
  undo.
  repeat rewrite PartMaps.map_correctness.
  rewrite Heqo2. simpl.
  unfold next_pstate_pc' in H0. undo. 
  destruct (known mt (common.val a0)) eqn:?;
  destruct (is_kernel_tag w0) eqn:?; try discriminate. 
  undo.
  rewrite (concretize_known _ env _ _ Heqo3). 
  eexists. 
  split.
  replace
   ({|
    cop := op_to_word JUMP;
    ctpc := TKernel;
    cti := concretize_pvalue mt env (tag a);
    ct1 := w0;
    ct2 := TNone;
    ct3 := TNone |})
   with
    (concretize_mvec mt env
       {|
         cop := (C mt (op_to_word JUMP));
         ctpc := (C mt TKernel);
         cti := tag a;
         ct1 := (C mt w0);
         ct2 := (C mt TNone);
         ct3 := (C mt TNone) |}) by auto.  (* why is this needed? *)
  eapply sound_next_pstate_pc. 
  auto.
  unfold next_pstate_pc. simpl. 
  unfold next_pstate. unfold next_tpc_tr. simpl. 
  rewrite op_to_wordK. simpl.  eauto.
  simpl. rewrite Heqb. auto. 

  (* Jal *)
  admit. (* similar *)

  (* JumpEPC *)
  admit. (* similar *)
Qed.


(* Third case: a step to Halted.
   There should be no step at all. 
   Could combine this statement with the normal case. *)

Set Printing Depth 20.

Lemma sound_halt_step : forall env ps,
  Some (Halted mt) = pstep mt masks ps ->
  None = step masks mt (concretize_pstate mt env ps).
Proof.
  intros.
  unfold step. (* unfold concretize_pstate.  *)
  unfold pstep in H.
  destruct ps. simpl.
  destruct ppc0.
  undo.
  replace (PartMaps.get (PartMaps.map (concretize_atom mt env) pmem0) val)
          with (option_map (concretize_atom mt env) (PartMaps.get pmem0 val))
                 by (rewrite <- PartMaps.map_correctness; auto).
  rewrite Heqo.  simpl.
  rewrite (concretize_known _ env _ _ Heqo0).
  rewrite Heqo1.  simpl.
  destruct i; undo.

  (* Jump *)
  unfold next_pstate_pc' in H; undo.
  destruct (known mt (common.val a0)) eqn:?;
  destruct (is_kernel_tag w0) eqn:?; try discriminate. 
  undo.
  undo.

  (* Jal *)
  unfold next_pstate_reg_and_pc' in H;  undo. 
  destruct (known mt (common.val a0)) eqn:?;
  destruct (is_kernel_tag w0) eqn:?; try discriminate. 
  undo.
  undo.

  (* JumpEpc *)
  unfold next_pstate_pc' in H; undo.
  destruct (known mt (common.val pepc0)) eqn:?;
  destruct (is_kernel_tag w0) eqn:?; try discriminate. 
  undo.
  undo.
  
  (* Halt *)
  auto.
Qed.

(* Not sure if this particular form is still useful.. -- too weak *)
Lemma sound_tstep: forall env ts ts' s,
  kernel_tstate ts -> 
  forall NS: normal_tstate ts',
  Some ts' = tstep mt masks ts ->
  Some s = concretize_tstate mt env ts -> 
  concretize_tstate mt env ts' = step masks mt s.
Proof.
  induction ts; intros. 
    inv H. 
    inv H. 
    inv H. destruct (concretize_tstate mt env (St mt p)) eqn:?.
      inv H1.  inv Heqo. eapply sound_normal_step; eauto. 
      inv H1. 
    inv H0. undo. simpl in H1. inv H. inv NS. 
    simpl. 
    generalize H1. 
    have [zer|nonzer] := altP (concretize_pvalue mt env p =P Word.zero); eauto.
Qed.    

(* Not right...

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

End WithStuff.
