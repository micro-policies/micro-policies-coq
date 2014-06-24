Require Import Coq.Lists.List Coq.Arith.Arith Coq.ZArith.ZArith.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Require Import lib.utils lib.partial_maps.
Require Import common.common.
Require Import lib.Coqlib.
Require Import cfi.property.
Set Implicit Arguments.

Import ListNotations.

Module Abs.

Open Scope bool_scope.
Open Scope Z_scope.

Section WithClasses.

Import PartMaps.

Context (t : machine_types).
Context {ops : machine_ops t}.
Context {opss : machine_ops_spec ops}.

Class abstract_params := {
  imemory : Type;
  imem_class :> partial_map imemory (word t) (word t);

  dmemory : Type;
  dmem_class :> partial_map dmemory (word t) (word t);

  registers : Type;
  reg_class :> partial_map registers (reg t) (word t)
}.

Class params_spec (ap : abstract_params) := {

  imem_axioms :> PartMaps.axioms (@imem_class ap);

  dmem_axioms :> PartMaps.axioms (@dmem_class ap);

  reg_axioms :> PartMaps.axioms (@reg_class ap)

}.

Context {ap : abstract_params}.

Open Scope word_scope.

Local Notation word := (word t).
Local Notation "x .+1" := (add_word x (Z_to_word 1)).

(* CH: TODO: turn this into a record:
Record state := State {
  imem : imemory;
  dmem : dmemory;
  regs : registers;
  pc   : word;
  cont : bool (* machine stops when this is false;
                 this starts out as true in initial state *)
}.
*)
Definition state :=
  (imemory * dmemory * registers * word (* pc *) * bool (*jump check*))%type.

(* Para-virtualizing system calls, since CFI doesn't have any system
   calls of its own and dealing with them is an interesting problem *)
Record syscall := Syscall {
  address : word;
  sem : state -> option state
}.

Variable table : list syscall.

Definition get_syscall (addr : word) : option syscall :=
  List.find (fun sc => address sc == addr) table.

Variable valid_jmp : word -> word -> bool.

Inductive step : state -> state -> Prop :=
| step_nop : forall imem dmem reg pc i,
             forall (FETCH : get imem pc = Some i),
             forall (INST : decode_instr i = Some (Nop _)),
             step (imem,dmem,reg,pc,true) (imem,dmem,reg,pc.+1,true)
| step_const : forall imem dmem reg reg' pc i n r,
             forall (FETCH : get imem pc = Some i),
             forall (INST : decode_instr i = Some (Const _ n r)),
             forall (UPD : upd reg r (imm_to_word n) = Some reg'),
             step (imem,dmem,reg,pc,true) (imem,dmem,reg',pc.+1,true)
| step_mov : forall imem dmem reg reg' pc i r1 r2 w1,
             forall (FETCH : get imem pc = Some i),
             forall (INST : decode_instr i = Some (Mov _ r1 r2)),
             forall (R1W : get reg r1 = Some w1),
             forall (UPD : upd reg r2 w1 = Some reg'),
             step (imem,dmem,reg,pc,true) (imem,dmem,reg',pc.+1,true)
| step_binop : forall imem dmem reg reg' pc i f r1 r2 r3 w1 w2,
             forall (FETCH : get imem pc = Some i),
             forall (INST : decode_instr i = Some (Binop _ f r1 r2 r3)),
             forall (R1W : get reg r1 = Some w1),
             forall (R2W : get reg r2 = Some w2),
             forall (UPD : upd reg r3 (binop_denote f w1 w2) = Some reg'),
             step (imem,dmem,reg,pc,true) (imem,dmem,reg',pc.+1,true)
| step_load : forall imem dmem reg reg' pc i r1 r2 w1 w2,
             forall (FETCH : get imem pc = Some i),
             forall (INST : decode_instr i = Some (Load _ r1 r2)),
             forall (R1W : get reg r1 = Some w1),
             forall (MEM1 : get imem w1 = Some w2 \/ get dmem w1 = Some w2),
             forall (UPD : upd reg r2 w2 = Some reg'),
             step (imem,dmem,reg,pc,true) (imem,dmem,reg',pc.+1,true)
| step_store : forall imem dmem dmem' reg pc i r1 r2 w1 w2,
             forall (FETCH : get imem pc = Some i),
             forall (INST : decode_instr i = Some (Store _ r1 r2)),
             forall (R1W : get reg r1 = Some w1),
             forall (R2W : get reg r2 = Some w2),
             forall (UPD : upd dmem w1 w2 = Some dmem'),
             step (imem,dmem,reg,pc,true) (imem,dmem',reg,pc.+1,true)
| step_jump : forall imem dmem reg pc i r w b,
             forall (FETCH : get imem pc = Some i),
             forall (INST : decode_instr i = Some (Jump _ r)),
             forall (RW : get reg r = Some w),
             forall (VALID : valid_jmp pc w = b),
             step (imem,dmem,reg,pc,true) (imem,dmem,reg,w,b)
| step_bnz : forall imem dmem reg pc i r n w,
             forall (FETCH : get imem pc = Some i),
             forall (INST : decode_instr i = Some (Bnz _ r n)),
             forall (RW : get reg r = Some w),
             let pc' := add_word pc (if w == Z_to_word 0 then Z_to_word 1
                                     else imm_to_word n) in
             step (imem,dmem,reg,pc,true) (imem,dmem,reg,pc',true)
| step_jal : forall imem dmem reg reg' pc i r w b,
             forall (FETCH : get imem pc = Some i),
             forall (INST : decode_instr i = Some (Jal _ r)),
             forall (RW : get reg r = Some w),
             forall (UPD : upd reg ra (pc.+1) = Some reg'),
             forall (VALID : valid_jmp pc w = b),
             step (imem,dmem,reg,pc,true) (imem,dmem,reg',w,b)
| step_syscall : forall imem dmem dmem' reg reg' pc pc' sc,
                 forall (FETCH : get imem pc = None),
                 forall (NOUSERM : get dmem pc = None),
                 forall (GETCALL : get_syscall pc = Some sc), 
                 forall (CALL : sem sc (imem,dmem,reg,pc,true) =
                                Some (imem,dmem',reg',pc',true)),
                 step (imem,dmem,reg,pc,true) (imem,dmem',reg',pc',true).

Inductive step_a : state -> state -> Prop :=
| step_attack : forall imem dmem dmem' reg reg' pc i
             (FETCH: get imem pc = Some i)
             (MSAME: same_domain dmem dmem')
             (RSAME: same_domain reg reg'),
             step_a (imem,dmem,reg,pc,true) (imem,dmem',reg',pc,true).

(* Extending valid_jmp to a complete allowed CFG *)
Definition succ (st : state) (st' : state) : bool :=
  let '(imem,dmem,reg,pc,_) := st in
  let '(_,_,_,pc',_) := st' in
  match (get imem pc) with
    | Some i =>
      match decode_instr i with
        | Some (Jump r) => valid_jmp pc pc'
        | Some (Jal r) => valid_jmp pc pc'
        | Some (Bnz r imm) => (pc' == pc .+1) || (pc' == pc + imm_to_word imm)
        | None => false
        | _ => pc' == pc .+1
      end
    | None => 
      match get dmem pc with
        | Some _ => false
        | None =>
          match get_syscall pc with
            | Some sc => true
              (* This allows monitor service to return anywhere *)
              (* An alternative would be restricting this to the value
                 in the ra register (which should be the same at the end
                 of the system call to what it was before it) *)
            | None => false
          end
      end
  end.

(* CH: TODO: I'm expecting the cont bit to be initially true *)
Definition initial (s : state) := 
  let '(_,_,_,_,cont) := s in cont = true.

Program Instance abstract_cfi_machine : cfi_machine := {|
  state := state;
  initial s := initial s;

  step := step;
  step_a := step_a;

  succ := succ
 |}.

Definition S (xs : list state) :=
  exists s, xs = [s] /\ ~ exists s', step s s'.

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

Lemma step_succ_violation ast ast' :
   succ ast ast' = false ->
   step ast ast' ->
   let '(_,_,_,_,b) := ast' in
   b = false.
Proof.
  intros SUCC STEP.
  inversion STEP; subst; simpl in SUCC; rewrite FETCH in SUCC;
  try rewrite INST in SUCC;
  try (rewrite eqxx in SUCC; congruence);
  try (destruct (w == 0)); try (rewrite eqxx ?orbT in SUCC);
  try (rewrite RW in SUCC);
  try rewrite GETCALL NOUSERM in SUCC; 
  try congruence; auto.
Qed.

Lemma step_a_violation ast ast' :
   step_a ast ast' ->
   let '(_,_,_,_,b) := ast' in
   b = true.
Proof.
  intros STEP.
  inversion STEP; subst. reflexivity.
Qed.

Theorem cfi : cfi abstract_cfi_machine S.
Proof.
  unfold cfi. intros.
  apply interm_equiv_intermrev in INTERM.
  induction INTERM as [s s' STEP | s s' s'' xs STEP INTERM ].
  + destruct (succ s s') eqn:SUCC.
    * (*case the step is in the control flow graph*)
      left. intros si sj IN2.
      destruct IN2 as [[? ?] | CONTRA]; [idtac | destruct CONTRA];
      subst. auto.
    * (*case the step is outside the contro flow graph*)
      destruct STEP as [STEPA | STEP].
      - (*case it's an attacker step*)
        left. intros si sj IN2.
        destruct IN2 as [[? ?] | CONTRA]; [subst | destruct CONTRA].
        auto.
        intro STEP. assert (CONTRA := step_succ_violation SUCC STEP).
        inversion STEPA. subst. discriminate.
      - (*case it's a normal step*)
        right; exists s; exists s'; exists []; exists [].
        simpl; repeat (split;auto).
        intros ? ? IN2. destruct IN2.
        intros ? ? IN2. destruct IN2.
        unfold S. exists s'. split; auto.
        intro CONTRA. destruct CONTRA as [s'' CONTRA].
        assert (FLAG := step_succ_violation SUCC STEP).
        destruct s' as [[[[imem dmem] aregs] apc] b].
        subst. inversion CONTRA.
  + apply interm_equiv_intermrev in INTERM.
    destruct (IHINTERM INIT) as [TSAFE | [sv1 [sv2 [hs [tl VIOLATION]]]]].
    { unfold trace_has_cfi in TSAFE.
      destruct (succ s' s'') eqn:SUCC.
      * (*case the step is in the control flow graph*)
        left. intros si sj IN2.
        induction xs using rev_ind.
        { destruct IN2. }
        { clear IHxs.
          rewrite <- app_assoc in IN2.
          simpl in IN2.
          destruct (in2_reverse IN2) as [IN2' | [EQ1 EQ2]].
          - apply TSAFE; assumption.
          - subst. apply interm_last_step in INTERM; subst.
            auto.
        }
      * (*case the step is not in the control flow graph*)
        destruct STEP as [STEPA | STEP].
      - (*case it's an attacker step*)
        left. intros si sj IN2.
        induction xs using rev_ind.
        { destruct IN2. }
        { rewrite <- app_assoc in IN2.
          simpl in IN2.
          destruct (in2_reverse IN2) as [IN2' | [EQ1 EQ2]].
          - apply TSAFE; assumption.
          - subst. apply interm_last_step in INTERM; subst; auto.
            intro STEP. assert (CONTRA := step_succ_violation SUCC STEP).
            inversion STEPA; subst; discriminate. }
      - (*case it's a normal step*)
        right. induction xs using rev_ind; [inversion INTERM | idtac].
        apply interm_last_step in INTERM; subst.
        exists s'; exists s''; exists xs; exists [].
        simpl; rewrite <- app_assoc. repeat (split; auto).
        intros ? ? IN2.
        destruct IN2.
        unfold S. exists s''. split; [reflexivity | idtac].
        intro CONTRA. destruct CONTRA as [s''' CONTRA].
        assert (FLAG := step_succ_violation SUCC STEP).
        destruct s'' as [[[[imem dmem] aregs] apc] b].
        subst. inversion CONTRA. }
    { (*Case a violation occurs in the trace*)
     induction xs using rev_ind; [inversion INTERM | subst; clear IHxs].
     destruct VIOLATION as [LST [VIO [T1 [T2 STOPS]]]].
     rewrite LST in INTERM. unfold S in STOPS.
     destruct STOPS as [sv2' [EQ IRRED]].
     destruct tl; [simpl; inversion EQ; subst | inversion EQ].
     change [sv1;sv2'] with ([sv1] ++ [sv2']) in INTERM.
     remember (hs ++ [sv1]) as hs'.
     rewrite app_assoc in INTERM.
     rewrite <- Heqhs' in INTERM.
     apply interm_last_step in INTERM; subst.
     destruct VIO as [VSTEP SUCC].
     assert (FLAG := step_succ_violation SUCC VSTEP).
     destruct s' as [[[[imem dmem] aregs] apc] b]; subst.
     destruct STEP as [STEPA | STEP].
     - inversion STEPA.
     - inversion STEP. }
Qed.

End WithClasses.

End Abs.

Arguments Abs.state t {_}.
Arguments Abs.imemory t {_}.
Arguments Abs.dmemory t {_}.
Arguments Abs.registers t {_}.
Arguments Abs.syscall t {_}.
