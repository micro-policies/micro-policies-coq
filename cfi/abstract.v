Require Import Coq.Lists.List Coq.Arith.Arith.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Require Import lib.Integers lib.utils lib.partial_maps.
Require Import common.common.
Require Import lib.Coqlib.
Require Import cfi.property.
Require Import cfi.classes.
Require lib.list_utils.
Set Implicit Arguments.

Import ListNotations.

Module Abs.

Open Scope bool_scope.

Section WithClasses.

Import PartMaps.

Context (t : machine_types).
Context {ops : machine_ops t}.
Context {opss : machine_ops_spec ops}.

Open Scope word_scope.

Local Notation word := (word t).
Local Notation "x .+1" := (Word.add x Word.one).

Local Notation imemory := (word_map t word).
Local Notation dmemory := (word_map t word).
Local Notation registers := (reg_map t word).

Record state := State {
  imem : imemory;
  dmem : dmemory;
  regs : registers;
  pc   : word;
  cont : bool (* machine stops when this is false;
                 this starts out as true in initial state *)
}.

(* Para-virtualizing system calls, since CFI doesn't have any system
   calls of its own and dealing with them is an interesting problem *)
Record syscall := Syscall {
  address : word;
  sem : state -> option state
}.

Variable table : list syscall.

Definition get_syscall (addr : word) : option syscall :=
  List.find (fun sc => address sc == addr) table.

Context {ids : @cfi_id t}.

Variable cfg : id -> id -> bool.

Definition valid_jmp := classes.valid_jmp cfg.

Inductive step : state -> state -> Prop :=
| step_nop : forall imem dmem reg pc i,
             forall (FETCH : get imem pc = Some i),
             forall (INST : decode_instr i = Some (Nop _)),
             step (State imem dmem reg pc true) (State imem dmem reg pc.+1 true)
| step_const : forall imem dmem reg reg' pc i n r,
             forall (FETCH : get imem pc = Some i),
             forall (INST : decode_instr i = Some (Const n r)),
             forall (UPD : upd reg r (Word.casts n) = Some reg'),
             step (State imem dmem reg pc true) (State imem dmem reg' pc.+1 true)
| step_mov : forall imem dmem reg reg' pc i r1 r2 w1,
             forall (FETCH : get imem pc = Some i),
             forall (INST : decode_instr i = Some (Mov r1 r2)),
             forall (R1W : get reg r1 = Some w1),
             forall (UPD : upd reg r2 w1 = Some reg'),
             step (State imem dmem reg pc true) (State imem dmem reg' pc.+1 true)
| step_binop : forall imem dmem reg reg' pc i f r1 r2 r3 w1 w2,
             forall (FETCH : get imem pc = Some i),
             forall (INST : decode_instr i = Some (Binop f r1 r2 r3)),
             forall (R1W : get reg r1 = Some w1),
             forall (R2W : get reg r2 = Some w2),
             forall (UPD : upd reg r3 (binop_denote f w1 w2) = Some reg'),
             step (State imem dmem reg pc true) (State imem dmem reg' pc.+1 true)
| step_load : forall imem dmem reg reg' pc i r1 r2 w1 w2,
             forall (FETCH : get imem pc = Some i),
             forall (INST : decode_instr i = Some (Load r1 r2)),
             forall (R1W : get reg r1 = Some w1),
             forall (MEM1 : get imem w1 = Some w2 \/ get dmem w1 = Some w2),
             forall (UPD : upd reg r2 w2 = Some reg'),
             step (State imem dmem reg pc true) (State imem dmem reg' pc.+1 true)
| step_store : forall imem dmem dmem' reg pc i r1 r2 w1 w2,
             forall (FETCH : get imem pc = Some i),
             forall (INST : decode_instr i = Some (Store r1 r2)),
             forall (R1W : get reg r1 = Some w1),
             forall (R2W : get reg r2 = Some w2),
             forall (UPD : upd dmem w1 w2 = Some dmem'),
             step (State imem dmem reg pc true) (State imem dmem' reg pc.+1 true)
| step_jump : forall imem dmem reg pc i r w b,
             forall (FETCH : get imem pc = Some i),
             forall (INST : decode_instr i = Some (Jump r)),
             forall (RW : get reg r = Some w),
             forall (VALID : valid_jmp pc w = b),
             step (State imem dmem reg pc true) (State imem dmem reg w b)
| step_bnz : forall imem dmem reg pc i r n w,
             forall (FETCH : get imem pc = Some i),
             forall (INST : decode_instr i = Some (Bnz r n)),
             forall (RW : get reg r = Some w),
             let pc' := Word.add pc (if w == Word.zero then Word.one
                                     else Word.casts n) in
             step (State imem dmem reg pc true) (State imem dmem reg pc' true)
| step_jal : forall imem dmem reg reg' pc i r w b,
             forall (FETCH : get imem pc = Some i),
             forall (INST : decode_instr i = Some (Jal r)),
             forall (RW : get reg r = Some w),
             forall (UPD : upd reg ra (pc.+1) = Some reg'),
             forall (VALID : valid_jmp pc w = b),
             step (State imem dmem reg pc true) (State imem dmem reg' w b)
| step_syscall : forall imem dmem dmem' reg reg' pc pc' sc,
                 forall (FETCH : get imem pc = None),
                 forall (NOUSERM : get dmem pc = None),
                 forall (GETCALL : get_syscall pc = Some sc),
                 forall (CALL : sem sc (State imem dmem reg pc true) =
                                Some (State imem dmem' reg' pc' true)),
                 step (State imem dmem reg pc true)
                      (State imem dmem' reg' pc' true).

Inductive step_a : state -> state -> Prop :=
| step_attack : forall imem dmem dmem' reg reg' pc b
             (MSAME: same_domain dmem dmem')
             (RSAME: same_domain reg reg'),
             step_a (State imem dmem reg pc b)
                    (State imem dmem' reg' pc b).

(* Extending valid_jmp to a complete allowed CFG *)
Definition succ (st : state) (st' : state) : bool :=
  let '(State imem dmem reg pc _) := st in
  let '(State _ _ _ pc' _) := st' in
  match (get imem pc) with
    | Some i =>
      match decode_instr i with
        | Some (Jump r) => valid_jmp pc pc'
        | Some (Jal r) => valid_jmp pc pc'
        | Some (Bnz r imm) => (pc' == pc .+1) || (pc' == pc + Word.casts imm)
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

Definition initial (s : state) :=
  cont s = true.

Definition all_attacker (xs : list state) : Prop :=
  forall x1 x2, In2 x1 x2 xs -> step_a x1 x2.

Definition all_stuck (xs : list state) : Prop :=
  forall x, In x xs -> ~ exists s, step x s.

Definition stopping (xs : list state) : Prop :=
  all_attacker xs /\ all_stuck xs.

Program Instance abstract_cfi_machine : cfi_machine := {|
  state := state;
  initial s := initial s;

  step := step;
  step_a := step_a;

  succ := succ;
  stopping := stopping
 |}.

Lemma step_succ_violation ast ast' :
   succ ast ast' = false ->
   step ast ast' ->
   cont ast = true /\ cont ast' = false.
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
   cont ast = cont ast'.
Proof.
  intros STEP.
  inversion STEP; subst. reflexivity.
Qed.

Lemma list_theorem {X} (x : X) xs hs y z tl x0 :
  xs ++ [x] = hs ++ y :: z :: tl ++ [x0] ->
  x = x0.
Proof.
  intro H.
  gdep hs. gdep y. gdep z. gdep tl.
  induction xs.
  - intros. simpl in H. repeat (destruct hs; inversion H).
  - intros. destruct hs.
    + simpl in H. inversion H. subst.
      destruct tl.
      * simpl in *.
        destruct xs; simpl in H2; [inversion H2 | idtac].
        destruct xs; simpl in *.
        inv H2. reflexivity.
        destruct xs; simpl in H2; inversion H2.
      * simpl in H2.
        specialize (IHxs tl x1 z []). apply IHxs.
        auto.
    + inv H.
      eapply IHxs; eauto.
Qed.



Lemma all_attacker_red ast ast' axs :
  all_attacker (ast :: ast' :: axs) ->
  all_attacker (ast' :: axs).
Proof.
  intros ATTACKER asi asj IN2.
  assert (IN2' : In2 asi asj (ast :: ast' :: axs))
    by (simpl; auto).
  apply ATTACKER in IN2'.
  assumption.
Qed.

Lemma all_stuck_red ast ast' axs :
  all_stuck (ast :: ast' :: axs) ->
  all_stuck (ast' :: axs).
Proof.
  intros ALLS asi IN.
  unfold all_stuck in ALLS.
  assert (IN': In asi (ast :: ast' :: axs))
    by (simpl; right; auto).
  auto.
Qed.

Lemma stuck_states_preserved_by_a asi tl :
  all_attacker (asi :: tl) ->
  cont asi = false ->
  forall asj, In asj tl -> cont asj = false.
Proof.
  intros ALLATTACKER CONT asj IN.
  gdep asi.
  induction tl; intros.
  - destruct IN.
  - destruct IN as [? | IN].
    + subst.
      assert (IN2: In2 asi asj (asi :: asj :: tl))
        by (simpl; auto).
      apply ALLATTACKER in IN2.
      destruct (step_a_violation IN2).
      assumption.
    + assert (IN2: In2 asi a (asi :: a :: tl))
        by (simpl; auto).
      apply ALLATTACKER in IN2.
      assert (CONT' := step_a_violation IN2).
      rewrite CONT' in CONT.
      apply all_attacker_red in ALLATTACKER.
      eapply IHtl; eauto.
Qed.

Theorem cfi : cfi abstract_cfi_machine.
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
        left. intros si sj IN2. simpl in *.
        destruct IN2 as [[? ?] | CONTRA]; [subst | destruct CONTRA].
        intro STEP.
        destruct (step_succ_violation SUCC STEP) as [CONT1 CONT2].
        assert (CONTRA := step_a_violation STEPA).
        rewrite CONTRA in CONT1. congruence.
      - (*case it's a normal step*)
        right; exists s; exists s'; exists []; exists [].
        simpl; repeat (split;auto).
        intros ? ? IN2. destruct IN2.
        intros ? ? IN2. destruct IN2.
        unfold stopping.
        intros si sj CONTRA. by destruct CONTRA.
        intros si IN. destruct IN as [? | IN]; [subst | destruct IN].
        destruct (step_succ_violation SUCC STEP) as [H1 H2].
        intros (? & CONTRA).
        inv CONTRA; simpl in H2; by discriminate.
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
            intro STEP. destruct (step_succ_violation SUCC STEP) as [H1 H2].
            assert (CONTRA := step_a_violation STEPA).
            rewrite CONTRA in H1. congruence. }
      - (*case it's a normal step*)
        right. induction xs using rev_ind; [inversion INTERM | idtac].
        apply interm_last_step in INTERM; subst.
        exists s'; exists s''; exists xs; exists [].
        simpl; rewrite <- app_assoc. repeat (split; auto).
        intros ? ? IN2.
        destruct IN2.
        unfold stopping.
        intros ? ? CONTRA. destruct CONTRA.
        intros si IN.
        destruct IN as [? | IN]; [subst | destruct IN].
        destruct (step_succ_violation SUCC STEP) as [H1 H2].
        intros (? & CONTRA).
        inv CONTRA; simpl in H2; by discriminate.
    }
    { (*Case a violation occurs in the trace*)
     induction xs using rev_ind; [inversion INTERM | subst; clear IHxs].
     destruct VIOLATION as [LST [VIO [T1 [T2 STOPS]]]].
     rewrite LST in INTERM. simpl in *.
     destruct STOPS as [ALLATTACKER ALLSTUCK].
     destruct VIO as [VSTEP SUCC].
     destruct (step_succ_violation SUCC VSTEP) as [H1 H2].
     destruct STEP as [STEPA | STEP].
     - unfold trace_has_at_most_one_violation.
       right.
       rewrite LST.
       exists sv1; exists sv2; exists hs; exists (tl ++ [s'']).
       split.
       { rewrite <- app_assoc. by reflexivity. }
       { split.
         { simpl; split; by auto. }
         { split; [assumption | simpl].
           split.
           - intros si sj IN2 STEP.
             induction tl using rev_ind.
             * simpl in IN2.
               destruct IN2 as [[? ?] | CONTRA]; [subst | destruct CONTRA].
               inv STEP; simpl in H2; discriminate.
             * clear IHtl.
               rewrite <- LST in INTERM.
               assert (EQ := list_theorem x xs hs sv1 sv2 tl x0 LST).
               subst.
               apply interm_last_step in INTERM; subst.
               rewrite <- app_assoc in IN2.
               simpl ((sv2 :: tl ++ [s'] ++ [s''])) in IN2.
               rewrite app_comm_cons in IN2.
               remember (sv2 :: tl) as tl'.
               destruct (in2_reverse IN2) as [IN2' | [? ?]]; subst.
               + unfold all_stuck in ALLSTUCK.
                 apply In2_implies_In in IN2'.
                 apply ALLSTUCK in IN2'.
                 assert (ESTEP: exists s, step si s)
                   by (eexists; eauto).
                 destruct (IN2' ESTEP).
               + destruct (succ si sj) eqn:SUCC'.
                 * assumption.
                 * destruct (step_succ_violation SUCC' STEP) as [H3 H4].
                   assert (EQ := step_a_violation STEPA).
                   rewrite EQ in H3.
                   congruence.
           - unfold stopping.
             split.
             { (*all attacker*)
               intros si sj IN2.
               destruct tl using rev_ind.
               - simpl in IN2.
                 destruct IN2 as [[? ?] | CONTRA]; [subst | destruct CONTRA].
                 change (hs ++ [sv1; si]) with (hs ++ [sv1] ++ [si]) in INTERM.
                 rewrite app_assoc in INTERM.
                 apply interm_last_step in INTERM; subst.
                 assumption.
               - clear IHtl.
                 rewrite <- LST in INTERM.
                 apply list_theorem in LST; subst.
                 apply interm_last_step in INTERM; subst.
                 rewrite <- app_assoc in IN2.
                 simpl (sv2 :: tl ++ [s'] ++ [s'']) in IN2.
                 rewrite app_comm_cons in IN2.
                 destruct (in2_reverse IN2) as [IN2' | [? ?]]; subst.
                 + apply ALLATTACKER; assumption.
                 + assumption.
             }
             { (*all stuck*)
               intros si IN.
               destruct tl using rev_ind.
               - destruct IN as [? | IN].
                 + subst. intros (? & CONTRA).
                   destruct (step_succ_violation SUCC VSTEP) as [H3 H4].
                   inv CONTRA; simpl in H3; by discriminate.
                 + destruct IN as [? | CONTRA].
                   * subst. intros (? & CONTRA).
                     destruct (step_succ_violation SUCC VSTEP) as [H3 H4].
                     change (hs ++ [sv1;sv2]) with (hs ++ [sv1] ++ [sv2]) in INTERM.
                     rewrite app_assoc in INTERM.
                     apply interm_last_step in INTERM. subst.
                     assert (EQ:= step_a_violation STEPA).
                     rewrite EQ in H4.
                     inv CONTRA; simpl in H4; by discriminate.
                   * destruct CONTRA.
               - clear IHtl.
                 rewrite app_comm_cons in IN.
                 apply list_utils.in_reverse in IN.
                 destruct IN as [IN | ?]; subst.
                 + apply ALLSTUCK; by assumption.
                 + rewrite <- LST in INTERM.
                   assert (EQ:= interm_last_step INTERM);
                   apply list_theorem in LST; subst.
                   subst.
                   unfold all_stuck in ALLSTUCK.
                   specialize (ALLSTUCK s').
                   assert (IN: In s' (sv2 :: tl ++ [s']))
                     by (eauto using list_utils.in_last).
                   assert (STUCK := stuck_states_preserved_by_a ALLATTACKER H2).
                   assert (IN' : In s' (tl ++ [s']))
                     by (eauto using list_utils.in_last).
                   apply STUCK in IN'.
                   assert (CONT := step_a_violation STEPA).
                   rewrite CONT in IN'.
                   intros (? & CONTRA).
                   inv CONTRA; simpl in IN'; discriminate.
             }
         }
       }
     - right.
       rewrite LST.
       exists sv1; exists sv2; exists hs; exists (tl ++ [s'']).
       split.
       { rewrite <- app_assoc. by reflexivity. }
       { split.
         { simpl; split; by auto. }
         { split; [assumption | simpl].
           split.
           - intros si sj IN2 STEP'.
             induction tl using rev_ind.
             * simpl in IN2.
               destruct IN2 as [[? ?] | CONTRA]; [subst | destruct CONTRA].
               inv STEP'; simpl in H2; discriminate.
             * clear IHtl.
               rewrite <- LST in INTERM.
               assert (EQ := list_theorem x xs hs sv1 sv2 tl x0 LST).
               subst.
               apply interm_last_step in INTERM; subst.
               rewrite <- app_assoc in IN2.
               simpl ((sv2 :: tl ++ [s'] ++ [s''])) in IN2.
               rewrite app_comm_cons in IN2.
               remember (sv2 :: tl) as tl'.
               destruct (in2_reverse IN2) as [IN2' | [? ?]]; subst.
               + unfold all_stuck in ALLSTUCK.
                 apply In2_implies_In in IN2'.
                 apply ALLSTUCK in IN2'.
                 assert (ESTEP: exists s, step si s)
                   by (eexists; eauto).
                 destruct (IN2' ESTEP).
               + unfold all_stuck in ALLSTUCK.
                 assert (IN: In si (sv2 :: tl ++ [si]))
                   by (eauto using list_utils.in_last).
                 apply ALLSTUCK in IN.
                 assert (ESTEP : exists s, step si s)
                   by (eexists; eauto).
                 destruct (IN ESTEP).
           - unfold stopping.
             split.
             { (*all attacker*)
               intros si sj IN2.
               destruct tl using rev_ind.
               - simpl in IN2.
                 destruct IN2 as [[? ?] | CONTRA]; [subst | destruct CONTRA].
                 change (hs ++ [sv1; si]) with (hs ++ [sv1] ++ [si]) in INTERM.
                 rewrite app_assoc in INTERM.
                 apply interm_last_step in INTERM; subst.
                 assert (IN: In s' [s']) by (simpl; auto).
                 apply ALLSTUCK in IN.
                 exfalso.
                 apply IN. eexists; eauto.
               - clear IHtl.
                 rewrite <- LST in INTERM.
                 apply list_theorem in LST; subst.
                 apply interm_last_step in INTERM; subst.
                 rewrite <- app_assoc in IN2.
                 simpl (sv2 :: tl ++ [s'] ++ [s'']) in IN2.
                 rewrite app_comm_cons in IN2.
                 destruct (in2_reverse IN2) as [IN2' | [? ?]]; subst.
                 + apply ALLATTACKER; assumption.
                 + assert (IN: In si (sv2 :: tl ++ [si]))
                     by (eauto using list_utils.in_last).
                   apply ALLSTUCK in IN.
                   exfalso. apply IN. eexists; eauto.
             }
             { (*all stuck*)
               intros si IN.
               destruct tl using rev_ind.
               - destruct IN as [? | IN].
                 + subst. intros (? & CONTRA).
                   destruct (step_succ_violation SUCC VSTEP) as [H3 H4].
                   inv CONTRA; simpl in H3; by discriminate.
                 + destruct IN as [? | CONTRA].
                   * subst. intros (? & CONTRA).
                     destruct (step_succ_violation SUCC VSTEP) as [H3 H4].
                     change (hs ++ [sv1;sv2]) with (hs ++ [sv1] ++ [sv2]) in INTERM.
                     rewrite app_assoc in INTERM.
                     apply interm_last_step in INTERM. subst.
                     assert (IN: In s' [s']) by (simpl; auto).
                     apply ALLSTUCK in IN.
                     exfalso.
                     apply IN. eexists; eauto.
                   * destruct CONTRA.
               - clear IHtl.
                 rewrite app_comm_cons in IN.
                 apply list_utils.in_reverse in IN.
                 destruct IN as [IN | ?]; subst.
                 + apply ALLSTUCK; by assumption.
                 + rewrite <- LST in INTERM.
                   assert (EQ:= interm_last_step INTERM);
                   apply list_theorem in LST; subst.
                   subst.
                   unfold all_stuck in ALLSTUCK.
                   specialize (ALLSTUCK s').
                   assert (IN: In s' (sv2 :: tl ++ [s']))
                     by (eauto using list_utils.in_last).
                  apply ALLSTUCK in IN.
                  exfalso.
                  apply IN; eexists; eauto.
             }
         }
       }
    }
Qed.

End WithClasses.

Notation imemory t := (word_map t (word t)).
Notation dmemory t := (word_map t (word t)).
Notation registers t := (reg_map t (word t)).

End Abs.

Arguments Abs.state t.
Arguments Abs.State {_} _ _ _ _ _.
Arguments Abs.syscall t.
