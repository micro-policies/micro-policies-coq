Require Import Coq.Lists.List Coq.Arith.Arith.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Require Import lib.Integers lib.utils.
Require Import common.common.
Require Import cfi.property.
Require Import cfi.classes.
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
  cont s.

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
   ~~ succ ast ast' ->
   step ast ast' ->
   cont ast /\ ~~ cont ast'.
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
  ~~ cont asi ->
  forall asj, In asj tl -> ~~ cont asj.
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

Lemma stuck_trace s s' xs s'' :
  interm (cfi_step abstract_cfi_machine) (s :: xs) s s'' ->
  ~~ cont s ->
  In s' (s :: xs) ->
  ~ exists s''', step s' s'''.
Proof.
  intros INTERM CONT IN (s''' & STEP).
  induction INTERM as [? ? STEP'|? ? ? ? STEP' INTERM'].
  - destruct IN as [? | IN]; subst.
    + inv STEP; by discriminate.
    + destruct IN as [? | IN]; [subst | inv IN].
      destruct STEP' as [STEPA | STEPN].
      * inv STEPA; simpl in *;
        inv STEP; by discriminate.
      * inv STEPN; by discriminate.
  - destruct IN as [? | IN];
    [inv STEP; by discriminate | subst].
    destruct STEP' as [STEPA | STEPN].
    + inv STEPA.
      simpl in *.
      by auto.
    + inv STEPN; by discriminate.
Qed.

Theorem cfi : cfi abstract_cfi_machine.
Proof.
  unfold cfi.
  intros.
  clear INIT.
  induction INTERM as [s s' STEP | s s' s'' xs STEP INTERM ].
  - unfold trace_has_at_most_one_violation.
    destruct STEP as [STEPA | STEPN].
    + left. unfold trace_has_cfi.
      intros si sj INTRACE STEP.
      have [SUCC//|SUCC] := boolP (succ si sj).
      destruct (step_succ_violation SUCC STEP) as [CONT1 CONT2].
      assert (CONTRA := step_a_violation STEPA).
      destruct INTRACE as [[? ?]|INTRACE]; subst.
      * by rewrite -CONTRA CONT1 in CONT2.
      * by (inv INTRACE).
    + unfold trace_has_cfi.
      have [SUCC|SUCC] := boolP (succ s s').
      * left. intros.
        destruct INTRACE as [[? ?]|INTRACE];
        [subst; by assumption | by (inv INTRACE)].
      * right.
        exists s; exists s'; do 2 exists [].
        simpl; repeat split; try (auto || intros ? ? IN2; by (destruct IN2)).
        intros ? IN [s0 STEP].
        destruct IN as [? | IN]; [subst | destruct IN].
        destruct (step_succ_violation SUCC STEPN) as [H1 H2].
        inv STEP; simpl in H2; by discriminate.
  - unfold trace_has_at_most_one_violation in IHINTERM.
    destruct IHINTERM as [TCFI | [sv1 [sv2 [hs [tl VIOLATION]]]]].
    { (*case no violation in the trace*)
      destruct STEP as [STEPA | STEPN].
      - left. unfold trace_has_cfi.
        intros si sj INTRACE STEP.
        have [SUCC|SUCC] := boolP (succ si sj); first assumption.
        destruct (step_succ_violation SUCC STEP) as [CONT1 CONT2];
        assert (CONTRA := step_a_violation STEPA);
        destruct xs; first (by inv INTRACE);
        apply interm_first_step in INTERM; subst;
        destruct INTRACE as [[? ?]|INTRACE]; subst.
        + by rewrite -CONTRA CONT1 in CONT2.
        + by auto.
      - have [SUCC|SUCC] := boolP (succ s s').
        + left. intros ? ? INTRACE STEP.
          destruct xs; first (by inv INTRACE).
          apply interm_first_step in INTERM; subst.
          destruct INTRACE as [[? ?]|INTRACE];
            [subst; by assumption | by auto].
        + right.
          destruct xs; first (by inv INTERM).
          assert (EQ := interm_first_step INTERM); subst.
          exists s; exists s'; exists []; exists xs.
          simpl; repeat split;
          try (auto || intros ? ? IN2; by (destruct IN2)).
          { intros ? ? IN2.
            assert (STEP := interm_in2_step INTERM IN2).
            destruct STEP as [STEPA | STEPN']; first (by assumption).
            unfold trace_has_cfi in TCFI.
            exfalso.
            destruct (step_succ_violation SUCC STEPN) as [CONT1 CONT2].
            clear TCFI SUCC.
            apply In2_implies_In in IN2.
            eapply stuck_trace; eauto.
          }
          { intros x IN (s0 & STEP).
            destruct (step_succ_violation SUCC STEPN) as [CONT1 CONT2].
            eapply stuck_trace; eauto.
          }
    }
    { destruct VIOLATION as [LST [[STEPV SUCC] [HCFI [TCFI STOP]]]].
      right.
      exists sv1; exists sv2; exists (s :: hs); exists tl.
      repeat split;
        try solve [rewrite LST; reflexivity
                  | auto
                  | simpl in STOP; destruct STOP; assumption].
      intros si sj IN2 STEPN.
      destruct hs.
      - destruct IN2 as [[? ?]|CONTRA];
        [subst | destruct CONTRA].
        have [SUCC'|SUCC'] := boolP (succ si sj); first (by assumption).
        destruct (step_succ_violation SUCC' STEPN) as [CONT1 CONT2].
        inv STEPV; by discriminate.
      - destruct IN2 as [[? ?]|IN2]; subst.
        + have [SUCC'|SUCC'] := boolP (succ si sj); first (by assumption).
          destruct (step_succ_violation SUCC' STEPN) as [CONT1 CONT2].
          exfalso.
          simpl in INTERM.
          remember (hs ++ sv1 :: sv2 :: tl) as lst.
          assert (Heq: sj :: hs ++ sv1 :: sv2 :: tl = sj :: lst)
            by (rewrite Heqlst; reflexivity).
          rewrite Heq in INTERM.
          have IN: In sv1 ((sj :: hs) ++ sv1 :: (sv2 :: tl)) by rewrite in_app_iff /=; auto.
          simpl ((sj :: hs) ++ sv1 :: sv2 :: tl) in IN.
          rewrite  Heq in IN.
          assert (EQ := interm_first_step INTERM); subst.
          eapply stuck_trace; eauto.
        + apply HCFI; by assumption.
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
