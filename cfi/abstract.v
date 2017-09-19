From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From CoqUtils Require Import word fset fmap.
Require Import lib.utils lib.ssr_list_utils common.types.
Require Import cfi.property cfi.classes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Abs.

Open Scope bool_scope.

Section WithClasses.

Context (mt : machine_types).
Context {ops : machine_ops mt}.
Context {opss : machine_ops_spec ops}.

Open Scope word_scope.

Local Notation word := (mword mt).
Local Notation "x .+1" := (x + 1).

Local Notation imemory := {fmap word -> word}.
Local Notation dmemory := {fmap word -> word}.
Local Notation registers := {fmap reg mt -> word}.

Record state := State {
  imem : imemory;
  dmem : dmemory;
  regs : registers;
  pc   : word;
  cont : bool (* machine stops when this is false;
                 this starts out as true in initial state *)
}.

Definition cfi_abs_state_eq (s1 s2 : state) :=
  [&& imem s1 == imem s2,
      dmem s1 == dmem s2,
      regs s1 == regs s2,
      pc s1 == pc s2 &
      cont s1 == cont s2].

Lemma cfi_abs_state_eqP : Equality.axiom cfi_abs_state_eq.
Proof.
move=> [?????] [?????]; apply/(iffP idP).
  by case/and5P=> /=; do !move => /= /eqP ->.
by case; do !move => ->; rewrite /cfi_abs_state_eq !eqxx.
Qed.

Definition cfi_abs_state_eqMixin := EqMixin cfi_abs_state_eqP.
Canonical cfi_abs_state_eqType :=
  Eval hnf in EqType state cfi_abs_state_eqMixin.

(* Para-virtualizing system calls, since CFI doesn't have any system
   calls of its own and dealing with them is an interesting problem *)
Record syscall := Syscall {
  sem : state -> option state
}.

Definition syscall_table := {fmap word -> syscall}.

Variable table : syscall_table.

Context {ids : cfi_id mt}.

Variable cfg : id -> id -> bool.

Definition valid_jmp := classes.valid_jmp cfg.

Implicit Types imem : imemory.
Implicit Types dmem : dmemory.
Implicit Types reg : registers.

Inductive step : state -> state -> Prop :=
| step_nop : forall imem dmem reg pc i,
             forall (FETCH : imem pc = Some i),
             forall (INST : decode_instr i = Some (Nop _)),
             step (State imem dmem reg pc true) (State imem dmem reg pc.+1 true)
| step_const : forall imem dmem reg reg' pc i n r,
             forall (FETCH : imem pc = Some i),
             forall (INST : decode_instr i = Some (Const n r)),
             forall (UPD : updm reg r (swcast n) = Some reg'),
             step (State imem dmem reg pc true) (State imem dmem reg' pc.+1 true)
| step_mov : forall imem dmem reg reg' pc i r1 r2 w1,
             forall (FETCH : imem pc = Some i),
             forall (INST : decode_instr i = Some (Mov r1 r2)),
             forall (R1W : reg r1 = Some w1),
             forall (UPD : updm reg r2 w1 = Some reg'),
             step (State imem dmem reg pc true) (State imem dmem reg' pc.+1 true)
| step_binop : forall imem dmem reg reg' pc i f r1 r2 r3 w1 w2,
             forall (FETCH : imem pc = Some i),
             forall (INST : decode_instr i = Some (Binop f r1 r2 r3)),
             forall (R1W : reg r1 = Some w1),
             forall (R2W : reg r2 = Some w2),
             forall (UPD : updm reg r3 (binop_denote f w1 w2) = Some reg'),
             step (State imem dmem reg pc true) (State imem dmem reg' pc.+1 true)
| step_load : forall imem dmem reg reg' pc i r1 r2 w1 w2,
             forall (FETCH : imem pc = Some i),
             forall (INST : decode_instr i = Some (Load r1 r2)),
             forall (R1W : reg r1 = Some w1),
             forall (MEM1 : imem w1 = Some w2 \/ dmem w1 = Some w2),
             forall (UPD : updm reg r2 w2 = Some reg'),
             step (State imem dmem reg pc true) (State imem dmem reg' pc.+1 true)
| step_store : forall imem dmem dmem' reg pc i r1 r2 w1 w2,
             forall (FETCH : imem pc = Some i),
             forall (INST : decode_instr i = Some (Store r1 r2)),
             forall (R1W : reg r1 = Some w1),
             forall (R2W : reg r2 = Some w2),
             forall (UPD : updm dmem w1 w2 = Some dmem'),
             step (State imem dmem reg pc true) (State imem dmem' reg pc.+1 true)
| step_jump : forall imem dmem reg pc i r w b,
             forall (FETCH : imem pc = Some i),
             forall (INST : decode_instr i = Some (Jump r)),
             forall (RW : reg r = Some w),
             forall (VALID : valid_jmp pc w = b),
             step (State imem dmem reg pc true) (State imem dmem reg w b)
| step_bnz : forall imem dmem reg pc i r n w,
             forall (FETCH : imem pc = Some i),
             forall (INST : decode_instr i = Some (Bnz r n)),
             forall (RW : reg r = Some w),
             let pc' := pc + (if w == 0 then 1 else swcast n) in
             step (State imem dmem reg pc true) (State imem dmem reg pc' true)
| step_jal : forall imem dmem reg reg' pc i r w b,
             forall (FETCH : imem pc = Some i),
             forall (INST : decode_instr i = Some (Jal r)),
             forall (RW : reg r = Some w),
             forall (UPD : updm reg ra (pc.+1) = Some reg'),
             forall (VALID : valid_jmp pc w = b),
             step (State imem dmem reg pc true) (State imem dmem reg' w b)
| step_syscall : forall imem dmem dmem' reg reg' pc pc' sc,
                 forall (FETCH : imem pc = None),
                 forall (NOUSERM : dmem pc = None),
                 forall (GETCALL : table pc = Some sc),
                 forall (CALL : sem sc (State imem dmem reg pc true) =
                                Some (State imem dmem' reg' pc' true)),
                 step (State imem dmem reg pc true)
                      (State imem dmem' reg' pc' true).

Inductive step_a : state -> state -> Prop :=
| step_attack : forall imem dmem dmem' reg reg' pc b
             (MSAME: domm dmem = domm dmem')
             (RSAME: domm reg = domm reg'),
             step_a (State imem dmem reg pc b)
                    (State imem dmem' reg' pc b).

(* Extending valid_jmp to a complete allowed CFG *)
Definition succ (st : state) (st' : state) : bool :=
  let '(State imem dmem reg pc _) := st in
  let '(State _ _ _ pc' _) := st' in
  match (imem pc) with
    | Some i =>
      match decode_instr i with
        | Some (Jump r) => valid_jmp pc pc'
        | Some (Jal r) => valid_jmp pc pc'
        | Some (Bnz r imm) => (pc' == pc .+1) || (pc' == pc + swcast imm)
        | None => false
        | _ => pc' == pc .+1
      end
    | None =>
      match dmem pc with
        | Some _ => false
        | None =>
          match table pc with
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

Definition all_attacker (xs : seq state) : Prop :=
  forall x1 x2, In2 x1 x2 xs -> step_a x1 x2.

Definition all_stuck (xs : seq state) : Prop :=
  forall x, x \in xs -> ~ exists s, step x s.

Definition stopping (xs : seq state) : Prop :=
  all_attacker xs /\ all_stuck xs.

Program Instance abstract_cfi_machine : cfi_machine := {
  state := [eqType of state];
  initial s := initial s;

  step := step;
  step_a := step_a;

  succ := succ;
  stopping := stopping
}.

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
  have IN' : asi \in (ast :: ast' :: axs)
    by rewrite inE IN orbT.
  auto.
Qed.

Lemma stuck_states_preserved_by_a asi tl :
  all_attacker (asi :: tl) ->
  ~~ cont asi ->
  forall asj, asj \in tl -> ~~ cont asj.
Proof.
  intros ALLATTACKER CONT asj IN.
  move: asi ALLATTACKER CONT.
  induction tl; intros.
  - done.
  - rewrite !inE in IN; case/orP: IN.
    + move=> /eqP ?; subst a.
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
      move => /IHtl {IHtl} IHtl; eapply IHtl; eauto.
Qed.

Lemma stuck_trace s s' xs s'' :
  interm (@cfi_step abstract_cfi_machine) (s :: xs) s s'' ->
  ~~ cont s ->
  s' \in s :: xs ->
  ~ exists s''', step s' s'''.
Proof.
  intros INTERM CONT IN (s''' & STEP).
  induction INTERM as [? ? STEP'|? ? ? ? STEP' INTERM'].
  - rewrite !inE in IN. case/orP: IN; move=> /eqP *; subst.
    + inv STEP; by discriminate.
    + destruct STEP' as [STEPA | STEPN].
      * inv STEPA; simpl in *;
        inv STEP; by discriminate.
      * inv STEPN; by discriminate.
  - rewrite !inE in IN; case/orP: IN => [/eqP ? | IN]; subst;
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
        exists s; exists s'; do 2 exists [::].
        simpl; repeat split; try (auto || intros ? ? IN2; by (destruct IN2)).
        intros ? IN [s0 STEP]; rewrite inE in IN; move/eqP in IN; subst.
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
          exists s; exists s'; exists [::]; exists xs.
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
          have IN: sv1 \in (sj :: hs) ++ sv1 :: (sv2 :: tl).
            by rewrite mem_cat !inE eqxx /= !orbT; auto.
          simpl ((sj :: hs) ++ sv1 :: sv2 :: tl) in IN.
          rewrite  Heq in IN.
          assert (EQ := interm_first_step INTERM); subst.
          eapply stuck_trace; eauto.
        + apply HCFI; by assumption.
    }
Qed.

End WithClasses.

Notation imemory mt := {fmap mword mt -> mword mt}.
Notation dmemory mt := {fmap mword mt -> mword mt}.
Notation registers mt := {fmap reg mt -> mword mt}.

End Abs.

Arguments Abs.State {_} _ _ _ _ _.

Canonical Abs.cfi_abs_state_eqType.
