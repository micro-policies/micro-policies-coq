Require Import Coq.Lists.List Coq.Arith.Arith Coq.ZArith.ZArith.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Require Import lib.utils lib.partial_maps.
Require Import lib.Integers.
Require Import common.common.
Require Import symbolic.symbolic.
Require Import symbolic.exec.
Require Import cfi.property.
Require Import cfi.rules.
Require Import cfi.classes.
Require Import lib.Coqlib.
Set Implicit Arguments.

Import ListNotations.

Module Sym.

Open Scope bool_scope.

Section WithClasses.

Context {t : machine_types}.
Context {ops : machine_ops t}.
Context {opss : machine_ops_spec ops}.

Import PartMaps.

Context {ids : @classes.cfi_id t}.

Variable cfg : id -> id -> bool.

Definition valid_jmp := classes.valid_jmp cfg.

Program Instance sym_cfi : Symbolic.params := {
  ttypes := cfi_tags;

  transfer := rules.cfi_handler cfg;

  internal_state := [eqType of unit]
}.

Local Notation memory := (Symbolic.memory t sym_cfi).
Local Notation registers := (Symbolic.registers t sym_cfi).

Variable table : list (Symbolic.syscall t).

(* The rest of the file is defining an instance of the cfi_machine *)

Definition no_violation (sst : Symbolic.state t) :=
  let '(Symbolic.State mem _ pc@tpc _) := sst in
  (forall i ti src,
    get mem pc = Some i@ti ->
    tpc = INSTR (Some src) ->
    exists dst,
        ti = INSTR (Some dst) /\ cfg src dst = true) /\
  (forall sc,
     get mem pc = None ->
     Symbolic.get_syscall table pc = Some sc ->
     forall src,
       tpc = INSTR (Some src) ->
       exists dst, (Symbolic.entry_tag sc) = INSTR (Some dst) /\ cfg src dst).

Inductive atom_equiv : atom (word t) (@cfi_tag t ids) -> atom (word t) (@cfi_tag t ids)
                       -> Prop :=
  | data_equiv : forall a a',
                   tag a = DATA ->
                   tag a' = DATA ->
                   atom_equiv a a'
  | instr_equiv : forall a a' id id',
                    tag a = INSTR id ->
                    tag a' = INSTR id' ->
                    a = a' ->
                    atom_equiv a a'.

Definition equiv {M : Type -> Type} {Key : Type}
           {M_class : partial_map M Key} :
           M (atom (word t) (@cfi_tag t ids)) -> M (atom (word t) (@cfi_tag t ids)) -> Prop :=
  pointwise atom_equiv.

Inductive step_a : Symbolic.state t ->
                   Symbolic.state t -> Prop :=
| step_attack : forall mem reg pc tpc int mem' reg'
                  (REQUIV: equiv reg reg')
                  (MEQUIV: equiv mem mem'),
                  step_a (Symbolic.State mem reg pc@tpc int)
                         (Symbolic.State mem' reg' pc@tpc int).

Lemma equiv_same_domain {M : Type -> Type} {Key : Type}
           {M_class : partial_map M Key }
           (m : M (atom (word t) cfi_tag)) (m' : M (atom (word t) cfi_tag)) :
  equiv m m' ->
  same_domain m m'.
Proof.
  intros EQUIV.
  intro k.
  assert (EQUIV' := EQUIV k).
  destruct (get m k); destruct (get m' k); auto.
Qed.

Local Notation "x .+1" := (Word.add x Word.one).

Open Scope word_scope.

Definition ssucc (st : Symbolic.state t) (st' : Symbolic.state t) : bool :=
  let pc_t := common.tag (Symbolic.pc st) in
  let pc_t' := common.tag (Symbolic.pc st') in
  let pc_s := common.val (Symbolic.pc st) in
  let pc_s' := common.val (Symbolic.pc st') in
  match (get (Symbolic.mem st) pc_s) with
    | Some i@DATA => false
    | Some i@(INSTR (Some src)) =>
      match decode_instr i with
        | Some (Jump r)
        | Some (Jal r) =>
          match (get (Symbolic.mem st) pc_s') with
            | Some _@(INSTR (Some dst)) =>
              cfg src dst
            | None =>
              match Symbolic.get_syscall table pc_s' with
                | Some sc => match Symbolic.entry_tag sc with
                               | INSTR (Some dst) =>
                                 cfg src dst
                               | _ => false
                             end
                | None => false
              end
            | _ => false
          end
        | Some (Bnz r imm) =>
          (pc_s' == pc_s .+1) || (pc_s' == pc_s + Word.casts imm)
        | None => false
        | _ => pc_s' == pc_s .+1
      end
    | Some i@(INSTR None) =>
      match decode_instr i with
        | Some (Jump r)
        | Some (Jal r) =>
          false
        | Some (Bnz r imm) =>
          (pc_s' == pc_s .+1) || (pc_s' == pc_s + Word.casts imm)
        | None => false
        | _ => pc_s' == pc_s .+1
      end
    | None =>
      match Symbolic.get_syscall table pc_s with
        | Some sc => true
        | None => false
      end
  end.

(*This should be enough for backwards refinement?*)
Definition instructions_tagged (mem : memory) :=
  forall addr i id,
    get mem addr = Some i@(INSTR (Some id)) ->
    word_to_id addr = Some id.

Definition entry_points_tagged (mem : memory) :=
  forall addr sc id,
    get mem addr = None ->
    Symbolic.get_syscall table addr = Some sc ->
    Symbolic.entry_tag sc = INSTR (Some id) ->
    word_to_id addr = Some id.

Definition valid_jmp_tagged (mem : memory) :=
  forall src dst,
    valid_jmp src dst = true ->
    (exists i, get mem src = Some i@(INSTR (word_to_id src))) /\
    ((exists i', get mem dst = Some i'@(INSTR (word_to_id dst))) \/
     get mem dst = None /\
     exists sc, Symbolic.get_syscall table dst = Some sc /\
                (Symbolic.entry_tag sc) = INSTR (word_to_id dst)).


(* These may be needed for forwards simulation, I will leave them out until
   I actually use them*)
(* Definition jumps_tagged (mem : memory) :=  *)
  (* forall addr i cfi_tg r, *)
  (*   get mem addr = Some i@(INSTR cfi_tg) -> *)
  (*   decode_instr i = Some (Jump _ r) -> *)
  (*   cfi_tg = Some addr. *)

(* Definition jals_tagged (mem : memory) :=  *)
  (* forall addr i cfi_tg r, *)
  (*   get mem addr = Some i@(INSTR cfi_tg) -> *)
  (*   decode_instr i = Some (Jal _ r) -> *)
  (*   cfi_tg = Some addr. *)

(*We will need stronger assumption on symbolic system calls for fwd simulation?*)
Hypothesis syscall_preserves_instruction_tags :
  forall sc st st',
    instructions_tagged (Symbolic.mem st) ->
    Symbolic.sem sc st = Some st' ->
    instructions_tagged (Symbolic.mem st').

Hypothesis syscall_preserves_valid_jmp_tags :
  forall sc st st',
    valid_jmp_tagged (Symbolic.mem st) ->
    Symbolic.sem sc st = Some st' ->
    valid_jmp_tagged (Symbolic.mem st').

Hypothesis syscall_preserves_entry_tags :
  forall sc st st',
    entry_points_tagged (Symbolic.mem st) ->
    Symbolic.sem sc st = Some st' ->
    entry_points_tagged (Symbolic.mem st').

(*Invariant (step) preservation theorems*)

Lemma itags_preserved_by_step (st : Symbolic.state t) (st' : Symbolic.state t) :
  instructions_tagged (Symbolic.mem st) ->
  Symbolic.step table st st' ->
  instructions_tagged (Symbolic.mem st').
Proof.
  intros INVARIANT STEP.
  inversion STEP;
  (*unfoldings and case analysis on tags*)
    repeat (
        match goal with
          | [H: Symbolic.next_state_pc _ _ _ = _ |- _] =>
            unfold Symbolic.next_state_pc in H
          | [H: Symbolic.next_state_reg _ _ _ _ = _ |- _] =>
            unfold Symbolic.next_state_reg in H
          | [H: Symbolic.next_state_reg_and_pc _ _ _ _ _ = _ |- _] =>
            unfold Symbolic.next_state_reg_and_pc in H
          | [H: Symbolic.next_state _ _ _ = Some _ |- _] =>
            unfold Symbolic.next_state in H; simpl in H
        end); match_inv; subst; try (simpl; assumption).
  + simpl in E. simpl. unfold instructions_tagged.
    intros addr i0 id GET.
    have [EQ|/eqP NEQ] := altP (addr =P w1); [simpl in EQ | simpl in NEQ]; subst.
    - intros. subst.
      apply PartMaps.get_upd_eq in E; try apply word_map_axioms.
      rewrite GET in E. congruence. auto.
    - apply PartMaps.get_upd_neq with (key' := addr) in E; try apply word_map_axioms.
      rewrite E in GET.
      specialize (INVARIANT _ _ _ GET); assumption.
      assumption.
  + simpl in E. simpl. unfold instructions_tagged.
    intros addr i0 id GET.
    have [EQ|/eqP NEQ] := altP (addr =P w1); [simpl in EQ | simpl in NEQ]; subst.
    - intros. subst.
      apply PartMaps.get_upd_eq in E; try apply word_map_axioms.
      rewrite GET in E. congruence. auto.
    - apply PartMaps.get_upd_neq with (key' := addr) in E; try apply word_map_axioms.
      rewrite E in GET.
      specialize (INVARIANT _ _ _ GET); assumption.
      assumption.
   + unfold Symbolic.run_syscall in CALL. simpl in CALL.
     match_inv;  eapply syscall_preserves_instruction_tags; eauto.
Qed.

Lemma valid_jmp_tagged_preserved_by_step
      (st : Symbolic.state t) (st' : Symbolic.state t) :
  valid_jmp_tagged (Symbolic.mem st) ->
  Symbolic.step table st st' ->
  valid_jmp_tagged (Symbolic.mem st').
Proof.
  intros INVARIANT STEP.
  inversion STEP;
    (*unfoldings and case analysis on tags*)
    repeat (
        match goal with
          | [H: Symbolic.next_state_pc _ _ _ = _ |- _] =>
            unfold Symbolic.next_state_pc in H
          | [H: Symbolic.next_state_reg _ _ _ _ = _ |- _] =>
            unfold Symbolic.next_state_reg in H
          | [H: Symbolic.next_state_reg_and_pc _ _ _ _ _ = _ |- _] =>
            unfold Symbolic.next_state_reg_and_pc in H
          | [H: Symbolic.next_state _ _ _ = Some _ |- _] =>
            unfold Symbolic.next_state in H; simpl in H
        end); match_inv; subst; try (simpl; assumption).
  + simpl in E. simpl. unfold valid_jmp_tagged.
    intros src dst VALID.
    unfold valid_jmp_tagged in INVARIANT. simpl in INVARIANT.
    specialize (INVARIANT _ _ VALID).
    destruct INVARIANT as [[isrc GET] [[idst GET'] | [GET' [sc TAG]]]].
    { have [EQ|/eqP NEQ] := altP (src =P w1); [simpl in EQ | simpl in NEQ]; subst.
      - rewrite GET in OLD. congruence.
      - have [EQ'|/eqP NEQ'] := altP (dst =P w1); [simpl in EQ' | simpl in NEQ']; subst.
        * rewrite OLD in GET'. congruence.
        * split.
          { apply PartMaps.get_upd_neq with (key' := src) in E; auto; try apply word_map_axioms.
            rewrite <- E in GET. eexists; eauto. }
          { left.
            apply PartMaps.get_upd_neq with (key' := dst) in E; auto; try apply word_map_axioms.
            rewrite <- E in GET'. eexists; eauto. }
    }
    { split.
      * have [EQ|/eqP NEQ] := altP (src =P w1); [simpl in EQ | simpl in NEQ]; subst.
        - rewrite GET in OLD. congruence.
        - exists isrc.
          eapply PartMaps.get_upd_neq in E; eauto; try apply word_map_axioms.
          rewrite <- E in GET. assumption.
      * right.
        split.
        - have [EQ|/eqP NEQ] := altP (dst =P w1); [simpl in EQ | simpl in NEQ]; subst.
          + apply PartMaps.upd_inv in E. destruct E as [? E].
            rewrite E in GET'. congruence.
          + eapply PartMaps.get_upd_neq in E; eauto; try apply word_map_axioms.
            rewrite E. assumption.
        - exists sc. assumption.
    }
  + simpl in E. simpl. unfold valid_jmp_tagged.
    intros src dst VALID.
    unfold valid_jmp_tagged in INVARIANT. simpl in INVARIANT.
    specialize (INVARIANT _ _ VALID).
    destruct INVARIANT as [[isrc GET] [[idst GET'] | [GET' [sc TAG]]]].
    { have [EQ|/eqP NEQ] := altP (src =P w1); [simpl in EQ | simpl in NEQ]; subst.
      - rewrite GET in OLD. congruence.
      - have [EQ'|/eqP NEQ'] := altP (dst =P w1); [simpl in EQ' | simpl in NEQ']; subst.
        * rewrite OLD in GET'. congruence.
        * split.
          { apply PartMaps.get_upd_neq with (key' := src) in E; auto; try apply word_map_axioms.
            rewrite <- E in GET. eexists; eauto. }
          { left.
            apply PartMaps.get_upd_neq with (key' := dst) in E; auto; try apply word_map_axioms.
            rewrite <- E in GET'. eexists; eauto. }
    }
    { split.
      * have [EQ|/eqP NEQ] := altP (src =P w1); [simpl in EQ | simpl in NEQ]; subst.
        - rewrite GET in OLD. congruence.
        - exists isrc.
          eapply PartMaps.get_upd_neq in E; eauto; try apply word_map_axioms.
          rewrite <- E in GET. assumption.
      * right.
        split.
        - have [EQ|/eqP NEQ] := altP (dst =P w1); [simpl in EQ | simpl in NEQ]; subst.
          + apply PartMaps.upd_inv in E. destruct E as [? E].
            rewrite E in GET'. congruence.
          + eapply PartMaps.get_upd_neq in E; eauto; try apply word_map_axioms.
            rewrite E. assumption.
        - exists sc. assumption.
    }
  +  unfold Symbolic.run_syscall in CALL. simpl in CALL.
     match_inv;  eapply syscall_preserves_valid_jmp_tags; eauto.
Qed.

Lemma entry_point_tags_preserved_by_step
      (st : Symbolic.state t) (st' : Symbolic.state t) :
  entry_points_tagged (Symbolic.mem st) ->
  Symbolic.step table st st' ->
  entry_points_tagged (Symbolic.mem st').
Proof.
  intros INVARIANT STEP.
  inversion STEP;
  (*unfoldings and case analysis on tags*)
    repeat (
        match goal with
          | [H: Symbolic.next_state_pc _ _ _ = _ |- _] =>
            unfold Symbolic.next_state_pc in H
          | [H: Symbolic.next_state_reg _ _ _ _ = _ |- _] =>
            unfold Symbolic.next_state_reg in H
          | [H: Symbolic.next_state_reg_and_pc _ _ _ _ _ = _ |- _] =>
            unfold Symbolic.next_state_reg_and_pc in H
          | [H: Symbolic.next_state _ _ _ = Some _ |- _] =>
            unfold Symbolic.next_state in H; simpl in H
        end); match_inv; subst; try (simpl; assumption).
  + simpl in E. simpl.
    intros addr sc id GET' CALL ETAG.
    have [EQ|/eqP NEQ] := altP (addr =P w1); [simpl in EQ | simpl in NEQ]; subst.
    - intros. subst.
      apply PartMaps.get_upd_eq in E; try apply word_map_axioms.
      rewrite GET' in E. congruence. auto.
    - apply PartMaps.get_upd_neq with (key' := addr) in E; auto; try apply word_map_axioms.
      rewrite E in GET'. unfold entry_points_tagged in INVARIANT.
      specialize (INVARIANT _ _ _ GET' CALL ETAG); assumption.
  + simpl in E. simpl.
    intros addr sc id GET' CALL ETAG.
    have [EQ|/eqP NEQ] := altP (addr =P w1); [simpl in EQ | simpl in NEQ]; subst.
    - intros. subst.
      apply PartMaps.get_upd_eq in E; try apply word_map_axioms.
      rewrite GET' in E. congruence. auto.
    - apply PartMaps.get_upd_neq with (key' := addr) in E; auto; try apply word_map_axioms.
      rewrite E in GET'. unfold entry_points_tagged in INVARIANT.
      specialize (INVARIANT _ _ _ GET' CALL ETAG); assumption.
  + unfold Symbolic.run_syscall in CALL. simpl in CALL.
     match_inv;  eapply syscall_preserves_entry_tags; eauto.
Qed.

Lemma itags_preserved_by_step_a (st : Symbolic.state t) (st' : Symbolic.state t) :
  instructions_tagged (Symbolic.mem st) ->
  step_a st st' ->
  instructions_tagged (Symbolic.mem st').
Proof.
  intros INV STEP.
  destruct STEP.
  simpl. intros addr i0 id0 GET.
  assert (MEQUIV' := MEQUIV addr).
  rewrite GET in MEQUIV'.
  destruct (get mem addr) eqn:GET'.
  - inv MEQUIV'.
    + simpl in H0. congruence.
    + specialize (INV _ _ _ GET'). assumption.
  - destruct MEQUIV'.
Qed.

Lemma valid_jmp_tagged_preserved_by_step_a
      (st : Symbolic.state t) (st' : Symbolic.state t) :
  valid_jmp_tagged (Symbolic.mem st) ->
  step_a st st' ->
  valid_jmp_tagged (Symbolic.mem st').
Proof.
  intros INVARIANT STEP.
  destruct STEP.
  simpl; intros src dst VALID. unfold valid_jmp_tagged in INVARIANT.
  assert (MEQUIVS := MEQUIV src).
  assert (MEQUIVD := MEQUIV dst).
  destruct (INVARIANT _ _ VALID) as [[isrc GET] [[idst GET'] | [GET' [sc [CALL TAG]]]]];
    clear INVARIANT.
  { rewrite GET in MEQUIVS; rewrite GET' in MEQUIVD.
    split.
    - destruct (get mem' src) eqn:GETS.
      + inversion MEQUIVS; subst.
        * simpl in H; congruence.
        * eexists; eauto.
      + destruct MEQUIVS.
    - destruct (get mem' dst) eqn:GETD.
      + inv MEQUIVD.
        * simpl in H. congruence.
        * left. eexists; eauto.
      + destruct MEQUIVD.
  }
  { rewrite GET in MEQUIVS. rewrite GET' in MEQUIVD.
    split.
    - destruct (get mem' src) eqn:GETS.
      + inv MEQUIVS.
        * simpl in H; congruence.
        * eexists; eauto.
      + destruct MEQUIVS.
    - destruct (get mem' dst) eqn:GETD.
      + destruct MEQUIVD.
      + right. split; [auto | eexists; eauto].
  }
Qed.

Lemma entry_point_tags_preserved_by_step_a
      (st : Symbolic.state t) (st' : Symbolic.state t) :
  entry_points_tagged (Symbolic.mem st) ->
  step_a st st' ->
  entry_points_tagged (Symbolic.mem st').
Proof.
  intros INV STEP addr sc id GET' CALL ETAG.
  destruct STEP.
  specialize ( MEQUIV addr).
  unfold entry_points_tagged in INV.
  rewrite GET' in MEQUIV.
  destruct (get mem addr) eqn:GET.
  - destruct MEQUIV.
  - apply (INV _ _ _ GET CALL ETAG).
Qed.

Lemma data_pc_no_violation : forall s,
  tag (Symbolic.pc s) = DATA ->
  no_violation s.
Proof.
  intros. destruct s. destruct pc as [pc tpc]. simpl. split; intros;
  simpl in H; congruence.
Qed.

Hint Resolve itags_preserved_by_step : invariant_db.
Hint Resolve itags_preserved_by_step_a : invariant_db.
Hint Resolve entry_point_tags_preserved_by_step : invariant_db.
Hint Resolve entry_point_tags_preserved_by_step_a : invariant_db.
Hint Resolve valid_jmp_tagged_preserved_by_step : invariant_db.
Hint Resolve valid_jmp_tagged_preserved_by_step_a : invariant_db.

Definition invariants st :=
  instructions_tagged (Symbolic.mem st) /\
  valid_jmp_tagged (Symbolic.mem st) /\
  entry_points_tagged (Symbolic.mem st).

Lemma invariants_preserved_by_step st st' :
  invariants st ->
  Symbolic.step table st st' ->
  invariants st'.
Proof.
  intros INV STEP.
  destruct INV as [ITG [VTG ETG]].
  split; eauto with invariant_db.
Qed.

Lemma invariants_preserved_by_step_a st st' :
  invariants st ->
  step_a st st' ->
  invariants st'.
Proof.
  intros INV STEP.
  destruct INV as [ITG [VTG ETG]].
  split; eauto with invariant_db.
Qed.

Definition initial (s : Symbolic.state t) :=
  (common.tag (Symbolic.pc s)) = DATA /\
  invariants s.

Definition all_attacker xs : Prop :=
  forall x1 x2, In2 x1 x2 xs -> step_a x1 x2.

Definition all_stuck xs : Prop :=
  forall x, In x xs -> ~ exists s, Symbolic.step table x s.

Definition stopping xs : Prop :=
  all_attacker xs /\ all_stuck xs.

Lemma all_attacker_step st st' xs :
  step_a st st' ->
  all_attacker (st' :: xs) ->
  all_attacker (st :: st' :: xs).
Proof.
  intros STEP ALLA si sj IN2.
  destruct IN2 as [[? ?] | IN2]; subst; auto.
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

Program Instance symbolic_cfi_machine : cfi_machine := {|
  state := Symbolic.state t;
  initial s := initial s;

  step := Symbolic.step table;
  step_a := step_a;

  succ := ssucc;
  stopping := stopping
 |}.

Import DoNotation.
Import Vector.VectorNotations.

Definition get_ti sst :=
  match get (Symbolic.mem sst) (common.val (Symbolic.pc sst)) with
    | Some i@ti => Some ti
    | None =>
      match Symbolic.get_syscall table (common.val (Symbolic.pc sst)) with
        | Some sc => Some (Symbolic.entry_tag sc)
        | None => None
      end
  end.

Definition violation sst :=
  let 'pc@tpc := Symbolic.pc sst in
  match get_ti sst with
    | Some ti =>
      match tpc with
        | INSTR (Some src) =>
          match ti with
            | INSTR (Some dst) =>
              cfg src dst = false
            | _ => true
          end
        | _ => match ti with
                 | INSTR _ => false
                 | DATA => true
               end
      end
    | None => true
  end.

Lemma attacker_preserves_tpc_ti sst sst':
  step_a sst sst' ->
  (Symbolic.pc sst = Symbolic.pc sst') /\
  (get_ti sst = get_ti sst').
Proof.
  intro STEP.
  inv STEP.
  split.
  - by reflexivity.
  - specialize (MEQUIV pc).
    unfold get_ti.
    simpl.
    destruct (get mem pc) as [[i ti]|] eqn:GET.
    { destruct (get mem' pc) as[[i' ti']|] eqn:GET'.
      - inversion MEQUIV as [? ? EQ1 EQ2 EQ3 EQ4|? ? ? ? EQ1 EQ2 EQ3]; subst.
        + simpl in EQ1, EQ2. subst. by reflexivity.
        + inv EQ3. by reflexivity.
      - by destruct MEQUIV.
    }
    { destruct (get mem' pc) as[[i' ti']|] eqn:GET'.
      - destruct MEQUIV.
      - by reflexivity.
    }
Qed.

Lemma violation_preserved_by_step_a sst sst' :
  violation sst ->
  step_a sst sst' ->
  violation sst'.
Proof.
  intros VIO STEP.
  unfold violation in *.
  destruct (attacker_preserves_tpc_ti STEP) as [TPC TI].
  rewrite <- TPC, TI in *.
  by assumption.
Qed.

Lemma violation_preserved_by_exec_a sst sst' :
  violation sst ->
  exec step_a sst sst' ->
  violation sst'.
Proof.
  intros VIO EXEC.
  induction EXEC.
  - by assumption.
  - eauto using violation_preserved_by_step_a.
Qed.

Lemma succ_false_implies_violation sst sst' :
  invariants sst -> (*invariants were not used after changing to ids*)
  ssucc sst sst' = false ->
  step sst sst' ->
  False \/ violation sst'.
Proof.
  intros INV SUCC STEP.
  destruct INV as [ITG [VTG ETG]].
  unfold ssucc in SUCC.
  inv STEP; simpl in *;
  rewrite PC in SUCC; try rewrite INST in SUCC;
  repeat (
      match goal with
        | [H: Symbolic.next_state_pc _ _ _ = _ |- _] =>
          unfold Symbolic.next_state_pc in H
        | [H: Symbolic.next_state_reg _ _ _ _ = _ |- _] =>
          unfold Symbolic.next_state_reg in H
        | [H: Symbolic.next_state_reg_and_pc _ _ _ _ _ = _ |- _] =>
          unfold Symbolic.next_state_reg_and_pc in H
        | [H: Symbolic.next_state _ _ _ = Some _ |- _] =>
          unfold Symbolic.next_state in H; simpl in H
      end); subst; match_inv; simpl in SUCC;
  try match goal with
        | [H: _ || _ = false |- _] =>
          apply orb_false_iff in H;
            destruct H as [? ?];
            destruct (w == 0);
            unfold pc' in *
      end;
  try match goal with
        | [H: (?A == ?A) = false |- _] =>
          by rewrite eqxx in H
      end;
  right; unfold violation;
  simpl; unfold get_ti; simpl in *;
  repeat match goal with
        |[H: ?Expr = _ |- context[match ?Expr with _ => _ end]] =>
         rewrite H
      end; by auto.
Qed.

Lemma is_violation_implies_stop sst umvec :
  violation sst ->
  build_ivec table sst = Some umvec ->
  Symbolic.transfer umvec = None.
Proof.
  intros VIO UMVEC.
  unfold violation in VIO.
  destruct sst as [mem reg [pc tpc] int].
  unfold build_ivec in UMVEC.
  simpl in UMVEC, VIO.
  unfold get_ti in VIO. simpl in VIO.
  destruct (get mem pc) as [[i itg]|] eqn:GET.
  - rewrite GET in VIO UMVEC.
    destruct tpc as [[src|]|], itg as [[dst|]|];
      try (by inversion VIO);
      simpl in UMVEC;
      unfold bind in UMVEC;
      repeat match goal with
               | [H: match ?Expr with _ => _ end = _, H1: ?Expr = _ |- _] =>
             rewrite H1 in H
               | [H: match ?Expr with _ => _ end = _ |- _ ] =>
                 destruct Expr eqn:?
               | [H: match ?Expr with _ => _ end _ = _ |- _ ] =>
                 destruct Expr eqn:?
         end;
      inv UMVEC; try reflexivity;
      unfold Symbolic.transfer; simpl; unfold cfi_handler;
      try rewrite VIO; try reflexivity.
    destruct (tag a1); by reflexivity.
  -  (*get mem pc = None*)
    rewrite GET in VIO UMVEC.
    destruct (Symbolic.get_syscall table pc) as [sc|] eqn:GETCALL.
    + destruct tpc as [[src|]|], (Symbolic.entry_tag sc) as [[dst|]|];
      try (by inversion VIO);
      inv UMVEC; try reflexivity.
      unfold Symbolic.transfer; simpl; unfold cfi_handler;
      try rewrite VIO; by reflexivity.
    + by discriminate.
Qed.

End WithClasses.

Notation memory t ids vj := (Symbolic.memory t (@sym_cfi t ids vj)).
Notation registers t ids vj := (Symbolic.registers t (@sym_cfi t ids vj)).

End Sym.
