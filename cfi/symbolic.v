Require Import Coq.Lists.List Coq.Arith.Arith Coq.ZArith.ZArith.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Require Import lib.utils lib.partial_maps.
Require Import common.common.
Require Import symbolic.symbolic.
Require Import cfi.property.
Require Import cfi.rules.
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

Context {memory : Type}
        {sm : partial_map memory (word t) (atom (word t) (@cfi_tag t))}
        {smems : axioms sm}
        {registers : Type}
        {sr : partial_map registers (reg t) (atom (word t) (@cfi_tag t))}.

Variable valid_jmp : word t -> word t -> bool.

Program Instance sym_cfi : (Symbolic.symbolic_params) := {
  tag := cfi_tag_eqType;

  handler := rules.cfi_handler valid_jmp;

  internal_state := unit;

  memory := memory;
  sm := sm;

  registers := registers;
  sr := sr
}.

Variable table : list (Symbolic.syscall t).

(* The rest of the file is defining an instance of the cfi_machine *)

Definition no_violation (sst : Symbolic.state t) :=
  let '(Symbolic.State mem _ pc@tpc _) := sst in
  (forall i ti src,
    get mem pc = Some i@ti ->
    tpc = INSTR (Some src) ->
    exists dst, 
        ti = INSTR (Some dst) /\ valid_jmp src dst = true) /\
  (forall sc, 
     get mem pc = None -> 
     Symbolic.get_syscall table pc = Some sc ->
     forall src, 
       tpc = INSTR (Some src) ->
       exists dst, (Symbolic.entry_tag sc) = INSTR (Some dst) /\ valid_jmp src dst).

Inductive atom_equiv : atom (word t) (@cfi_tag t) -> atom (word t) (@cfi_tag t) 
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

Definition equiv {M : Type} {Key : Type} 
           {M_class : partial_map M Key (atom (word t) cfi_tag)} :
           M -> M -> Prop :=
  pointwise atom_equiv.

Inductive step_a : Symbolic.state t ->
                   Symbolic.state t -> Prop :=
| step_attack : forall mem reg pc tpc int mem' reg' i id
                  (FETCH: get mem pc = Some i@(INSTR id))
                  (NOV: no_violation (Symbolic.State mem reg pc@tpc int))
                  (REQUIV: equiv reg reg')
                  (MEQUIV: equiv mem mem'),
                  step_a (Symbolic.State mem reg pc@tpc int)
                         (Symbolic.State mem' reg' pc@tpc int).

Lemma equiv_same_domain {M : Type} {Key : Type} 
           {M_class : partial_map M Key (atom (word t) cfi_tag)}
           (m : M) (m' : M) :
  equiv m m' ->
  same_domain m m'.
Proof.
  intros EQUIV.
  intro k.
  assert (EQUIV' := EQUIV k).
  destruct (get m k); destruct (get m' k); auto.
Qed.
                  
Local Notation "x .+1" := (add_word x (Z_to_word 1)).

Open Scope word_scope.

Definition ssucc (st : Symbolic.state t) (st' : Symbolic.state t) : bool :=
  let pc_t' := common.tag (Symbolic.pc st') in
  let pc_t := common.tag (Symbolic.pc st) in
  let pc_s := common.val (Symbolic.pc st) in
  let pc_s' := common.val (Symbolic.pc st') in
  match (get (Symbolic.mem st) pc_s) with
    | Some i@DATA => false
    | Some i@(INSTR _) =>
      match decode_instr i with
        | Some (Jump r) => valid_jmp pc_s pc_s'
        | Some (Jal r) => valid_jmp pc_s pc_s'
        | Some (Bnz r imm) => 
          (pc_s' == pc_s .+1) || (pc_s' == pc_s + imm_to_word imm)
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
Definition instructions_tagged (mem : @Symbolic.memory t sym_cfi) :=
  forall addr i (id : word t), 
    get mem addr = Some i@(INSTR (Some id)) ->
    id = addr. 

Definition entry_points_tagged (mem : @Symbolic.memory t sym_cfi) :=
  forall addr sc id,
    get mem addr = None ->
    Symbolic.get_syscall table addr = Some sc ->
    Symbolic.entry_tag sc = INSTR (Some id) ->
    id = addr.

Definition valid_jmp_tagged (mem : @Symbolic.memory t sym_cfi) := 
  forall src dst,
    valid_jmp src dst = true ->
    (exists i, get mem src = Some i@(INSTR (Some src))) /\
    ((exists i', get mem dst = Some i'@(INSTR (Some dst))) \/
     get mem dst = None /\
     exists sc, Symbolic.get_syscall table dst = Some sc /\
                (Symbolic.entry_tag sc) = INSTR (Some dst)).


(* These may be needed for forwards simulation, I will leave them out until
   I actually use them*)
Definition jumps_tagged (mem : @Symbolic.memory t sym_cfi) := True.
  (* forall addr i cfi_tg r, *)
  (*   get mem addr = Some i@(INSTR cfi_tg) -> *)
  (*   decode_instr i = Some (Jump _ r) -> *)
  (*   cfi_tg = Some addr. *)

Definition jals_tagged (mem : @Symbolic.memory t sym_cfi) := True.
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
      apply PartMaps.get_upd_eq in E.
      rewrite GET in E. congruence. auto.
    - apply PartMaps.get_upd_neq with (key' := addr) in E. 
      rewrite E in GET.
      specialize (INVARIANT _ _ _ GET); assumption.
      assumption. assumption.
  + simpl in E. simpl. unfold instructions_tagged.
    intros addr i0 id GET.
    have [EQ|/eqP NEQ] := altP (addr =P w1); [simpl in EQ | simpl in NEQ]; subst.
    - intros. subst.
      apply PartMaps.get_upd_eq in E.
      rewrite GET in E. congruence. auto.
    - apply PartMaps.get_upd_neq with (key' := addr) in E. 
      rewrite E in GET.
      specialize (INVARIANT _ _ _ GET); assumption.
      assumption. assumption.
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
          { apply PartMaps.get_upd_neq with (key' := src) in E; auto.
            rewrite <- E in GET. eexists; eauto. }
          { left.
            apply PartMaps.get_upd_neq with (key' := dst) in E; auto.
            rewrite <- E in GET'. eexists; eauto. }
    }
    { split.
      * have [EQ|/eqP NEQ] := altP (src =P w1); [simpl in EQ | simpl in NEQ]; subst.
        - rewrite GET in OLD. congruence.
        - exists isrc.
          eapply PartMaps.get_upd_neq in E; eauto.
          rewrite <- E in GET. assumption.
      * right. 
        split.
        - have [EQ|/eqP NEQ] := altP (dst =P w1); [simpl in EQ | simpl in NEQ]; subst.
          + apply PartMaps.upd_inv in E. destruct E as [? E].
            rewrite E in GET'. congruence.
          + eapply PartMaps.get_upd_neq in E; eauto.
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
          { apply PartMaps.get_upd_neq with (key' := src) in E; auto.
            rewrite <- E in GET. eexists; eauto. }
          { left.
            apply PartMaps.get_upd_neq with (key' := dst) in E; auto.
            rewrite <- E in GET'. eexists; eauto. }
    }
    { split.
      * have [EQ|/eqP NEQ] := altP (src =P w1); [simpl in EQ | simpl in NEQ]; subst.
        - rewrite GET in OLD. congruence.
        - exists isrc.
          eapply PartMaps.get_upd_neq in E; eauto.
          rewrite <- E in GET. assumption.
      * right. 
        split.
        - have [EQ|/eqP NEQ] := altP (dst =P w1); [simpl in EQ | simpl in NEQ]; subst.
          + apply PartMaps.upd_inv in E. destruct E as [? E].
            rewrite E in GET'. congruence.
          + eapply PartMaps.get_upd_neq in E; eauto.
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
      apply PartMaps.get_upd_eq in E.
      rewrite GET' in E. congruence. auto.
    - apply PartMaps.get_upd_neq with (key' := addr) in E; auto.
      rewrite E in GET'. unfold entry_points_tagged in INVARIANT.
      specialize (INVARIANT _ _ _ GET' CALL ETAG); assumption.
  + simpl in E. simpl.
    intros addr sc id GET' CALL ETAG.
    have [EQ|/eqP NEQ] := altP (addr =P w1); [simpl in EQ | simpl in NEQ]; subst.
    - intros. subst.
      apply PartMaps.get_upd_eq in E.
      rewrite GET' in E. congruence. auto.
    - apply PartMaps.get_upd_neq with (key' := addr) in E; auto.
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

Definition stopping xs :=
  exists s, xs = [s] /\ ~ exists s', Symbolic.step table s s'.

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

(*TODO: Move to symbolic*)
Definition build_mvec st : option (Symbolic.MVec (Symbolic.tag t)) :=
  let '(Symbolic.State mem reg pc@tpc int) := st in
  match get mem pc with
    | Some i =>
      match decode_instr (common.val i) with
        | Some op =>
          let part := @Symbolic.mkMVec (Symbolic.tag t) (opcode_of op) tpc (tag i) in
          match op return (Symbolic.mvec_operands (Symbolic.tag t) (Symbolic.nfields (opcode_of op)) ->
                           Symbolic.MVec (Symbolic.tag t)) -> option (Symbolic.MVec (Symbolic.tag t)) with
            | Nop => fun part => Some (part [])
            | Const n r => fun part => 
                do! old <- get reg r;
                Some (part [tag old])
            | Mov r1 r2 => fun part =>
              do! v1 <- get reg r1;
              do! v2 <- get reg r2;
              Some (part [(tag v1); (tag v2)])
            | Binop _ r1 r2 r3 => fun part =>
              do! v1 <- get reg r1;
              do! v2 <- get reg r2;
              do! v3 <- get reg r3;
              Some (part [(tag v1); (tag v2); (tag v3)])
            | Load  r1 r2 => fun part =>
              do! w1 <- get reg r1;
              do! w2 <- get mem (val w1);
              do! old <- get reg r2;
              Some (part [(tag w1); (tag w2); (tag old)])
            | Store  r1 r2 => fun part =>
              do! w1 <- get reg r1;
              do! w2 <- get reg r2;
              do! w3 <- get mem (val w1);
              Some (part [(tag w1); (tag w1); (tag w3)])
            | Jump  r => fun part =>
              do! w <- get reg r;
              Some (part [tag w])
            | Bnz  r n => fun part =>
              do! w <- get reg r;
              Some (part [tag w])
            | Jal  r => fun part =>
              do! w <- get reg r;
              do! old <- get reg ra;
              Some (part [tag w; tag old])
            | JumpEpc => fun _ => None
            | AddRule => fun _ => None
            | GetTag _ _ => fun _ => None
            | PutTag _ _ _ => fun _ => None
            | Halt => fun _ => None
          end part
        | None => None
      end
    | None => 
      match Symbolic.get_syscall table pc with
        | Some sc =>
          Some (@Symbolic.mkMVec (Symbolic.tag _) SERVICE tpc (Symbolic.entry_tag sc) (Vector.nil _))
        | None => None
      end 
  end.

Definition option_handler x := 
  match x with
    | Some v => Symbolic.handler v
    | None => None
  end.

Lemma succ_false_handler asi asj :
  invariants asi ->
  ssucc asi asj = false ->
  step asi asj ->
  option_handler (build_mvec asj) = None.
Proof.
  intros INV SUCC STEP.
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
      end); match_inv; subst; simpl in SUCC;
  try match goal with 
        | [H: _ || _ = false |- _] => 
          apply orb_false_iff in H;
            destruct H as [? ?];
            destruct (w == 0);
            unfold pc' in *
      end;
  try match goal with
        | [H: (?A == ?A) = false |- _] => 
      move/eqP:H => CONTRA; destruct (CONTRA erefl)
      end;
  simpl;
  repeat match goal with
    | [ |- option_handler match get ?Mem ?W with _ => _ end = _] => 
      destruct (get Mem W) eqn:GET
    | [ |- option_handler match decode_instr (val ?I) with _ => _ end = _] => 
      destruct (decode_instr (val I)) 
  end; try (destruct i0);
  try match goal with
    | [|- option_handler None = None] => unfold option_handler; reflexivity
  end; 
  destruct INV as [ITG [VTG ETG]]; simpl in *;
  unfold option_handler; simpl;
  try match goal with
    | |- context[get ?Reg ?R] => destruct (get Reg R)
         end;
  try match goal with
        | |- context[Some ?A] => destruct A; simpl
      end;
  try match goal with
    | |- context[get ?Reg ?R] => destruct (get Reg R)
         end;
  try match goal with
        | |- context[Some ?A] => destruct A; simpl
      end;
  try match goal with
        | |- context[get ?Reg ?R] => destruct (get Reg R)
      end;
  try match goal with
        | |- context[Some ?A] => destruct A; simpl
      end;
  try match goal with
    | [H: valid_jmp ?Pc ?W = false, H1: get ?Mem ?W = Some ?A |- _ ] =>
       destruct a as [v tg]; simpl;
       destruct tg as [[id|] |]; try reflexivity
  end;
 try match goal with
    | [|- match match ?Expr with _ => _ end with _ => _ end = None] => destruct Expr eqn:GETCALL
  end;
  unfold entry_points_tagged in ETG;
  try match goal with
        |[H: Symbolic.get_syscall _ _ = Some ?Sc |- _] =>
         destruct (Symbolic.entry_tag Sc) as [[id|]|] eqn:ETAG
      end;
  try reflexivity;
  try match goal with
    | [H: get ?Mem ?Pc = Some ?I@(INSTR (Some ?S)), H1: valid_jmp ?Pc ?W = false,
       H2: get ?Mem ?W = None,                                                 
       H3: Symbolic.get_syscall _ ?W  = Some ?Sc,
       H4: Symbolic.entry_tag _ = INSTR (Some _) |- _ ] =>
       assert (TG := ITG _ _ _ H); subst;
       assert (TG := ETG _ _ _ H2 H3 H4); subst;
       simpl; rewrite H1
    end;
  try match goal with
    | [H: get ?Mem ?Pc = Some ?I@(INSTR (Some ?S)), H1: valid_jmp ?Pc ?W = false,
       H2: get ?Mem ?W  = Some _@(INSTR (Some ?Id)) |- _ ] =>
       assert (TG := ITG _ _ _ H); subst;
       assert (TG := ITG _ _ _ H2); subst;
       rewrite H1
       end;
  try reflexivity;
  try (destruct tag1; reflexivity).
Qed.

End WithClasses.

End Sym.
