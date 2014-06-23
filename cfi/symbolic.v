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
        {smems : axioms sm}.

Context {registers : Type}.
Context {sr : partial_map registers (reg t) (atom (word t) (@cfi_tag t))}.

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

Definition target_tagged (mem : @Symbolic.memory t sym_cfi) := True.
  (* forall src dst i i' sc, *)
  (*   valid_jmp src dst -> *)
  (*   get mem src = Some i@(INSTR (Some src)) /\ *)
  (*   (get mem dst = Some i'@(INSTR (Some dst)) \/ *)
  (*    get mem dst = None /\ Symbolic.get_syscall table dst = Some sc -> *)
  (*    (Symbolic.entry_tag sc) = INSTR (Some dst)). *)

(*We will need stronger assumption on symbolic system calls for fwd simulation?*)
Hypothesis syscall_preserves_instruction_tags :
  forall sc st st',
    instructions_tagged (Symbolic.mem st) ->
    Symbolic.sem sc st = Some st' ->
    instructions_tagged (Symbolic.mem st').

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
    
(* CH: I'm a bit skeptical about this; I thought we require quite a
   lot about how things are initially tagged
   TODO: What should this contain?
   - no violation
   - instructions tagged "the right way"
*)
Definition initial (s : Symbolic.state t) := 
  no_violation s /\ instructions_tagged (Symbolic.mem s).  

Program Instance symbolic_cfi_machine : cfi_machine t := {|
  state := Symbolic.state t;
  initial s := initial s;
  
  step := Symbolic.step table;
  step_a := step_a;
  
  get_pc s := common.val (Symbolic.pc s);
  
  succ := ssucc      
 |}.
Next Obligation.
  inversion H. reflexivity.
Qed.

Definition S xs :=
  exists s, xs = [s] /\ ~ exists s', Symbolic.step table s s'.


End WithClasses.

End Sym.
