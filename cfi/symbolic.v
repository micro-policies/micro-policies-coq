Require Import Coq.Lists.List Coq.Arith.Arith Coq.ZArith.ZArith.
Require Import Coq.Classes.SetoidDec.
Require Import lib.utils.
Require Import concrete.common.
Require Import symbolic.symbolic.
Require Import cfi.cfi.
Require Import cfi.cfi_rules.
Set Implicit Arguments.

Import ListNotations.

Module SymbolicCFI.

Open Scope bool_scope.

Section WithClasses.

Context {t : machine_types}.
Context {ops : machine_ops t}.
Context {opss : machine_ops_spec ops}.

Import PartMaps.

Context {memory : Type}.
Context {sm : partial_map memory (word t) (atom (word t) (@cfi_tag t))}.

Context {registers : Type}.
Context {sr : partial_map registers (reg t) (atom (word t) (@cfi_tag t))}.

Variable valid_jmp : word t -> word t -> bool.

Program Instance sym_cfi : (Symbolic.symbolic_params) := {
  tag := cfi_tag;

  handler := cfi_rules.cfi_handler valid_jmp;

  internal_state := unit;

  memory := memory;
  sm := sm;

  registers := registers;
  sr := sr
}.

Variable table : list (Symbolic.syscall t).

(* TODO: Attacker steps will be implemented later *)
Variable step_a : Symbolic.state t -> Symbolic.state t -> Prop.

Local Notation "x .+1" := (add_word x (Z_to_word 1)) (at level 60).

Open Scope word_scope.

(* The rest of the file is only used for CFI theorem ... so probably
   move somewhere else? *)
Definition ssucc (st : Symbolic.state t) (st' : Symbolic.state t) : bool :=
  let pc_t' := common.tag (Symbolic.pc st') in
  let pc_t := common.tag (Symbolic.pc st) in
  let pc_s := common.val (Symbolic.pc st) in
  let pc_s' := common.val (Symbolic.pc st') in
  match (get (Symbolic.mem st) pc_s) with
    | Some i =>
      match decode_instr (common.val i) with
        | Some (Jump r) => valid_jmp pc_s pc_s'
        | Some (Jal r) => valid_jmp pc_s pc_s'
        | Some (Bnz r imm) => 
          (pc_s' ==b pc_s .+1) || (pc_s' ==b pc_s + imm_to_word imm)
        | None => false
        | _ => pc_s' ==b pc_s .+1
      end
    | None => false
  end.

Definition initial (s : Symbolic.state t) := True.

Program Instance symbolic_cfi_machine : cfi_machine t := {|
  state := Symbolic.state t;
  initial s := initial s;
  
  step := Symbolic.step table;
  step_a := step_a;

  get_pc s := common.val (Symbolic.pc s);
  
  succ := ssucc      
 |}.
Next Obligation.
Admitted.
Next Obligation.
Admitted.

Definition V s s' := 
  succ s s' = false.

Definition S xs :=
  exists s, xs = [s] /\ ~ exists s', cfi_step symbolic_cfi_machine s s'.

End WithClasses.

End SymbolicCFI.