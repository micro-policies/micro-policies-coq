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

Class sym_cfi_params := {
  memory : Type;
  registers : Type;

  get_mem : memory -> word t -> option (atom (word t) (@cfi_tag t));
  upd_mem : memory -> word t -> atom (word t) (@cfi_tag t) -> option memory;

  get_reg : registers -> reg t -> option (atom (word t) (@cfi_tag t));
  upd_reg : registers -> reg t -> atom (word t) (@cfi_tag t) -> option registers

}.

Context {scp : sym_cfi_params}.

Variable valid_jmp : word t -> word t -> bool.

Program Instance sym_cfi : (Symbolic.symbolic_params t) := {
  memory := memory;
  registers := registers;
  tag := cfi_tag;

  get_mem := get_mem;
  upd_mem := upd_mem;

  get_reg := get_reg;
  upd_reg := upd_reg;

  handler := cfi_rules.handler valid_jmp;

  internal_state := unit
}.

Variable table : list (Symbolic.syscall t).
                                 
(* Attacker steps will be implemented later*)
Variable step_a : Symbolic.state t -> Symbolic.state t -> Prop.

Local Notation "x .+1" := (add_word x (Z_to_word 1)) (at level 60).

Open Scope word_scope.

Definition csucc (st : Abstract.state t) (st' : Abstract.state t) : bool :=
  let pc_t' := common.tag (Abstract.pc st') in
  let pc_t := common.tag (Abstract.pc st) in
  let pc_s := common.val (Abstract.pc st) in
  let pc_s' := common.val (Abstract.pc st') in
  match (get_mem (Abstract.mem st) pc_s) with
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
  
  succ := csucc      
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
