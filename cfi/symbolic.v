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

(* The rest of the file is only used for CFI theorem ... so probably
   move somewhere else? *)

Variable table : list (Symbolic.syscall t).

Definition no_violation (sst : @Symbolic.state t sym_cfi) :=
  let '(Symbolic.State mem _ pc@tpc _) := sst in
  forall i ti src,
    get mem pc = Some i@ti ->
    tpc = INSTR (Some src) ->
    exists dst, 
        ti = INSTR (Some dst) /\ valid_jmp src dst = true.

Inductive atom_equiv : atom (word t) (@cfi_tag t) -> atom (word t) (@cfi_tag t) 
                       -> Prop :=
  | data_equiv : forall a a', 
                   common.tag a = DATA ->
                   common.tag a' = DATA ->
                   atom_equiv a a'
  | instr_equiv : forall a a' id id',
                    common.tag a = INSTR id ->
                    common.tag a' = INSTR id' ->
                    a = a' ->
                    atom_equiv a a'.

Definition reg_equiv (reg : registers) (reg' : registers) : Prop :=
  forall w,
    match get reg w, get reg' w with
    | None  , None   => True
    | Some a, Some a' => atom_equiv a a'
    | _     , _      => False
    end.

Definition mem_equiv (mem : memory) (mem' : memory) : Prop :=
  forall w,
    match get mem w, get mem' w with
    | None  , None   => True
    | Some a, Some a' => atom_equiv a a'
    | _     , _      => False
    end.

Inductive step_a : (@Symbolic.state t sym_cfi) -> 
                   (@Symbolic.state t sym_cfi) -> Prop :=
| step_attack : forall mem reg pc int mem' reg',
                  no_violation (Symbolic.State mem reg pc int) ->
                  reg_equiv reg reg' ->
                  mem_equiv mem mem' ->
                  step_a (Symbolic.State mem reg pc int) 
                         (Symbolic.State mem' reg' pc int).
                  
Local Notation "x .+1" := (add_word x (Z_to_word 1)) (at level 60).

Open Scope word_scope.

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
  inversion H. reflexivity.
Qed.

Definition V s s' := 
  ssucc s s' = false.

Definition S xs :=
  exists s, xs = [s] /\ ~ exists s', cfi_step symbolic_cfi_machine s s'.

End WithClasses.

End SymbolicCFI.
