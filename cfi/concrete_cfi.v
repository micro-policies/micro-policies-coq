Require Import Coq.Lists.List Coq.Arith.Arith Coq.ZArith.ZArith.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Require Import lib.utils lib.partial_maps.
Require Import common.common.
Require Import .symbolic.
Require Import cfi.cfi.
Require Import cfi.cfi_rules.
Require Import lib.Coqlib.

Set Implicit Arguments.
Open Scope Z_scope.

Section ConcreteCFI.

Context (t : machine_types).
Context {cp : Concrete.concrete_params t}.
Context {sp : Concrete.params_spec cp}.
Context (ops : machine_ops t).


(*allow attacker to change only things tagged USER DATA! all the rest should be equiv*)

Definition is_instr_tag (ti : word t) := 
  match concrete_kernel.word_to_tag ti with
    | Some (USER (INSTR _)) => true
    | _ => false
  end.

Definition is_entry_Tag (ti : word t) :=
  match concrete_kernel.word_to_tag ti with
    | Some ENTRY => true
    | _ => false
  end.

(* But not a syscall tag*)
Definition is_user_tag (ti : word t) :=
  match concrete_kernel.word_to_tag ti with
    | Some (USER (INSTR SYSCALL)) => false
    | Some (USER _) => true
    | _ => false
  end.


(* Definition of state equivelance from an attacker point*)

Inductive mem_equiv : Concrete.memory t -> Concrete.memory t -> Prop :=
  | mequiv : forall w m1 v1 t1 m2 v2 t2
               (MEM1 : Concrete.get_mem m1 w = Some v1@t1)
               (MEM2 : Concrete.get_mem m2 w = Some v2@t2),
               t1 = t2 /\ 
               ((t1 = Concrete.TKernel \/ is_instr_tag t1 = true \/ 
                is_entry_tag t1 = true) -> v1 = v2) ->
               mem_equiv m1 m2.

Inductive reg_equiv : Concrete.registers t -> Concrete.registers t -> Prop :=
  | requiv : forall r regs1 v1 t1 regs2 v2 t2
               (REG1 : Concrete.get_reg regs1 r = v1@t1)
               (REG2 : Concrete.get_reg regs2 r = v2@t2),
               (t1 = t2 /\ 
                t1 = Concrete.TKernel ->
                v1 = v2) ->
               reg_equiv regs1 regs2.

Inductive states_equiv : Concrete.state t -> Concrete.state t -> Prop :=
  | sequiv : forall s1 s2
               (MEMEQ : mem_equiv (Concrete.mem s1) (Concrete.mem s2))
               (REGEQ : reg_equiv (Concrete.regs s1) (Concrete.regs s2))
               (PCEQ : Concrete.pc s1 = Concrete.pc s2)
               (EPCEQ : Concrete.epc s1 = Concrete.epc s2)
               (CACHEEQ : Concrete.cache s1 = Concrete.cache s2),
               states_equiv s1 s2.

Inductive step_a : Concrete.state t -> Concrete.state t -> Prop :=
  | step_attack : forall s1 s2
                    (USER : is_user_tag (common.tag (Concrete.pc s1)) = true)
                    (NKERNEL : forall s3, (Concrete.step ops masks s1 s3 -> Concrete.is_kernel_tag ops (common.tag (Concrete.pc s3)) = false))
                    (SEQ : states_equiv s1 s2),
                    step_a s1 s2.

Variable valid_jmp : word t -> word t -> bool.

Local Notation "x .+1" := (add_word x (Z_to_word 1)) (at level 60).
Local Open Scope word_scope.
Definition csucc (st : Concrete.state t) (st' : Concrete.state t) : bool :=
  let pc_t' := common.tag (Concrete.pc st') in
  let pc_s := common.val (Concrete.pc st) in
  let pc_s' := common.val (Concrete.pc st') in
  if Concrete.is_kernel_tag ops pc_t' then true else
  match (Concrete.get_mem (Concrete.mem st) pc_s) with
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

Definition cinitial (s : Concrete.state t) := True.

Variable masks : Concrete.Masks.

Program Instance concrete_cfi_machine : cfi_machine t := {|
  state := Concrete.state t;
  initial s := cinitial s;
  
  step s1 s2 := Concrete.step ops masks s1 s2;
  step_a := step_a;

  get_pc s := common.val (Concrete.pc s);

  succ := csucc
 |}.
Next Obligation.
Admitted.
Next Obligation.
Proof.
  inversion H as [s1 s2 USER NKERNEL SEQ]; subst.
  * inversion SEQ; subst.
    rewrite PCEQ; reflexivity.
Qed.

End ConcreteCFI.

(* ask about these*)
Arguments Concrete.state t {cp}.
Arguments Concrete.memory t {_}.
Arguments Concrete.registers t {_}.
Arguments Concrete.TNone {t _}.
Arguments Concrete.TKernel {t _}.
