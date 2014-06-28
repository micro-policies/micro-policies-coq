Require Import Coq.Lists.List Coq.Arith.Arith Coq.ZArith.ZArith.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Require Import lib.utils lib.partial_maps.
Require Import common.common.
Require Import concrete.concrete.
Require Import symbolic.symbolic.
Require Import cfi.symbolic.
Require Import cfi.property.
Require Import cfi.rules.
Require Import symbolic.rules.
Require Import lib.Coqlib.
Require Import symbolic.refinement_common.

Set Implicit Arguments.
Open Scope Z_scope.

Module Conc.
Section ConcreteSection.

Context {t : machine_types}
        {ops : machine_ops t}
        {cp : Concrete.concrete_params t}
        {csp : Concrete.params_spec cp}
        {e : @rules.encodable (@rules.cfi_tag_eqType t) t ops}.

Import PartMaps.
Context {memory : Type}
        {sm : partial_map memory (word t) (atom (word t) (@cfi_tag t))}
        {smems : axioms sm}
        {registers : Type}
        {sr : partial_map registers (reg t) (atom (word t) (@cfi_tag t))}.

Variable valid_jmp : word t -> word t -> bool.
(*allow attacker to change only things tagged USER DATA! all the rest should be equiv*)

Import PartMaps.

Definition no_violation (cst : Concrete.state t) :=
  let '(Concrete.mkState mem _  _ pc@tpc _) := cst in
  (forall i ti src,
    get mem pc = Some i@(encode (USER ti)) ->
    tpc = encode (USER (INSTR (Some src))) ->
    exists dst, 
        ti = INSTR (Some dst) /\ valid_jmp src dst = true) /\
  (forall i ti src,
     get mem pc = Some i@(encode (ENTRY ti)) ->
     tpc = encode (USER (INSTR (Some src))) ->
     exists dst, 
       ti = INSTR (Some dst) /\ valid_jmp src dst = true).

(*Defined in terms of atom_equiv for symbolic tags*)
(* TODO: as a sanity check, please prove reflexivity for this and
   the other attacker relations. That will ensure that the attacker
   can at least keep things the same. *)
Inductive atom_equiv : atom (word t) (word t) -> atom (word t) (word t) 
                       -> Prop :=
  | user_equiv : forall a a' v v' ut ut', 
                   a = v@(encode (USER ut)) ->
                   a' = v'@(encode (USER ut')) ->
                   Sym.atom_equiv v@ut v'@ut' ->
                   atom_equiv a a'
  | any_equiv : forall a a',
                    (~ exists ut, common.tag a = encode (USER ut)) ->
                    a = a' ->
                    atom_equiv a a'.


Definition equiv {M : Type} {Key : Type} 
           {M_class : partial_map M Key (atom (word t) (word t))} :
           M -> M -> Prop :=
  pointwise atom_equiv.

Definition reg_equiv (regs : Concrete.registers t) (regs' : Concrete.registers t) :=
  forall r,
    atom_equiv (TotalMaps.get regs r) (TotalMaps.get regs' r).

(* Do we also want to disallow attacker if the next step is KERNEL?
  Isn't the violation enough? *)
Inductive step_a : Concrete.state t ->
                   Concrete.state t -> Prop :=
| step_attack : forall mem reg cache pc tpc epc mem' reg' i id
                  (INUSER: word_lift (fun x => is_user x) tpc)
                  (FETCH: get mem pc = Some i@(encode (USER (INSTR id))))
                  (NOV: no_violation (Concrete.mkState mem reg cache pc@tpc epc))
                  (REQUIV: reg_equiv reg reg')
                  (MEQUIV: equiv mem mem'),
                  step_a (Concrete.mkState mem reg cache pc@tpc epc)
                         (Concrete.mkState mem' reg' cache pc@tpc epc).

Local Notation "x .+1" := (add_word x (Z_to_word 1)).
Local Open Scope word_scope.
Definition csucc (st : Concrete.state t) (st' : Concrete.state t) : bool :=
  let pc_s := common.val (Concrete.pc st) in
  let pc_s' := common.val (Concrete.pc st') in
  if in_kernel st || in_kernel st' then true else
  match (get (Concrete.mem st) pc_s) with
    | Some i =>
      match decode_instr (common.val i) with
        | Some (Jump r) => valid_jmp pc_s pc_s'
        | Some (Jal r) => valid_jmp pc_s pc_s'
        | Some (Bnz r imm) => 
          (pc_s' == pc_s .+1) || (pc_s' == pc_s + imm_to_word imm)
        | None => false
        | _ => pc_s' == pc_s .+1
      end
    | None => false
  end.

Definition sp := @Sym.sym_cfi t _ _ _ _ valid_jmp.

Variable ki : (@refinement_common.kernel_invariant t ops sp cp e).

Variable stable : list (@Symbolic.syscall t sp).

(* This is basically the initial_refine assumption on preservation *)
Definition cinitial (cs : Concrete.state t) := 
  exists ss, Sym.initial stable ss /\ refine_state ki stable ss cs.

Variable masks : Concrete.Masks.

Definition in_user := @in_user t ops sp cp e.

Definition stopping (ss : list (Concrete.state t)) : Prop :=
  exists hd tl,
    ss = hd :: tl /\
    in_user hd /\
    forall s, In s tl -> in_kernel s.

Program Instance concrete_cfi_machine : cfi_machine := {|
  state := Concrete.state t;
  initial s := cinitial s;
  
  step s1 s2 := Concrete.step ops masks s1 s2;
  step_a := step_a;

  succ := csucc;
  stopping := stopping
 |}.

End ConcreteSection.

End Conc.
