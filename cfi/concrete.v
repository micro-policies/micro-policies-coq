Require Import Coq.Lists.List Coq.Arith.Arith Coq.ZArith.ZArith.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Require Import lib.utils lib.partial_maps.
Require Import common.common.
Require Import concrete.concrete.
Require Import symbolic.symbolic.
Require Import cfi.symbolic.
Require Import cfi.property.
Require Import cfi.rules.
Require Import cfi.classes.
Require Import symbolic.rules.
Require Import lib.Coqlib.
Require Import symbolic.refinement_common.

Set Implicit Arguments.
Open Scope Z_scope.

Module Conc.
Section ConcreteSection.

Context {t : machine_types}
        {ops : machine_ops t}
        {ids : @classes.cfi_id t}
        {e : @rules.encodable rules.cfi_tag_eqType t ops}.

Import PartMaps.
Context {word_map : Type -> Type}
        {sw : partial_map word_map (word t)}
        {smems : axioms sw}
        {reg_map : Type -> Type}
        {sr : partial_map reg_map (reg t)}.

Variable cfg : id -> id -> bool.

Definition valid_jmp := classes.valid_jmp cfg.

(*allow attacker to change only things tagged USER DATA! all the rest should be equiv*)


Definition no_violation (cst : Concrete.state t) :=
  let '(Concrete.mkState mem _  _ pc@tpc _) := cst in
  (forall i ti src,
    get mem pc = Some i@(encode (USER ti)) ->
    tpc = encode (USER (INSTR (Some src))) ->
    exists dst, 
        ti = INSTR (Some dst) /\ cfg src dst = true) /\
  (forall i ti src,
     get mem pc = Some i@(encode (ENTRY ti)) ->
     tpc = encode (USER (INSTR (Some src))) ->
     exists dst, 
       ti = INSTR (Some dst) /\ cfg src dst = true).

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

Definition equiv {M : Type -> Type} {Key : Type} 
           {M_class : partial_map M Key} :
           M (atom (word t) (word t))-> M (atom (word t) (word t))-> Prop :=
  pointwise atom_equiv.

Definition reg_equiv (regs : Concrete.registers t) (regs' : Concrete.registers t) :=
  forall r,
    atom_equiv (TotalMaps.get regs r) (TotalMaps.get regs' r).

Inductive step_a : Concrete.state t ->
                   Concrete.state t -> Prop :=
| step_attack : forall mem reg cache pc tpc epc mem' reg'
                  (INUSER: word_lift (fun x => is_user x) tpc)
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
      match (decode (common.tag i)) with
        | Some (USER (INSTR (Some src))) =>
          match decode_instr (common.val i) with
            | Some (Jump r)
            | Some (Jal r) => 
              match (get (Concrete.mem st) pc_s') with
                | Some i' =>
                  match (decode (common.tag i')) with
                    | Some (USER (INSTR (Some dst))) =>
                      cfg src dst
                    | _ => false
                  end
                | _ => false
              end
            | Some (Bnz r imm) => 
              (pc_s' == pc_s .+1) || (pc_s' == pc_s + imm_to_word imm)
            | None => false
            | _ => pc_s' == pc_s .+1
          end
        | Some (USER (INSTR None)) =>
          match decode_instr (common.val i) with
            | Some (Jump r)
            | Some (Jal r) =>
              false
            | Some (Bnz r imm) => 
              (pc_s' == pc_s .+1) || (pc_s' == pc_s + imm_to_word imm)
            | None => false
            | _ => pc_s' == pc_s .+1
          end
        | Some (USER DATA)
        | Some KERNEL             (* this says that if cst,cst' is in user mode then it's
                                  not sensible to point to kernel memory*)
        | Some (ENTRY _) => false
        | None => false
      end
    | None => false
  end.

Instance sp : Symbolic.params := Sym.sym_cfi cfg.

Variable ki : refinement_common.kernel_invariant.

Variable stable : list (Symbolic.syscall t).

(* This is basically the initial_refine assumption on preservation *)
Definition cinitial (cs : Concrete.state t) := 
  exists ss, Sym.initial stable ss /\ refine_state ki stable ss cs.

Variable masks : Concrete.Masks.

Import ListNotations.

Definition all_attacker (xs : list (Concrete.state t)) : Prop :=
  forall x1 x2, In2 x1 x2 xs -> step_a x1 x2 /\ ~ Concrete.step _ masks x1 x2. 

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

Definition stopping (ss : list (Concrete.state t)) : Prop :=
  (all_attacker ss /\ forallb in_user ss)
  \/
  (exists user kernel,
    ss = user ++ kernel /\
    all_attacker user /\ forallb in_user user /\ 
    forallb in_kernel kernel).

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
