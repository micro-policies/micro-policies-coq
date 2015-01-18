Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ord word partmap.

Require Import lib.utils lib.partmap_utils.
Require Import common.common.
Require Import concrete.concrete.
Require Import symbolic.symbolic.
Require Import cfi.symbolic.
Require Import cfi.property.
Require Import cfi.rules.
Require Import cfi.classes.
Require Import symbolic.rules.
Require Import symbolic.refinement_common.

Set Implicit Arguments.

Module Conc.
Section ConcreteSection.

Context {t : machine_types}
        {ops : machine_ops t}
        {ids : @classes.cfi_id t}
        {e : rules.fencodable t cfi_tags}.

Variable cfg : id -> id -> bool.

Definition valid_jmp := classes.valid_jmp cfg.

(*allow attacker to change only things tagged USER DATA! all the rest should be equiv*)


Definition no_violation (cst : Concrete.state t) :=
  let '(Concrete.mkState mem _  _ pc@tpc _) := cst in
  (forall i cti ti src,
    getm mem pc = Some i@cti ->
    @fdecode _ _ e Symbolic.M cti = Some (USER ti) ->
    @fdecode _ _ e Symbolic.P tpc = Some (USER (INSTR (Some src))) ->
    exists dst,
        ti = INSTR (Some dst) /\ cfg src dst) /\
  (forall i cti ti src,
     getm mem pc = Some i@cti ->
     @fdecode _ _ e Symbolic.M cti = Some (ENTRY ti) ->
     @fdecode _ _ e Symbolic.P tpc = Some (USER (INSTR (Some src))) ->
     exists dst,
       ti = INSTR (Some dst) /\ cfg src dst).

(*Defined in terms of atom_equiv for symbolic tags*)
(* TODO: as a sanity check, please prove reflexivity for this and
   the other attacker relations. That will ensure that the attacker
   can at least keep things the same. *)
Inductive atom_equiv k (a : atom (mword t) (mword t)) (a' : atom (mword t) (mword t)) : Prop :=
  | user_equiv : forall v v' ct ut ct' ut',
                   a = v@ct ->
                   @fdecode _ _ e k ct = Some (USER ut) ->
                   a' = v'@ct' ->
                   @fdecode _ _ e k ct' = Some (USER ut') ->
                   Sym.atom_equiv v@ut v'@ut' ->
                   atom_equiv k a a'
  | any_equiv : (~ exists ut, @fdecode _ _ e k (common.tag a) = Some (USER ut)) ->
                a = a' ->
                atom_equiv k a a'.

Definition equiv (mem mem' : Concrete.memory t) :=
  pointwise (atom_equiv Symbolic.M) mem mem'.

Definition reg_equiv (regs : Concrete.registers t) (regs' : Concrete.registers t) :=
  forall r, exists x x',
    getm regs r = Some x /\
    getm regs' r = Some x' /\
    atom_equiv Symbolic.R x x'.

Inductive step_a : Concrete.state t ->
                   Concrete.state t -> Prop :=
| step_attack : forall mem reg cache pc tpc epc mem' reg'
                  (INUSER: oapp (fun x => is_user x) false (@fdecode _ _ e Symbolic.P tpc))
                  (REQUIV: reg_equiv reg reg')
                  (MEQUIV: equiv mem mem'),
                  step_a (Concrete.mkState mem reg cache pc@tpc epc)
                         (Concrete.mkState mem' reg' cache pc@tpc epc).

Local Notation "x .+1" := (x + 1)%w.
Local Open Scope word_scope.

Definition csucc (st : Concrete.state t) (st' : Concrete.state t) : bool :=
  let pc_s := common.val (Concrete.pc st) in
  let pc_s' := common.val (Concrete.pc st') in
  if in_kernel st || in_kernel st' then true else
  match (getm (Concrete.mem st) pc_s) with
    | Some i =>
      match (@fdecode _ _ e Symbolic.M (common.tag i)) with
        | Some (USER (INSTR (Some src))) =>
          match decode_instr (common.val i) with
            | Some (Jump r)
            | Some (Jal r) =>
              match (getm (Concrete.mem st) pc_s') with
                | Some i' =>
                  match (@fdecode _ _ e Symbolic.M (common.tag i')) with
                    | Some (USER (INSTR (Some dst))) =>
                      cfg src dst
                    | Some (ENTRY (INSTR (Some dst))) =>
                      is_nop (common.val i') && cfg src dst
                    | _ => false
                  end
                | _ => false
              end
            | Some (Bnz r imm) =>
              (pc_s' == pc_s .+1) || (pc_s' == pc_s + swcast imm)
            | None => false
            | _ => pc_s' == pc_s .+1
          end
        | Some (USER (INSTR None)) =>
          match decode_instr (common.val i) with
            | Some (Jump r)
            | Some (Jal r) =>
              false
            | Some (Bnz r imm) =>
              (pc_s' == pc_s .+1) || (pc_s' == pc_s + swcast imm)
            | None => false
            | _ => pc_s' == pc_s .+1
          end
       (* this says that if cst,cst' is in user mode then it's
          not sensible to point to kernel memory*)
        | Some (USER DATA)
        | Some (ENTRY _)
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
  (all_attacker ss /\ all in_user ss)
  \/
  (exists user kernel,
    ss = user ++ kernel /\
    all_attacker user /\ all in_user user /\
    all in_kernel kernel).

Program Instance concrete_cfi_machine : cfi_machine := {|
  state := [eqType of Concrete.state t];
  initial s := cinitial s;

  step s1 s2 := Concrete.step ops masks s1 s2;
  step_a := step_a;

  succ := csucc;
  stopping := stopping
 |}.

End ConcreteSection.

End Conc.
