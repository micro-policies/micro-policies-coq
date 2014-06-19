Require Import Coq.Lists.List Coq.Arith.Arith Coq.ZArith.ZArith.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Require Import lib.utils lib.partial_maps.
Require Import common.common.
Require Import lib.Coqlib.
Require Import cfi.cfi.
Set Implicit Arguments.

Import ListNotations.

Module Abstract.

Open Scope bool_scope.
Open Scope Z_scope.

Section WithClasses.

Import PartMaps.

Context (t : machine_types).
Context {ops : machine_ops t}.
Context {opss : machine_ops_spec ops}.

Class abstract_params := {
  imemory : Type;
  imem_class :> partial_map imemory (word t) (word t);

  dmemory : Type;
  dmem_class :> partial_map dmemory (word t) (word t);

  registers : Type;
  reg_class :> partial_map registers (reg t) (word t)
}.

Class params_spec (ap : abstract_params) := {

  imem_axioms :> PartMaps.axioms (@imem_class ap);

  dmem_axioms :> PartMaps.axioms (@dmem_class ap);

  reg_axioms :> PartMaps.axioms (@reg_class ap)

}.

Context {ap : abstract_params}.

Open Scope word_scope.

Local Notation word := (word t).
Local Notation "x .+1" := (add_word x (Z_to_word 1)).

Definition state := 
  (imemory * dmemory * registers * word (* pc *) * bool (*jump check*))%type.

Record syscall := Syscall {
  address : word;
  sem : state -> option state
}.

Variable table : list syscall.

Definition get_syscall (addr : word) : option syscall :=
  List.find (fun sc => address sc == addr) table.

Variable valid_jmp : word -> word -> bool.

Inductive step : state -> state -> Prop :=
| step_nop : forall imem dmem reg pc i,
             forall (FETCH : get imem pc = Some i),
             forall (INST : decode_instr i = Some (Nop _)),
             step (imem,dmem,reg,pc,true) (imem,dmem,reg,pc.+1,true)
| step_const : forall imem dmem reg reg' pc i n r,
             forall (FETCH : get imem pc = Some i),
             forall (INST : decode_instr i = Some (Const _ n r)),
             forall (UPD : upd reg r (imm_to_word n) = Some reg'),
             step (imem,dmem,reg,pc,true) (imem,dmem,reg',pc.+1,true)
| step_mov : forall imem dmem reg reg' pc i r1 r2 w1,
             forall (FETCH : get imem pc = Some i),
             forall (INST : decode_instr i = Some (Mov _ r1 r2)),
             forall (R1W : get reg r1 = Some w1),
             forall (UPD : upd reg r2 w1 = Some reg'),
             step (imem,dmem,reg,pc,true) (imem,dmem,reg',pc.+1,true)
| step_binop : forall imem dmem reg reg' pc i f r1 r2 r3 w1 w2,
             forall (FETCH : get imem pc = Some i),
             forall (INST : decode_instr i = Some (Binop _ f r1 r2 r3)),
             forall (R1W : get reg r1 = Some w1),
             forall (R2W : get reg r2 = Some w2),
             forall (UPD : upd reg r3 (binop_denote f w1 w2) = Some reg'),
             step (imem,dmem,reg,pc,true) (imem,dmem,reg',pc.+1,true)
| step_load : forall imem dmem reg reg' pc i r1 r2 w1 w2,
             forall (FETCH : get imem pc = Some i),
             forall (INST : decode_instr i = Some (Load _ r1 r2)),
             forall (R1W : get reg r1 = Some w1),
             forall (MEM1 : get imem w1 = Some w2 \/ get dmem w1 = Some w2), 
             forall (UPD : upd reg r2 w2 = Some reg'),
             step (imem,dmem,reg,pc,true) (imem,dmem,reg',pc.+1,true)
| step_store : forall imem dmem dmem' reg pc i r1 r2 w1 w2,
             forall (FETCH : get imem pc = Some i),
             forall (INST : decode_instr i = Some (Store _ r1 r2)),
             forall (R1W : get reg r1 = Some w1),
             forall (R2W : get reg r2 = Some w2),
             forall (UPD : upd dmem w1 w2 = Some dmem'),
             step (imem,dmem,reg,pc,true) (imem,dmem',reg,pc.+1,true)
| step_jump : forall imem dmem reg pc i r w b,
             forall (FETCH : get imem pc = Some i),
             forall (INST : decode_instr i = Some (Jump _ r)),
             forall (RW : get reg r = Some w), 
             forall (VALID : valid_jmp pc w = b), 
             step (imem,dmem,reg,pc,true) (imem,dmem,reg,w,b)
| step_bnz : forall imem dmem reg pc i r n w,
             forall (FETCH : get imem pc = Some i),
             forall (INST : decode_instr i = Some (Bnz _ r n)),
             forall (RW : get reg r = Some w),
             let pc' := add_word pc (if w == Z_to_word 0 then Z_to_word 1 
                                     else imm_to_word n) in
             step (imem,dmem,reg,pc,true) (imem,dmem,reg,pc',true)
| step_jal : forall imem dmem reg reg' pc i r w b,
             forall (FETCH : get imem pc = Some i),
             forall (INST : decode_instr i = Some (Jal _ r)),
             forall (RW : get reg r = Some w),
             forall (GETCALL : get_syscall w = None),
             forall (UPD : upd reg ra (pc.+1) = Some reg'),
             forall (VALID : valid_jmp pc w = b),
             step (imem,dmem,reg,pc,true) (imem,dmem,reg',w,b)
| step_syscall : forall imem dmem dmem' reg reg' pc i r w sc b,
                 forall (FETCH : get imem pc = Some i),
                 forall (INST : decode_instr i = Some (Jal _ r)),
                 forall (RW : get reg r = Some w),
                 forall (GETCALL : get_syscall w = Some sc),
                 forall (CALL : sem sc (imem,dmem,reg,pc,true) = 
                                Some (imem,dmem',reg',pc .+1,true)),
                 forall (VALID : valid_jmp pc w = b), 
                 step (imem,dmem,reg,pc,true) (imem,dmem',reg',pc .+1,b).

(*unused so far*)
Hypothesis step_determ : forall s s' s'', step s s' -> step s s'' -> s' = s''.

Inductive step_a : state -> state -> Prop :=
| step_attack : forall imem dmem dmem' reg reg' pc i
             (FETCH: get imem pc = Some i)
             (MSAME: same_domain dmem dmem')
             (RSAME: same_domain reg reg'),
             step_a (imem,dmem,reg,pc,true) (imem,dmem',reg',pc,true). 

Definition succ (st : state) (st' : state) : bool :=
  let '(imem,_,reg,pc,_) := st in
  let '(_,_,_,pc',_) := st' in
  match (get imem pc) with
    | Some i => 
      (*XXX: Review this *)
      match decode_instr i with
        | Some (Jump r) => valid_jmp pc pc'
        | Some (Jal r) => match get reg r with
                            | Some w => match get_syscall w with
                                          | Some sc => valid_jmp pc w
                                          | None => valid_jmp pc pc'
                                        end
                            | None => false
                          end
        | Some (Bnz r imm) => (pc' == pc .+1) || (pc' == pc + imm_to_word imm)
        | None => false
        | _ => pc' == pc .+1
      end
    | None => false
  end.

Definition initial (s : state) := True.

Program Instance abstract_cfi_machine : cfi_machine t := {|
  state := state;
  initial s := initial s;
  
  step := step;
  step_a := step_a;

  get_pc s := let '(_,_,_,pc,_) := s in pc;
  
  succ := succ      
 |}.
Next Obligation.
Admitted.
Next Obligation.
  inversion H; subst. reflexivity. 
Qed.

Definition V (s : state) s' := 
  (*step s s' /\*) succ s s' = false.

Definition S (xs : list state) :=
  exists s, xs = [s] /\ ~ exists s', step s s'.

Ltac match_inv :=
  repeat match goal with
  | H : bind (fun x : _ => _) _ = Some _ |- _ =>
    apply bind_inv in H;
    let x := fresh x in
    let E := fresh "E" in
    destruct H as (x & H & E);
    simpl in H; simpl in E
  | H : (if ?b then _ else _) = Some _ |- _ =>
    let E := fresh "E" in
    destruct b eqn:E;
    try discriminate
  | H : match ?E with _ => _ end = _ |- _ =>
    destruct E eqn:?; try discriminate
  | H : Some _ = Some _ |- _ => inv H
  | H : ?O = Some _ |- context[bind _ ?O] => rewrite H; simpl
  | H : True |- _ => clear H
  end.

Lemma step_succ_violation ast ast' :
   succ ast ast' = false ->
   step ast ast' ->
   let '(_,_,_,_,b) := ast' in
   b = false.
Proof.
  intros SUCC STEP.
  inversion STEP; subst; simpl in SUCC; rewrite FETCH INST in SUCC;
  try (rewrite eqxx in SUCC; congruence); 
  try (destruct (w == 0)); try (rewrite eqxx ?orbT in SUCC); 
  try (rewrite RW GETCALL in SUCC); auto.
Qed.

Lemma step_a_violation ast ast' :
   step_a ast ast' ->
   let '(_,_,_,_,b) := ast' in
   b = true.
Proof.
  intros STEP.
  inversion STEP; subst. reflexivity. 
Qed.  


End WithClasses.

End Abstract.

Arguments Abstract.state t {_}.
Arguments Abstract.imemory t {_}.
Arguments Abstract.dmemory t {_}.
Arguments Abstract.registers t {_}.
Arguments Abstract.syscall t {_}.
