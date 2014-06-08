Require Import Coq.Lists.List Coq.Arith.Arith Coq.ZArith.ZArith.
Require Import Coq.Classes.SetoidDec.
Require Import lib.utils.
Require Import concrete.common.
Require Import cfi.cfi.
Set Implicit Arguments.

Import ListNotations.

Module Abstract.

Open Scope bool_scope.
Open Scope Z_scope.

Section WithClasses.

Context (t : machine_types).
Context {ops : machine_ops t}.
Context {opss : machine_ops_spec ops}.

Class abstract_params := {
  imemory : Type;
  dmemory : Type;
  registers : Type;

  get_imem : imemory -> word t -> option (word t);
  upd_imem : imemory -> word t -> word t -> option imemory;

  get_dmem : dmemory -> word t -> option (word t);
  upd_dmem : dmemory -> word t -> word t -> option dmemory;

  (* Contrary to concrete machine, here register access and update
     might fail, since they might correspond to kernel registers *)

  get_reg : registers -> reg t -> option (word t);
  upd_reg : registers -> reg t -> word t -> option registers

}.

Class params_spec (ap : abstract_params) := {

  imem_axioms :> PartMaps.axioms get_imem upd_imem;

  dmem_axioms :> PartMaps.axioms get_dmem upd_dmem;

  reg_axioms :> PartMaps.axioms get_reg upd_reg

}.

Context {ap : abstract_params}.

Local Coercion Z_to_word : Z >-> word.
Open Scope word_scope.

Local Notation word := (word t).
Local Notation "x .+1" := (add_word x (Z_to_word 1)) (at level 60).

Definition state := 
  (imemory * dmemory * registers * word (* pc *) * bool (*jump check*))%type.

Record syscall := Syscall {
  address : word;
  sem : state -> option state
}.

Variable table : list syscall.

Definition get_syscall (addr : word) : option syscall :=
  find (fun sc => address sc ==b addr) table.

Variable valid_jmp : word -> word -> bool.

Inductive step : state -> state -> Prop :=
| step_nop : forall imem dmem reg pc i,
             forall (FETCH : get_imem imem pc = Some i),
             forall (INST : decode_instr i = Some (Nop _)),
             step (imem,dmem,reg,pc,true) (imem,dmem,reg,pc.+1,true)
| step_const : forall imem dmem reg reg' pc i n r,
             forall (FETCH : get_imem imem pc = Some i),
             forall (INST : decode_instr i = Some (Const _ n r)),
             forall (UPD : upd_reg reg r (imm_to_word n) = Some reg'),
             step (imem,dmem,reg,pc,true) (imem,dmem,reg',pc.+1,true)
| step_mov : forall imem dmem reg reg' pc i r1 r2 w1,
             forall (FETCH : get_imem imem pc = Some i),
             forall (INST : decode_instr i = Some (Mov _ r1 r2)),
             forall (R1W : get_reg reg r1 = Some w1),
             forall (UPD : upd_reg reg r2 w1 = Some reg'),
             step (imem,dmem,reg,pc,true) (imem,dmem,reg',pc.+1,true)
| step_binop : forall imem dmem reg reg' pc i f r1 r2 r3 w1 w2,
             forall (FETCH : get_imem imem pc = Some i),
             forall (INST : decode_instr i = Some (Binop _ f r1 r2 r3)),
             forall (R1W : get_reg reg r1 = Some w1),
             forall (R2W : get_reg reg r2 = Some w2),
             forall (UPD : upd_reg reg r3 (binop_denote f w1 w2) = Some reg'),
             step (imem,dmem,reg,pc,true) (imem,dmem,reg',pc.+1,true)
| step_load : forall imem dmem reg reg' pc i r1 r2 w1 w2,
             forall (FETCH : get_imem imem pc = Some i),
             forall (INST : decode_instr i = Some (Load _ r1 r2)),
             forall (R1W : get_reg reg r1 = Some w1),
             forall (MEM1 : (*(get_imem imem w1 = None /\ 
                             get_dmem dmem w1 = Some w2) \/ 
                            (get_dmem dmem w1 = None /\ 
                             get_imem imem w1 = Some w2)*)
             (* disjointness of memories for abstract machine is guaranteed by the refinement
                since it's there by default for the concrete machine
                -> this will imply the determinism of this step *)
                    get_imem imem w1 = Some w2 \/ get_dmem dmem w1 = Some w2), 
             forall (UPD : upd_reg reg r2 w2 = Some reg'),
             step (imem,dmem,reg,pc,true) (imem,dmem,reg',pc.+1,true)
| step_store : forall imem dmem dmem' reg pc i r1 r2 w1 w2,
             forall (FETCH : get_imem imem pc = Some i),
             forall (INST : decode_instr i = Some (Store _ r1 r2)),
             forall (R1W : get_reg reg r1 = Some w1),
             forall (R2W : get_reg reg r2 = Some w2),
             forall (UPD : upd_dmem dmem w1 w2 = Some dmem'),
             step (imem,dmem,reg,pc,true) (imem,dmem',reg,pc.+1,true)
| step_jump : forall imem dmem reg pc i r w b,
             forall (FETCH : get_imem imem pc = Some i),
             forall (INST : decode_instr i = Some (Jump _ r)),
             forall (RW : get_reg reg r = Some w), 
             forall (VALID : valid_jmp pc w = b), 
             step (imem,dmem,reg,pc,true) (imem,dmem,reg,w,b)
| step_bnz : forall imem dmem reg pc i r n w,
             forall (FETCH : get_imem imem pc = Some i),
             forall (INST : decode_instr i = Some (Bnz _ r n)),
             forall (RW : get_reg reg r = Some w),
             let pc' := add_word pc (if w ==b Z_to_word 0 then Z_to_word 1 else imm_to_word n) in
             step (imem,dmem,reg,pc,true) (imem,dmem,reg,pc',true)
| step_jal : forall imem dmem reg reg' pc i r w b,
             forall (FETCH : get_imem imem pc = Some i),
             forall (INST : decode_instr i = Some (Jal _ r)),
             forall (RW : get_reg reg r = Some w),
             forall (GETCALL : get_syscall w = None),
             forall (UPD : upd_reg reg ra (pc.+1) = Some reg'),
             forall (VALID : valid_jmp pc w = b),
             step (imem,dmem,reg,pc,true) (imem,dmem,reg',w,b)
| step_syscall : forall imem dmem dmem' reg reg' pc i r w sc b,
                 forall (FETCH : get_imem imem pc = Some i),
                 forall (INST : decode_instr i = Some (Jal _ r)),
                 forall (RW : get_reg reg r = Some w),
                 forall (GETCALL : get_syscall w = Some sc),
                 forall (CALL : sem sc (imem,dmem,reg,pc,true) = Some (imem,dmem',reg',pc .+1,true)),
                 forall (VALID : valid_jmp pc w = b), 
                 step (imem,dmem,reg,pc,true) (imem,dmem',reg',pc .+1,b).

Hypothesis step_determ : forall s s' s'', step s s' -> step s s'' -> s' = s''.

Inductive step_a : state -> state -> Prop :=
| step_attack : forall imem dmem dmem' reg reg' pc,
             step_a (imem,dmem,reg,pc,true) (imem,dmem',reg',pc,true). 

Definition succ (st : state) (st' : state) : bool :=
  let '(imem,_,reg,pc,_) := st in
  let '(_,_,_,pc',_) := st' in
  match (get_imem imem pc) with
    | Some i => 
      (*XXX: Review this *)
      match decode_instr i with
        | Some (Jump r) => valid_jmp pc pc'
        | Some (Jal r) => match get_reg reg r with
                            | Some w => match get_syscall w with
                                          | Some sc => valid_jmp pc w
                                          | None => valid_jmp pc pc'
                                        end
                            | None => false
                          end
        | Some (Bnz r imm) => (pc' ==b pc .+1) || (pc' ==b pc + imm_to_word imm)
        | None => false
        | _ => pc' ==b pc .+1
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
  succ s s' = false.

Definition S (xs : list state) :=
  exists s, xs = [s] /\ ~ exists s', cfi_step abstract_cfi_machine s s'.

Theorem cfi' : cfi' abstract_cfi_machine V S.
Proof.
  unfold cfi'. intros. 
  apply interm_equiv_intermrev in INTERM.
  induction INTERM as [s s' STEP | s s' s'' xs STEP INTERM ].
  + destruct STEP as [STEPA | STEP].
    - left. intros si sj IN2.
      destruct IN2 as [[EQ1 EQ2] | CONTRA]; subst.
      { left. split; [assumption | apply attacker_pc in STEPA; assumption]. }
      { destruct CONTRA. }
    - inversion STEP; subst; simpl;      
      repeat (  match goal with 
          | [H: cfi.step (_,_,_,_,true) (_,_,_,_,true) |- trace_has_cfi _ _ \/ _] =>
            left; intros si sj IN2; destruct IN2 as [[EQ1 EQ2] | CONTRA]; subst
          | [ |- _ \/ cfi.succ (_,_,_,_,true) (_,_,_,_,true) = true ] =>
              right; simpl; rewrite FETCH, INST
          | [H: In2 _ _ [_] |- _ ] => destruct H
          | [H: true = valid_jmp _ _ |- valid_jmp _ _ = true] => symmetry; assumption 
          | [H: cfi.step (_,_,_,_,true) (_,_,_,_,valid_jmp ?pc ?w) |- trace_has_cfi _ _ \/ _] =>
            remember (valid_jmp pc w) as validjmp; destruct validjmp
          | [H: false = valid_jmp _ _ |- trace_has_cfi _ _ \/ _] => 
            right; eexists; eexists; exists []; exists [];
            split; [simpl; auto | idtac]
          | [ |- V _ _ /\ _ ] => split; [unfold V; simpl; rewrite FETCH, INST; auto | idtac]
          | [ |- trace_has_cfi _ _ /\ _] => split; [intros csi csj IN2; destruct IN2 | idtac]
          | [ |- S _ ] => unfold S; eexists; split; [eauto | idtac]
          | [ |- ~ _] => intro FALSE; inversion FALSE as [s''' FALSE2];
            inversion FALSE2 as [FSTEP | FSTEP]; inversion FSTEP
          | [H : get_reg _ _ = _, H1 : get_syscall _ = _ |- match _ with _ => _ end = _] =>
            rewrite H; rewrite H1; auto
          | [ |- (_ ==b _) = true ] =>  apply eqb_refl
          | [H : get_reg _ _ = _, H1 : get_syscall _ = _ |- match _ with _ => _ end = _] =>
            rewrite H; rewrite H1; auto
                                     
              end).     
    destruct (w ==b Z_to_word 0);
    unfold pc'; apply Bool.orb_true_iff; constructor (apply eqb_refl; apply eq_wordP). 
  + apply interm_equiv_intermrev in INTERM.
    destruct (IHINTERM INIT) as [TSAFE | [sv1 [sv2 [hs [tl VIOLATION]]]]].
    - destruct STEP as [STEPA | STEP].
      * left. intros si sj IN2. 
        induction xs using rev_ind.
        { simpl in IN2. destruct IN2. }
        { rewrite <- app_assoc in IN2.
          simpl in IN2. 
          destruct (in2_reverse si sj xs x s'' IN2) as [IN2' | [EQ1 EQ2]].
          - apply TSAFE; assumption.
          - subst. apply interm_last_step in INTERM; subst.
            left; split; [assumption | apply attacker_pc in STEPA; assumption].
        }
      * induction xs using rev_ind.
        inversion INTERM. 
        inversion STEP; subst; simpl; apply interm_last_step in INTERM; subst;
        repeat (  match goal with 
          | [H: cfi.step (_,_,_,_,true) (_,_,_,_,true) |- trace_has_cfi _ _ \/ _] =>
            left; intros si sj IN2; rewrite <- app_assoc in IN2; simpl in IN2; apply in2_reverse in IN2
          | [H: In2 _ _ _ |- _ ] => 
            rewrite <- app_assoc in H; simpl in H; apply in2_reverse in H
          | [H: In2 _ _ _ \/ _ |- _] => destruct H as [? | [? ?]]; [apply TSAFE; assumption | subst; right]
          | [ |- cfi.succ (_,_,_,_,true) (_,_,_,_,true) = _ ] =>
               simpl; rewrite FETCH, INST
          | [ |- (_ ==b _) = true] => apply eqb_refl; apply eq_wordP
          | [H: cfi.step (_,_,_,_,true) (_,_,_,_,valid_jmp ?pc ?w) |- trace_has_cfi _ _ \/ _] =>
            remember (valid_jmp pc w) as validjmp; destruct validjmp
          | [H: true = valid_jmp _ _ |- valid_jmp _ _ = true] => symmetry; assumption
          | [H: false = valid_jmp _ _, 
            H1: cfi.step (?Imem, ?Dmem, ?Reg, ?Pc, true) (?Imem', ?Dmem', ?Reg', ?Pc', false)
              |- trace_has_cfi _ _ \/ _] => 
            right; exists (Imem,Dmem,Reg,Pc,true); exists (Imem',Dmem',Reg',Pc',false); exists xs; exists [];
            split; [rewrite <- app_assoc; reflexivity | idtac]                                                              
          | [ |- V _ _ /\ _ ] => split; [unfold V; simpl; rewrite FETCH, INST; auto | idtac]
          | [ |- trace_has_cfi _ _ /\ _] => split
          | [H: trace_has_cfi _ ?Xs |- trace_has_cfi _ ?Xs] => assumption
          | [ |- trace_has_cfi _ [?S] ] => intros ? ? IN2; destruct IN2
          | [ |- S _ ] => unfold S; eexists; split; [eauto | idtac]
          | [ |- ~ _] => intro FALSE; inversion FALSE as [s''' FALSE2]; 
            inversion FALSE2 as [FSTEP | FSTEP]; inversion FSTEP
          | [H : get_reg _ _ = _, H1 : get_syscall _ = _ |- match _ with _ => _ end = _] =>
            rewrite H; rewrite H1; auto
                  end).
        destruct (w ==b Z_to_word 0);
        unfold pc'; apply Bool.orb_true_iff; constructor (apply eqb_refl; apply eq_wordP).
   - (*Case a violation occurs in the trace*)
     induction xs using rev_ind. inversion INTERM. subst. clear IHxs.
     destruct VIOLATION as [LST [VIO [T1 [T2 STOPS]]]].
     rewrite LST in INTERM. unfold S in STOPS.
     destruct STOPS as [sv2' [EQ IRRED]].
     destruct tl; [simpl; inversion EQ; subst | inversion EQ].
     change [sv1;sv2'] with ([sv1] ++ [sv2']) in INTERM.
     remember (hs ++ [sv1]) as hs'.
     rewrite app_assoc in INTERM.
     rewrite <- Heqhs' in INTERM.
     apply interm_last_step in INTERM; subst.
     assert (CONTRA: exists s'', cfi_step abstract_cfi_machine s' s'') by (eexists; eauto).
     destruct (IRRED CONTRA).
Qed.

  
    
  

End WithClasses.

End Abstract.

Arguments Abstract.state t {_}.
Arguments Abstract.imemory t {_}.
Arguments Abstract.dmemory t {_}.
Arguments Abstract.registers t {_}.
Arguments Abstract.syscall t {_}.
