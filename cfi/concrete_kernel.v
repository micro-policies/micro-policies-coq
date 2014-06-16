Require Import Bool Arith ZArith.
Require Import Coq.Classes.SetoidDec.

Require Import lib.utils.
Require Import common.common.
Require Import concrete.concrete.
Require Import cfi.fault_handler_spec.

Section chandler_def.

Context {t : machine_types}.
Context {op : machine_ops t}
        {sp : machine_ops_spec op}.

Import DoNotation.

Open Scope Z.

Definition tag_to_Z (tg : tag) : Z :=
  match tg with
    | KERNEL => 0
    | ENTRY => 1
    | USER DATA => 2
    | USER (INSTR NONE) => 3
    | USER (INSTR SYSCALL) => 4
    | USER (INSTR (NODE n)) => (Z.of_nat n) + 5
  end.

Definition tag_to_imm (tg : tag) : imm t :=
  Z_to_imm (tag_to_Z tg).


Definition Z_to_tag (z : Z) : option tag :=
  match z with
  | 0 => Some KERNEL
  | 1 => Some ENTRY
  | 2 => Some (USER DATA)
  | 3 => Some (USER (INSTR NONE))
  | 4 => Some (USER (INSTR SYSCALL))
  | other => if (other <? 0) then None else 
               Some (USER (INSTR (NODE (Z.to_nat (z-5)))))
  end.

Definition Z_to_tag' (z : Z) : tag :=
  if Z.eqb z 0 then KERNEL else
    if Z.eqb z 1 then ENTRY else
      if Z.eqb z 2 then USER DATA else
        if Z.eqb z 3 then USER (INSTR NONE) else
          if Z.eqb z 4 then USER (INSTR SYSCALL) else
        USER (INSTR (NODE (Z.to_nat (z-5)))).

Lemma tag_to_ZK : forall tg,
  Z_to_tag (tag_to_Z tg) = Some tg.
Proof.
  Admitted.

(*Lemma tag_to_ZK' : forall tg,
  Z_to_tag' (tag_to_Z tg) = tg.
Proof.
  destruct tg; try reflexivity.
  destruct c as [i|]; try reflexivity.
  simpl tag_to_Z. destruct i. unfold Z_to_tag'.
  remember (Z.of_nat i + 5 =? 0) as eq.
  rewrite Z.add_comm in Heqeq.
  destruct eq.
  + inversion Heqeq as [CONTRA]. destruct i; simpl in CONTRA; inversion CONTRA.
  + 
    remember (Z.of_nat i + 5 =? 1) as eq1.
    rewrite Z.add_comm in Heqeq1. destruct eq1.
    destruct i.
    { simpl in Heqeq1. inversion Heqeq1. }
    { assert (ONE : 1 = 1 + 0) by (rewrite Z.add_0_r; reflexivity).
      rewrite ONE in Heqeq1.
      assert (FIVE : 5 = 1 + 4) by reflexivity.
      rewrite FIVE in Heqeq1.
      rewrite <- Z.add_assoc in Heqeq1.
      symmetry in Heqeq1. rewrite Z.eqb_eq in Heqeq1.
      rewrite Z.add_cancel_l in Heqeq1.
      inversion Heqeq1. }
    remember (Z.of_nat i + 5 =? 2) as eq2.
    rewrite Z.add_comm in Heqeq2. destruct eq2.
    destruct i.
    { simpl in Heqeq2. inversion Heqeq2. }
    { assert (TWO : 2 = 2 + 0) by (rewrite Z.add_0_r; reflexivity).
      rewrite TWO in Heqeq2.
      assert (FIVE : 5 = 2 + 3) by reflexivity.
      rewrite FIVE in Heqeq2.
      rewrite <- Z.add_assoc in Heqeq2.
      symmetry in Heqeq2. rewrite Z.eqb_eq in Heqeq2.
      rewrite Z.add_cancel_l in Heqeq2.
      inversion Heqeq2. }
    remember (Z.of_nat i + 5 =? 3) as eq3.
    rewrite Z.add_comm in Heqeq3. destruct eq3.
    destruct i.
    { simpl in Heqeq3. inversion Heqeq3. }
    { assert (THREE : 3 = 3 + 0) by (rewrite Z.add_0_r; reflexivity).
           rewrite THREE in Heqeq3.
           assert (FIVE : 5 = 3 + 2) by reflexivity.
           rewrite FIVE in Heqeq3.
           rewrite <- Z.add_assoc in Heqeq3.
           symmetry in Heqeq3. rewrite Z.eqb_eq in Heqeq3.
           rewrite Z.add_cancel_l in Heqeq3.
           inversion Heqeq3.
    }
    remember (Z.of_nat i + 5 =? 4) as eq4.
    rewrite Z.add_comm in Heqeq4. destruct eq4.
    destruct i.
    { simpl in Heqeq4. inversion Heqeq4. }
    { assert (FOUR : 4 = 4 + 0) by (rewrite Z.add_0_r; reflexivity).
           rewrite FOUR in Heqeq4.
           assert (FIVE : 5 = 4 + 1) by reflexivity.
           rewrite FIVE in Heqeq4.
           rewrite <- Z.add_assoc in Heqeq4.
           symmetry in Heqeq4. rewrite Z.eqb_eq in Heqeq4.
           rewrite Z.add_cancel_l in Heqeq4.
           inversion Heqeq4.
    }
    assert (EQ: (Z.of_nat i + 5 - 5) = Z.of_nat i) by omega.
    rewrite EQ.
    rewrite Nat2Z.id; reflexivity.
  + reflexivity.
  + reflexivity.
Qed.*)

        
Definition tag_to_word (tg : tag) : word t :=
  Z_to_word (tag_to_Z tg).

Definition word_to_tag (w : word t) : option tag :=
  Z_to_tag (word_to_Z w).

Lemma tag_to_word_to_tag : forall tg,
  word_to_tag (tag_to_word tg) = Some tg.
Proof.
  Admitted.

Lemma tag_to_word_inj tg1 tg2 :
  tag_to_word tg1 = tag_to_word tg2 -> tg1 = tg2.
Proof.
  Admitted.

Lemma tag_to_word_eq t1 t2 :
  (tag_to_word t1 ==b tag_to_word t2)%word =
  tag_eq t1 t2.
Proof. Admitted.

Lemma word_to_tag_to_word : forall w tg,
  forall (H : word_to_tag w = Some tg),
  tag_to_word tg = w.
Proof.
  Admitted.

Definition cmvec_to_mvec (cmvec : Concrete.MVec (word t)) : option MVec :=
  match cmvec with
  | Concrete.mkMVec cop ctpc cti ct1 ct2 ct3 =>
    do op  <- word_to_op  cop;
    do tpc <- word_to_tag ctpc;
    do ti  <- word_to_tag cti;
    do t1  <- word_to_tag ct1;
    do t2  <- word_to_tag ct2;
    do t3  <- word_to_tag ct3;
    Some (mkMVec op tpc ti t1 t2 t3)
  end.

Definition rvec_to_crvec (rvec : RVec) : Concrete.RVec (word t):=
  match rvec with
  | mkRVec trpc tr => Concrete.mkRVec (tag_to_word trpc) (tag_to_word tr)
  end.

Variable cfg : cfg_type.

Definition chandler cmvec :=
  do mvec <- cmvec_to_mvec cmvec;
  do rvec <- handler cfg kernel_srules mvec;
  Some (rvec_to_crvec rvec).
(*
Definition compile_rule (r : rule) : Concrete.rule (word t) :=
  let '(mvec, rvec) := r in
  ({|
      Concrete.cop := op_to_word (fault_handler_spec.op mvec);
      Concrete.ctpc := tag_to_word (tpc mvec);
      Concrete.cti := tag_to_word (ti mvec);
      Concrete.ct1 := tag_to_word (t1 mvec);
      Concrete.ct2 := tag_to_word (t2 mvec);
      Concrete.ct3 := tag_to_word (t3 mvec)
   |},
   {|
     Concrete.ctrpc := tag_to_word (trpc rvec);
     Concrete.ctr := tag_to_word (tr rvec)
   |}).

Definition compile_rules := List.map compile_rule.

Definition concrete_ground_rules := compile_rules (ground_rules USER).*)

End chandler_def.
