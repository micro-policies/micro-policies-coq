Require Import ZArith.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Require Import lib.Integers lib.utils lib.partial_maps lib.Coqlib common.common concrete.concrete.
Require Import List.

Import ListNotations.
Import Concrete. Import DoNotation.

Open Scope Z_scope.

Require Import concrete.exec.

Require Import concrete.int_32.

Require Import eval.

Section WithStuff.

Definition t := concrete_int_32_t.
Instance ops : machine_ops t := concrete_int_32_ops.


Definition kernel_code l := map encode_instr l.

(* Let's invent an environment containing a little program and see what we can prove about it. *)

Definition dontcare : word t := Word.zero.

Open Scope word_scope.

Definition r0 : reg t := 0.
Definition r1 : reg t := 1.
Definition r2 : reg t := 2.
Definition r3 : reg t := Word.repr 3. 

Definition max_code :=
map (fun i => (Atom (C t i) (C t TKernel)))
(map encode_instr
 [(* 0 *) Binop LEQ r2 r1 r3;
  (* 1 *) Bnz r3 (Word.repr 4); 
  (* 2 *) Mov r2 r3;
  (* 3 *) Const 1 r0;
  (* 4 *) Bnz r0 (Word.repr 2);
  (* 5 *) Mov r1 r3;
  (* 6 *) Nop _; 
  (* 7 *) Nop _; 
  (* 8 *) Nop _;
  (* 9 *) Nop _;
  (* 10 *) Nop _ ]).
 
(* From symbolic/int_32.v *)
Fixpoint insert_from {A : Type} (i : word t) (l : list A)
                     (mem : word_map t A) : word_map t A :=
  match l with
    | []      => mem
    | h :: l' => insert_from (Word.add i Word.one) l' (PartMaps.set mem i h)
  end.

(*
(* Environment only needs to describe data, not code.
   (If code is not already constant in the initial parametric environment,
    evaluation will fail anyway.)
*)
Definition env (a b: word t) (v:var t) : word t :=
  match v with
  | MP _ => dontcare 
  | MT _ => TKernel
  | RP w => if w == 1 then a else if w == 2 then b else dontcare
  | RT _ => TKernel
  end. 
*)


Let memory := word_map t (common.atom (pvalue t) (pvalue t)).

Definition set_one_mem (m:memory) (i: word t) : memory := 
  PartMaps.set m i (Atom (V t (MP t i)) (V t (MT t i))).

(* Pseudo-code:

Fixpoint initial_pmem_from (i:Z) (m:memory) : memory :=
   if zle i 0 then
     set_one_mem m 0 
   else
     initial_pmem_from (Z.pred i) (set_one_mem m (repr i))
.
*)

Definition initial_pmem_from (i : Z)  (m:memory) : memory :=
  fst (
  Z.iter i 
         (fun (rrec:memory*Z -> memory*Z) (mi:memory*Z) => 
            let (m,i) := mi in 
            let (m',i') := rrec (m,Z.pred i) in
            (set_one_mem m' (Word.repr i),i))
         (fun mi => (set_one_mem m 0,Z.zero))
         (m,i)).                                    
     
Definition max_mem_loc : Z := 10. 

Definition initial_pmem code := 
  insert_from Word.zero code (initial_pmem_from max_mem_loc PartMaps.empty).

Let regs := reg_map t (common.atom (pvalue t) (pvalue t)).

Definition set_one_reg (r:regs) (i: reg t) : regs := 
  PartMaps.set r i (Atom (V t (RP t i)) (V t (RT t i))).

(* Pseudo-code:

Fixpoint initial_pregs_from (i:Z) (r:regs) : regs :=
   if zle i 0 then
     set_one_reg r 0 
   else
     initial_pregs_from (Z.pred i) (set_one_reg r (repr i))
.
*)
Definition initial_pregs_from (i : Z)  (r:regs) : regs :=
  fst (
  Z.iter i 
         (fun (rrec:regs*Z -> regs*Z) (ri:regs*Z) => 
            let (r,i) := ri in 
            let (r',i') := rrec (r,Z.pred i) in
            (set_one_reg r' (Word.repr i),i))
         (fun ri => (set_one_reg r 0,Z.zero))
         (r,i)).                                    
     
Definition max_reg : Z := 10.

Definition initial_pregs := 
  initial_pregs_from max_reg PartMaps.empty.

(* Initial memory consists of code plus V mappings everywhere else. 
   Initial registers consists of V mappings everywhere. 
   Initial cache is an empty list.
   Initial ppc is (0,Kernel)
   Initial pepc is unimportant *)

Definition initial_tstate code := 
  St t (mkPState t (initial_pmem code)
                   initial_pregs
                   []
                   (Atom 0 TKernel)
                   (Atom (C t 0) (C t TKernel))(* irrelevant *)).

(* does something like this lemma already exist? *)
Lemma repr_signed2 : forall n b z, Word.signed b = z -> b = @Word.repr n z. 
Proof.
  intros. rewrite <- H. rewrite Word.repr_signed. reflexivity.
Qed.

(* FIRST APPROACH: Use abstract environment.*)

Definition arga : var t := RP t (r1).
Definition argb : var t := RP t (r2). 

Lemma max_behavior: forall env  masks,
                    exists ts', Some ts' = teval t masks 8 (initial_tstate max_code) /\ 
                    forall (T:forall w, env (RT t w) = TKernel),
                    PartMaps.get (Concrete.regs (concretize_tstate t env ts')) (Word.repr 3) = 
                    Some (Atom (Word.repr (Z.max (Word.signed (env arga)) (Word.signed (env argb)))) TKernel). 

Proof.
  intros. eexists.
  split.
  match goal with |- ?A = ?B => set z := B end. 
  vm_compute in z;  reflexivity.

  (* things become distessingly slow here...*)
  intro. unfold concretize_tstate, concretize_pvalue.

  destruct (binop_denote LEQ (env argb) (env arga) == 0) eqn: D; rewrite D;  
    rewrite PartMaps.map_correctness; 
    match goal with |- ?A = ?B => set z := A end; vm_compute in z; subst z;
    f_equal;
    f_equal; 
    auto;
    apply repr_signed2;
    unfold binop_denote, bool_to_word, Word.lt in D;
    destruct (zlt (Word.signed (env argb)) (Word.signed (env arga))).

    inv D.
    (* idiocy *)
    replace
     (RP t
         (Word.mkint (reg_field_size_minus_one t) 
                     2
                     (Word.Z_mod_modulus_range' 4 2)))
    with 
     argb by auto.
    zify; omega.

    (* idiocy *)
    replace
     (RP t
         (Word.mkint (reg_field_size_minus_one t) 
                     1
                     (Word.Z_mod_modulus_range' 4 1)))
    with 
     arga by auto.
    zify; omega. 

    (* Is there an easier way? *)
    have [eq|neq] := altP ((env argb) =P (env arga)). 
    {
     rewrite eq. 
     (* idiocy *)
     replace
      (RP t
         (Word.mkint (reg_field_size_minus_one t) 
                     1
                     (Word.Z_mod_modulus_range' 4 1)))
     with 
       arga by auto.
     zify; omega. 
    }

    {
      apply negb_true_iff in neq.
      rewrite neq in D.
      inv D.
    }
Qed.


(* ALTERNATIVE: Use concrete environment. *)

(* Environment only needs to describe data, not code.
   (If code is not already constant in the initial parametric environment,
    evaluation will fail anyway.)
*)
Definition env (a b: word t) (v:var t) : word t :=
  match v with
  | MP _ => dontcare 
  | MT _ => TKernel
  | RP w => if w == 1 then a else if w == 2 then b else dontcare
  | RT _ => TKernel
  end. 

Lemma max_behavior': forall (a b:word t) masks,
                    exists ts', Some ts' = teval t masks 8 (initial_tstate max_code) /\ 
                    PartMaps.get (Concrete.regs (concretize_tstate t (env a b) ts')) (Word.repr 3) = 
                    Some (Atom (Word.repr (Z.max (Word.signed a) (Word.signed b))) TKernel). 

Proof.
  intros. eexists.
  split.
  match goal with |- ?A = ?B => set z := B end. 
  vm_compute in z;  reflexivity.

  (* things become distessingly slow here...*)
  unfold concretize_tstate, concretize_pvalue, env.

  destruct ({| Word.intval := 1;
               Word.intrange := Word.Z_mod_modulus_range' 4 1 |} == 1) eqn:X;
  [(rewrite X; clear X) | inv X].
  destruct ({| Word.intval := 2;
               Word.intrange := Word.Z_mod_modulus_range' 4 2 |} == 1) eqn:X;
  [ inv X | (rewrite X; clear X)].
  destruct ({| Word.intval := 2;
               Word.intrange := Word.Z_mod_modulus_range' 4 2 |} == 2) eqn:X;
  [ (rewrite X;clear X) | inv X].
  destruct ({| Word.intval := 1;
            Word.intrange := Word.Z_mod_modulus_range' 31 1 |} == 0) eqn:X;
  [ inv X| (rewrite X;clear X)]. 


  destruct (binop_denote LEQ b a == 0) eqn: D; 
    rewrite PartMaps.map_correctness;
    match goal with |- ?A = ?B => set z := A end; vm_compute in z; subst z;
    f_equal;
    f_equal;
    apply repr_signed2;
    unfold binop_denote, bool_to_word, Word.lt in D; 
    destruct (zlt (Word.signed b) (Word.signed a)).

    inv D. 

    zify; omega.

    zify; omega. 

    (* Is there an easier way? *)
    have [eq|neq] := altP (b =P a). 
      subst. zify; omega. 

      apply negb_true_iff in neq.
      rewrite neq in D.
      inv D.
Qed.



End WithStuff.