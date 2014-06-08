(* Fault handler implementation *)

Require Import ZArith.
Require Import List.

Import ListNotations.

Require Import lib.utils lib.Coqlib.
Require Import concrete.common.
Require Import concrete.concrete.
Require Import kernel.rules.
Require Import kernel.refinement.

Section fault_handler.

Context (mt : machine_types)
        (ops : machine_ops mt)
        (cp : Concrete.concrete_params mt)
        (sp : Concrete.params_spec cp).

Let code := list (instr mt).

Class fault_handler_params := {
  rop : reg mt; (* Opcode register *)

  rtpc : reg mt; (* PC register *)

  rti : reg mt; rt1 : reg mt; rt2 : reg mt; rt3 : reg mt; (* Tag registers *)

  rb : reg mt; (* Boolean result register *)

  ri : reg mt; (* Auxiliary register for if statement *)

  rtrpc : reg mt; rtr : reg mt; (* Registers for tag results *)
  raddr : reg mt; (* Addressing register *)

  eq_code : reg mt -> reg mt -> reg mt -> code;
  load_const : word mt -> reg mt -> code
}.

Context (fhp : fault_handler_params).

Definition is_user s d :=
  [Const mt (tag_to_imm USER) rb] ++
  eq_code rb s d.

Definition is_call s d :=
  [Const mt (tag_to_imm CALL) rb] ++
  eq_code rb s d.

Definition mvec_regs := [rop; rtpc; rti; rt1; rt2; rt3].

Definition kernel_regs := mvec_regs ++ [rb; ri; rtrpc; rtr; raddr].

Definition bool_to_imm (b : bool) : imm mt :=
  if b then Z_to_imm 1 else Z_to_imm 0.

Definition stag_compile (st : stag) : reg mt :=
  match st with
  | TPC => rtpc
  | TINSTR => rti
  | T1 => rt1
  | T2 => rt2
  | T3 => rt3
  end.

(* Test for value in [r]. If true (i.e., not zero), execute [t]. Otherwise, execute [f]. *)
Definition if_ (r : reg mt) (t f : code) : code :=
  let lt := Z_to_imm (Z.of_nat (length t + 1)) in
  let eend := [Const mt (bool_to_imm true) ri] ++
              [Bnz mt ri lt] in
  let lf := Z_to_imm (Z.of_nat (length f + length eend + 1)) in
  [Bnz mt r lf] ++
  f ++
  eend ++
  t.

Fixpoint ptag_compile (pt : ptag) : code :=
  match pt with
  | ISUSER st => is_user (stag_compile st) rb
  | ISCALL st => is_call (stag_compile st) rb
  | TRUE => [Const mt (bool_to_imm true) rb]
  | FALSE => [Const mt (bool_to_imm false) rb]
  | AND pt1 pt2 => ptag_compile pt1 ++ if_ rb (ptag_compile pt2) []
  | OR pt1 pt2 => ptag_compile pt1 ++ if_ rb [] (ptag_compile pt2)
  end.

Definition inf_loop : code :=
  [Const mt (Z_to_imm 0) rb] ++
  [Bnz mt rb (Z_to_imm 0)].

Definition srule_compile (sr : srule) : code :=
  ptag_compile (allow sr) ++
  if_ rb
      ([Const mt (tag_to_imm USER) rtrpc] ++
       [Const mt (tag_to_imm (result sr)) rtr])
      [].

Definition load_mvec : code :=
  fst (fold_left (fun acc r =>
                    let '(c,addr) := acc in
                    (c ++
                     load_const addr raddr ++
                     [Load mt raddr r],
                     addr + Z_to_word 1))%word
                 mvec_regs
                 ([],Concrete.cache_line_addr (t := mt))).

Definition srules_compile (srs : srules) : code :=
  load_mvec ++
  fold_right (fun op c =>
                [Const mt (op_to_imm op) rb] ++
                eq_code rb rop rb ++
                if_ rb
                    (srule_compile (srs op))
                    c)
             []
             opcodes ++
  if_ rb
      (load_const (Concrete.Mtrpc ops) raddr ++
       [Store mt rtrpc raddr] ++
       load_const (Concrete.Mtr ops) raddr ++
       [Store mt rtr raddr] ++
       [AddRule _] ++
       [JumpEpc _])
      inf_loop.

Definition kernel_protection_fh := srules_compile (kernel_srules USER).

Section invariant.

Context {s : machine_ops_spec ops}.

Variable fhstart : word mt.

(* TODO: refactor this? *)

Hypothesis kernel_tag_correct :
  Concrete.TKernel = tag_to_word KERNEL.

Let invariant (mem : Concrete.memory _)
              (regs : Concrete.registers _)
              (cache : Concrete.rules (word mt)) : Prop :=
  (forall addr, In addr (Concrete.rvec_fields _) ->
                exists w, Concrete.get_mem mem addr = Some w@(tag_to_word KERNEL)) /\
  (forall addr instr,
     nth_error kernel_protection_fh addr = Some instr ->
     Concrete.get_mem mem (add_word fhstart (Z_to_word (Z.of_nat addr))) =
     Some (encode_instr instr)@(tag_to_word KERNEL)) /\
  (* FIXME:
     This really shouldn't be included here, since it doesn't mention the neither the
     memory nor the register bank. Try to put this somewhere else. *)
  (forall addr, addr < length kernel_protection_fh ->
                ~ In (add_word fhstart (Z_to_word (Z.of_nat addr)))
                     (Concrete.mvec_and_rvec_fields _)) /\
  (forall mvec rvec,
     Concrete.ctpc mvec = Concrete.TKernel ->
     Concrete.cache_lookup _ cache masks mvec = Some rvec ->
     Concrete.cache_lookup _ concrete_ground_rules masks mvec = Some rvec) /\
  (forall mvec rvec,
     Concrete.cache_lookup _ concrete_ground_rules masks mvec = Some rvec ->
     Concrete.cache_lookup _ cache masks mvec = Some rvec) /\
  (forall r, In r kernel_regs ->
             common.tag (Concrete.get_reg regs r) = tag_to_word KERNEL).

Lemma invariant_upd_mem :
  forall regs mem1 mem2 cache addr w1 w2
         (KINV : invariant mem1 regs cache)
         (GET : Concrete.get_mem mem1 addr = Some w1@(tag_to_word USER)) (* TODO: non-kernel memory *)
         (UPD : Concrete.upd_mem mem1 addr w2 = Some mem2),
    invariant mem2 regs cache.
Proof.
  intros. destruct KINV as (RVEC & PROG & MEM & GRULES1 & GRULES2 & REGS).
  split; [|split]; [ | | solve[eauto]].
  - intros addr' IN.
    destruct (eq_wordP addr' addr) as [|NEQ]; subst.
    + apply RVEC in IN. destruct IN as [w1' IN].
      rewrite IN in GET.
      assert (EQ : tag_to_word KERNEL = tag_to_word USER) by congruence.
      apply tag_to_word_inj in EQ. discriminate.
    + rewrite (PartMaps.get_upd_neq (Concrete.mem_axioms (t := mt)) _ _ NEQ UPD).
      now eauto.
  - intros addr' i GET'.
    destruct (eq_wordP (fhstart + Z_to_word (Z.of_nat addr'))%word addr) as [|NEQ]; subst.
    + erewrite (PartMaps.get_upd_eq (Concrete.mem_axioms (t := mt))); [|eauto].
      apply PROG in GET'.
      assert (EQ : tag_to_word KERNEL = tag_to_word USER) by congruence.
      apply tag_to_word_inj in EQ. discriminate.
    + rewrite (PartMaps.get_upd_neq (Concrete.mem_axioms (t := mt)) _ _ NEQ UPD).
      now eauto.
Qed.

Lemma invariant_upd_reg :
  forall mem regs cache r w1 w2
         (KINV : invariant mem regs cache)
         (GET : Concrete.get_reg regs r = w1@(tag_to_word USER)), (* TODO: non-kernel register *)
    invariant mem (Concrete.upd_reg regs r w2@(tag_to_word USER)) cache.
Proof.
  intros. destruct KINV as (RVEC & PROG & MEM & GRULES1 & GRULES2 & REGS).
  do 5 (split; eauto).
  intros r' IN.
  destruct (eq_regP r' r) as [|NEQ]; subst.
  - apply REGS in IN.
    rewrite GET in IN. simpl in IN.
    apply tag_to_word_inj in IN.
    discriminate.
  - erewrite (TotalMaps.get_upd_neq (Concrete.reg_axioms (t := mt))); eauto.
Qed.

Lemma invariant_store_mvec mem mem' mvec regs cache :
  forall (KINV : invariant mem regs cache)
         (MVEC : Concrete.store_mvec ops mem mvec = Some mem'),
    invariant mem' regs cache.
Proof.
  intros (RVEC & PROG & MEM & REGS).
  split; [|split; eauto].
  - intros addr IN.
    destruct (in_dec (fun x y => Bool.reflect_dec _ _ (eq_wordP x y))
                     addr (Concrete.mvec_fields ops)) as [IN' | NIN].
    + destruct (PartMaps.get_upd_list_in (Concrete.mem_axioms (t := mt)) mem _ addr MVEC IN')
        as (v' & IN'' & GET).
      rewrite GET. clear GET.
      simpl in IN''.
      rewrite <- kernel_tag_correct.
      repeat match goal with
      | H : _ \/ _ |- _ =>
        destruct H as [E | ?]; [inv E; eauto|]
      | H : False |- _ => inversion H
      end.
    + erewrite (PartMaps.get_upd_list_nin (Concrete.mem_axioms (t := mt))); eauto.
  - intros addr instr GET.
    erewrite (PartMaps.get_upd_list_nin (Concrete.mem_axioms (t := mt))); eauto.
    intros CONTRA.
    eapply MEM.
    + eapply nth_error_valid; eauto.
    + apply in_or_app. now eauto.
Qed.

Definition fault_handler_invariant : kernel_invariant := {|
  kernel_invariant_statement := invariant;
  kernel_invariant_upd_reg := invariant_upd_reg;
  kernel_invariant_upd_mem := invariant_upd_mem;
  kernel_invariant_store_mvec := invariant_store_mvec
|}.

End invariant.

End fault_handler.
