(* Fault handler implementation *)

Require Import ZArith.
Require Import List.

Import ListNotations.

Require Import eqtype.

Require Import lib.utils lib.Coqlib lib.partial_maps.
Require Import common.common.
Require Import concrete.concrete.
Require Import symbolic.rules.
Require Import symbolic.refinement_common.
Require Import symbolic.symbolic.

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

  ri : reg mt; (* Auxiliary register *)

  rtrpc : reg mt; rtr : reg mt; (* Registers for tag results *)
  raddr : reg mt; (* Addressing register *)

  eq_code : reg mt -> reg mt -> reg mt -> code;
  load_const : word mt -> reg mt -> code;

  (* Try to find whether tag in first register has the form [USER t
     ic]. If so, puts 1 in second register, [t] in third register, and
     [ic] in fourth register. Otherwise, puts 0 in second register. *)
  extract_user_tag : reg mt -> reg mt -> reg mt -> reg mt -> code;

  (* The inverse operation. Take a tag [t] in first register and a
     boolean [ic] in the second register, and return the encoding of
     [USER t ic] in the third register. *)
  wrap_user_tag : reg mt -> reg mt -> reg mt -> code;

  (* Take as input an M-vector of user tags in the corresponding
     registers given above and runs the user-level fault-handler. If
     the operation is allowed, put a 1 in [rb], and the user-level
     result tags in [rtrpc] and [rtr]. *)
  user_handler : code;

  is_entry_tag : reg mt -> reg mt -> code

}.

Context (fhp : fault_handler_params).

Definition mvec_regs := [rop; rtpc; rti; rt1; rt2; rt3].

Definition kernel_regs := mvec_regs ++ [rb; ri; rtrpc; rtr; raddr].

Definition bool_to_imm (b : bool) : imm mt :=
  if b then Z_to_imm 1 else Z_to_imm 0.

(* Test value in [r]. If true (i.e., not zero), execute [t]. Otherwise, execute [f]. *)
Definition if_ (r : reg mt) (t f : code) : code :=
  let lt := Z_to_imm (Z.of_nat (length t + 1)) in
  let eend := [Const mt (bool_to_imm true) ri] ++
              [Bnz mt ri lt] in
  let lf := Z_to_imm (Z.of_nat (length f + length eend + 1)) in
  [Bnz mt r lf] ++
  f ++
  eend ++
  t.

Definition inf_loop : code :=
  [Const mt (Z_to_imm 0) rb] ++
  [Bnz mt rb (Z_to_imm 0)].

Definition load_mvec : code :=
  fst (fold_left (fun acc r =>
                    let '(c,addr) := acc in
                    (c ++
                     load_const addr raddr ++
                     [Load mt raddr r],
                     addr + Z_to_word 1))%w
                 mvec_regs
                 ([],Concrete.cache_line_addr ops)).

Definition analyze_operand_tags : code :=
  (* Check whether instruction is tagged USER *)
  extract_user_tag rti rb rti ri ++
  if_ rb
      (* We are in user mode, extract operand tags *)
      [] (* TODO *)
      (* We hit an invalid point; halt the machine *)
      inf_loop.

Definition handler : code :=
  load_mvec ++
  extract_user_tag rtpc rb rtpc ri ++
  if_ rb
      (* PC has USER tag *)
      (if_ ri
           (* We just performed a Jal. Check whether we're an entry point *)
           (is_entry_tag rti ri ++
            if_ ri
                (* We are in a system call. Put KERNEL tags and return *)
                (load_const Concrete.TKernel ri ++
                 load_const (Concrete.Mtrpc ops) raddr ++
                 [Store _ ri raddr] ++
                 load_const (Concrete.Mtr ops) raddr ++
                 [Store _ ri raddr])
                (* We are not in a system call. Proceed as normal. *)
                analyze_operand_tags)
           (* We have executed something else besides Jal. Proceed normally. *)
           analyze_operand_tags)
      (* PC is not tagged USER, halt execution *)
      inf_loop.

Section invariant.

Context {s : machine_ops_spec ops}.

Let invariant (mem : Concrete.memory _)
              (regs : Concrete.registers _)
              (cache : Concrete.rules (word mt)) : Prop :=
  (forall addr : word mt, In addr (Concrete.rvec_fields ops) ->
                          exists w : word mt, PartMaps.get mem addr = Some w@Concrete.TKernel) /\
  (forall addr instr,
     nth_error handler addr = Some instr ->
     PartMaps.get mem (add_word (Concrete.fault_handler_start ops) (Z_to_word (Z.of_nat addr))) =
     Some (encode_instr instr)@Concrete.TKernel) /\
  (* FIXME:
     This really shouldn't be included here, since it doesn't mention the neither the
     memory nor the register bank. Try to put this somewhere else. *)
  (forall addr, addr < length handler ->
                ~ In (add_word (Concrete.fault_handler_start ops) (Z_to_word (Z.of_nat addr)))
                     (Concrete.mvec_and_rvec_fields _)) /\
  (forall mvec rvec,
     Concrete.ctpc mvec = Concrete.TKernel ->
     Concrete.cache_lookup _ cache masks mvec = Some rvec ->
     Concrete.cache_lookup _ ground_rules masks mvec = Some rvec) /\
  (forall mvec rvec,
     Concrete.cache_lookup _ ground_rules masks mvec = Some rvec ->
     Concrete.cache_lookup _ cache masks mvec = Some rvec) /\
  (forall r, In r kernel_regs ->
             common.tag (TotalMaps.get regs r) = Concrete.TKernel).

(*
Lemma invariant_upd_mem :
  forall regs mem1 mem2 cache addr w1 ut b w2 int
         (KINV : invariant mem1 regs cache)
         (GET : PartMaps.get mem1 addr = Some w1@(tag_to_word USER)) (* TODO: non-kernel memory *)
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
*)
End invariant.

End fault_handler.
