(* Fault handler implementation for concrete realization of symbolic machine *)

Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype.
Require Import tuple ssrint.
Require Import word partmap.

Require Import lib.utils.
Require Import common.types.
Require Import concrete.concrete.
Require Import symbolic.rules.
Require Import symbolic.refinement_common.
Require Import symbolic.symbolic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section fault_handler.

Context (mt : machine_types)
        (ops : machine_ops mt).

Let code := seq (instr mt).

Class fault_handler_params := {
  rop : reg mt; (* Opcode register *)

  rtpc : reg mt; (* PC register *)

  rti : reg mt; rt1 : reg mt; rt2 : reg mt; rt3 : reg mt; (* Tag registers *)

  rb : reg mt; (* Boolean result register *)

  ri1 : reg mt; ri2 : reg mt; ri3 : reg mt; ri4 : reg mt; ri5 : reg mt; (* Auxiliary registers *)

  rtrpc : reg mt; rtr : reg mt; (* Registers for tag results *)
  raddr : reg mt; (* Addressing register *)

  load_const : mword mt -> reg mt -> code
}.

Context (fhp : fault_handler_params).

(* Encoding:

   USER ut  -> | ut   | 0 | 1 |
   KERNEL   -> | 0..0 | 0 | 0 |
   ENTRY ut -> | ut   | 1 | 0 |

   (where "ENTRY ut" means that the entry point carries a specific
   tag, which might be used by the transfer function) *)

Definition mvec_regs := [:: rop; rtpc; rti; rt1; rt2; rt3].

Definition kernel_regs := mvec_regs ++ [:: rb; ri1; ri2; ri3; ri4; ri5; rtrpc; rtr; raddr].

(* For debugging -- put a telltale marker in the code *)
Definition got_here : code := [:: Const (as_word 999) ri5; Const 0%w ri5].

(* Test value in [r]. If true (i.e., not zero), execute [t]. Otherwise,
   execute [f]. Warning: overwrites ri1. *)
Definition if_ (r : reg mt) (t f : code) : code :=
  let lt := as_word (length t + 1) in
  let eend := [:: Const (as_word true) ri1] ++
              [:: Bnz ri1 lt] in
  let lf := as_word (length f + length eend + 1) in
  [:: Bnz r lf] ++
  f ++
  eend ++
  t.

(* Try to find whether tag in first register has the form [USER t]. If
   so, puts 1 in second register and [t] in third register. Otherwise,
   puts 0 in second register.  Warning: overwrites ri2.*)

Definition extract_user_tag (rsrc rsucc rut : reg mt) : code :=
  [:: Const 1%w ri2] ++
  [:: Binop AND rsrc ri2 rsucc] ++
  if_ rsucc
      ([:: Const (as_word 2) ri2] ++
       [:: Binop SHRU rsrc ri2 rut])
      [::].

(* The inverse operation. Take a tag [t] in first register and return
   the encoding of [USER t] in the second register. Warning:
   overwrites ri2. *)
Definition wrap_user_tag (rut rdst : reg mt) : code :=
  [:: Const (as_word 2) ri2] ++
  [:: Binop SHL rut ri2 ri2] ++
  [:: Const 1%w rdst] ++
  [:: Binop OR rdst ri2 rdst].

(* Similar to [extract_user_tag], but for kernel entry-point tags. *)
Definition extract_entry_tag (rsrc rsucc rut : reg mt) : code :=
  [:: Const (as_word 3) ri2] ++
  [:: Binop AND rsrc ri2 rsucc] ++
  [:: Const (as_word 2) ri2] ++
  [:: Binop EQ rsucc ri2 rsucc] ++
  if_ rsucc
      ([:: Const (as_word 2) ri2] ++
       [:: Binop SHRU rsrc ri2 rut])
      [::].

Definition load_mvec : code :=
  fst (foldl (fun acc r =>
                    let '(c,addr) := acc in
                    (c ++
                     load_const addr raddr ++
                     [:: Load raddr r],
                     addr + 1))%w
                 ([::],Concrete.cache_line_addr _) mvec_regs).

(* Take as input an mvector of high-level tags (in the appropriate
   registers, as set above), and computes the policy handler on
   those tags. If the operation is allowed, returns the rvector in
   the appropriate registers. Otherwise, enters an infinite loop. *)
Variable policy_handler : code.

(* Check whether the operands for a particular opcode are tagged
   USER. If so, extract the corresponding policy-level tags and call
   the higher-level handler on them. Otherwise, halt. Warning: overwrites
   ri3. *)
Definition analyze_operand_tags_for_opcode (op : opcode) : code :=
  (* Check that [rop] contains a USER tag *)
  let do_op rop := extract_user_tag rop rb rop ++
                   if_ rb [::] [:: Halt _] in
  if Symbolic.privileged_op op then [:: Halt _] else
  match length (Symbolic.inputs op) with
  | 0 => [::]
  | 1 => do_op rt1
  | 2 => do_op rt1 ++ do_op rt2
  | 3 => do_op rt1 ++ do_op rt2 ++ do_op rt3
  | _ => [:: Halt _]
  end.

(* The entire code for the generic fault handler.
   Warning: overwrites ri4. *)
Definition handler : code :=
  load_mvec ++
  extract_user_tag rtpc rb rtpc ++
  if_ rb
      (* PC has USER tag *)
      (* Check whether we're at an entry point *)
      (extract_entry_tag rti ri4 rti ++
       if_ ri4
           (* THEN: We are entering a system call routine.
                    Change opcode to SERVICE and invoke policy
                    fault handler. If call is allowed, put KERNEL
                    tags in rvector. NB: system calls are now
                    required to begin with a Nop to simplify the
                    specification of the fault handler. *)
           ([:: Const (word_of_op NOP) ri4] ++
            [:: Binop EQ ri4 rop ri4] ++
            if_ ri4 [::] [:: Halt _] ++
            [:: Const (as_word (pickle SERVICE)) rop] ++
            policy_handler ++
            load_const Concrete.TKernel rtrpc ++
            load_const Concrete.TKernel rtr)
           (* ELSE: We are not in a system call. *)
           (extract_user_tag rti rb rti ++
            if_ rb
                (* THEN: We are in user mode: extract operand tags
                   and run policy handler *)
                (foldr (fun op c =>
                               load_const (word_of_op op) ri4 ++
                               [:: Binop EQ rop ri4 rb] ++
                               if_ rb
                                  (analyze_operand_tags_for_opcode op)
                                  c)
                            [::] (enum opcode) ++
                 policy_handler ++
                 (* Wrap rvec *)
                 wrap_user_tag rtrpc rtrpc ++
                 wrap_user_tag rtr rtr)
                (* ELSE: The instruction is not tagged USER: halt the machine *)
                [:: Halt _]))
      (* PC is not tagged USER, halt execution *)
      [:: Halt _] ++
  (* Store rvector registers in memory, install rule in cache, and
     return from trap *)
  load_const (Concrete.Mtrpc mt) raddr ++
  [:: Store raddr rtrpc] ++
  load_const (Concrete.Mtr mt) raddr ++
  [:: Store raddr rtr] ++
  [:: AddRule _] ++
  [:: JumpEpc _].

Section invariant.

Context {s : machine_ops_spec ops}
        {sp : Symbolic.params}
        {e : encodable mt Symbolic.ttypes}.

Record policy_invariant : Type := {
  policy_invariant_statement :> Concrete.memory mt -> Symbolic.internal_state -> Prop;

  policy_invariant_upd_mem :
    forall mem mem' addr w1 ct ut w2 int
           (PINV : policy_invariant_statement mem int)
           (GET : mem addr = Some w1@ct)
           (DEC : decode Symbolic.M mem ct = Some (USER ut))
           (UPD : updm mem addr w2 = Some mem'),
      policy_invariant_statement mem' int;

  policy_invariant_store_mvec :
    forall mem mem' mvec int
           (KINV : policy_invariant_statement mem int)
           (MVEC : Concrete.store_mvec mem mvec = mem'),
    policy_invariant_statement mem' int

}.

Variable pinv : policy_invariant.

Let invariant (mem : Concrete.memory mt)
              (regs : Concrete.registers mt)
              (cache : Concrete.rules mt)
              (int : Symbolic.internal_state) : Prop :=
  (forall addr : mword mt, addr \in Concrete.rvec_fields _ ->
                          exists w : mword mt, mem addr = Some w@Concrete.TKernel) /\
  (forall (addr : 'I_(size handler)) instr,
     tnth (in_tuple handler) addr = instr ->
     mem (Concrete.fault_handler_start mt + as_word addr)%w =
     Some (encode_instr instr)@Concrete.TKernel) /\
  (* FIXME:
     This really shouldn't be included here, since it doesn't mention
     either the memory or the register bank. Try to put this somewhere else. *)
  (forall addr, addr < length handler ->
                Concrete.fault_handler_start mt + as_word addr \notin
                Concrete.mvec_and_rvec_fields _)%w /\
  (forall mvec rvec,
     Concrete.ctpc mvec = Concrete.TKernel ->
     Concrete.cache_lookup cache masks mvec = Some rvec ->
     Concrete.cache_lookup (ground_rules mt) masks mvec = Some rvec) /\
  (forall mvec rvec,
     Concrete.cache_lookup (ground_rules mt) masks mvec = Some rvec ->
     Concrete.cache_lookup cache masks mvec = Some rvec) /\
  (forall r, r \in kernel_regs ->
   exists x, regs r = Some x@Concrete.TKernel) /\
  pinv mem int.

Lemma invariant_upd_mem :
  forall regs mem1 mem2 cache addr w1 ct ut w2 int
         (KINV : invariant mem1 regs cache int)
         (GET : mem1 addr = Some w1@ct)
         (DEC : decode Symbolic.M mem1 ct = Some (USER ut))
         (UPD : updm mem1 addr w2 = Some mem2),
    invariant mem2 regs cache int.
Proof.
  intros. destruct KINV as (RVEC & PROG & MEM & GRULES1 & GRULES2 & REGS & INT).
  repeat split; eauto.
  - intros addr' IN.
    move: UPD; rewrite /updm GET /= => - [<-]; rewrite getm_set.
    move: IN; have [-> {addr'}|_] := altP (_ =P _) => IN; last by eauto.
    apply RVEC in IN. destruct IN as [w1' IN].
    assert (EQ : Concrete.TKernel = ct) by congruence. subst ct.
    by rewrite decode_kernel_tag in DEC.
  - intros addr' i GET'.
    move: UPD; rewrite /updm GET /= => - [<-] {mem2}; rewrite getm_set.
    have [Heq|Hne] := altP (_ =P _).
    + rewrite -{}Heq {addr} in GET.
      specialize (@PROG _ _ GET').
      rewrite PROG in GET.
      move: GET => [_ CONTRA]. subst ct.
      by rewrite decode_kernel_tag in DEC.
    + by eauto.
  - by eapply policy_invariant_upd_mem; eauto.
Qed.

Lemma invariant_upd_reg :
  forall mem regs regs' cache r w1 ct1 ut1 w2 ct2 ut2 int
         (KINV : invariant mem regs cache int)
         (GET : regs r = Some w1@ct1)
         (DEC : decode Symbolic.R mem ct1 = Some (USER ut1))
         (UPD : updm regs r w2@ct2 = Some regs')
         (DEC' : decode Symbolic.R mem ct2 = Some (USER ut2)),
    invariant mem regs' cache int.
Proof.
  intros. destruct KINV as (RVEC & PROG & MEM & GRULES1 & GRULES2 & REGS & INT).
  do 6 (split; eauto).
  move=> r' IN; move: UPD; rewrite /updm GET /= => - [<-] {regs'}.
  rewrite getm_set.
  have [Heq|Hneq] := altP (_ =P _).
  - rewrite {}Heq {r'} in IN.
    move: IN => /REGS [x GET'].
    have ? : ct1 = Concrete.TKernel by congruence. subst ct1.
    by rewrite decode_kernel_tag in DEC.
  - by eauto.
Qed.

Lemma invariant_store_mvec mem mvec regs cache int :
  forall (KINV : invariant mem regs cache int),
    invariant (Concrete.store_mvec mem mvec) regs cache int.
Proof.
intros (RVEC & PROG & MEM & GRULES1 & GRULES2 & REGS & INT).
do 7 (try split; eauto).
- move=> addr IN.
  rewrite /Concrete.store_mvec getm_union.
  set m := mkpartmap _.
  rewrite -[isSome (m addr)]/(addr \in m) mem_mkpartmap /=.
  have [Hin | Hnin] := boolP (addr \in Concrete.mvec_fields mt); last by eauto.
  have: addr \in m by rewrite mem_mkpartmap.
  rewrite inE; case Heq: (m addr)=> [v|] //= _.
  suff: taga v = Concrete.TKernel.
    by case: v {Heq} => [w t] /= ->; eauto.
  apply/eqP; move/getm_mkpartmap': Heq.
  rewrite -{2}[v]/((addr, v).2); move: (addr, v).
  by apply/allP => /=; rewrite !eqxx /=.
- move=> addr instr Hget; rewrite getm_union.
  set m := mkpartmap _; set addr' := (_ + _)%w.
  rewrite -[isSome (m addr')]/(addr' \in m) mem_mkpartmap /=.
  have: addr' \notin Concrete.mvec_and_rvec_fields mt by apply: MEM.
  by rewrite mem_cat=> /norP [/negbTE -> _]; eauto.
- by eapply policy_invariant_store_mvec; eauto.
Qed.

Definition fault_handler_invariant : kernel_invariant := {|
  kernel_invariant_statement := invariant;
  kernel_invariant_upd_reg := invariant_upd_reg;
  kernel_invariant_upd_mem := invariant_upd_mem;
  kernel_invariant_store_mvec := invariant_store_mvec
|}.

End invariant.

End fault_handler.

Arguments rtrpc {_ _}.
Arguments rtr {_ _}.
Arguments rb {_ _}.
Arguments ri1 {_ _}.
Arguments ri2 {_ _}.
Arguments ri3 {_ _}.
Arguments ri4 {_ _}.
Arguments ri5 {_ _}.
Arguments rop {_ _}.
Arguments rtpc {_ _}.
Arguments rti {_ _}.
Arguments rt1 {_ _}.
Arguments rt2 {_ _}.
Arguments rt3 {_ _}.
Arguments if_ {_ _} r t f.
Arguments extract_user_tag {_ _} rsrc rsucc rut.
Arguments wrap_user_tag {_ _} rut rdst.
