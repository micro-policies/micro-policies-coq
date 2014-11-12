Require Import ZArith.

Require Import ssreflect ssrfun ssrbool eqtype fintype seq finset.

Require Import lib.utils lib.partial_maps lib.Coqlib lib.Integers.
Require Import common.common.
Require Import concrete.concrete.
Require Import concrete.int_32.
Require Import symbolic.symbolic.
Require Import symbolic.int_32.
Require Import symbolic.refinement_common.
Require Import symbolic.backward.
Require Import symbolic.rules.
Require Import compartmentalization.common.
Require Import compartmentalization.symbolic.
Require Import compartmentalization.abstract.
Require Import compartmentalization.refinementSA.

Import DoNotation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Refinement.

Let t := concrete_int_32_t.
Let sp := @Sym.sym_compartmentalization t.
Existing Instance concrete_int_32_ops.
Existing Instance concrete_int_32_ops_spec.
Existing Instance sp.

Definition read_kernel_word (mem : Concrete.memory t) (addr : word t) : option (word t) :=
  do! x <- PartMaps.get mem addr;
  if Concrete.is_kernel_tag (common.tag x) then Some (common.val x)
  else None.

Lemma read_kernel_word_monotonic mem mem' addr x ct x' ct' :
  PartMaps.get mem addr = Some x@ct ->
  ~~ Concrete.is_kernel_tag ct ->
  PartMaps.upd mem addr x'@ct' = Some mem' ->
  ~~ Concrete.is_kernel_tag ct' ->
  read_kernel_word mem' =1 read_kernel_word mem.
Proof.
  move=> Hget Hnk Hupd Hnk' addr'.
  rewrite /read_kernel_word (PartMaps.get_upd Hupd).
  have [-> {addr'} /=|//] := altP (addr' =P addr).
  by rewrite Hget /= (negbTE Hnk) (negbTE Hnk').
Qed.

Fixpoint read_kernel_array (mem : Concrete.memory t) (addr : word t) (count : nat) : option (seq.seq (word t)) :=
  match count with
  | 0 => Some [::]
  | S count =>
    do! x <- read_kernel_word mem addr;
    do! arr <- read_kernel_array mem (addr + 1)%w count;
    Some (x :: arr)
  end.

Lemma read_kernel_array_monotonic mem mem' addr x ct x' ct' :
  PartMaps.get mem addr = Some x@ct ->
  ~~ Concrete.is_kernel_tag ct ->
  PartMaps.upd mem addr x'@ct' = Some mem' ->
  ~~ Concrete.is_kernel_tag ct' ->
  read_kernel_array mem =2 read_kernel_array mem'.
Proof.
  move=> Hget Hnk Hupd Hnk' addr' count.
  elim: count addr' => [|count IH] addr' //=.
  by rewrite (read_kernel_word_monotonic Hget Hnk Hupd Hnk') IH.
Qed.

Definition read_set (mem : Concrete.memory t) (addr : word t) : option {set word t} :=
  do! count <- PartMaps.get mem addr;
  if Concrete.is_kernel_tag (common.tag count) then
    omap (fun arr => [set x : [finType of word t] in arr])
         (read_kernel_array mem (addr + 1)%w (Z.to_nat (Word.unsigned (common.val count))))
  else
    None.

Lemma read_set_monotonic mem mem' addr x ct x' ct' :
  PartMaps.get mem addr = Some x@ct ->
  ~~ Concrete.is_kernel_tag ct ->
  PartMaps.upd mem addr x'@ct' = Some mem' ->
  ~~ Concrete.is_kernel_tag ct' ->
  read_set mem =1 read_set mem'.
Proof.
  move=> Hget Hnk Hupd Hnk' addr'.
  rewrite /read_set (PartMaps.get_upd Hupd).
  have [-> {addr'} /=|_] := altP (addr' =P addr).
    by rewrite Hget /= (negbTE Hnk) (negbTE Hnk').
  case: (PartMaps.get mem addr') => [count|] //=.
  by rewrite (read_kernel_array_monotonic Hget Hnk Hupd Hnk').
Qed.

Definition decode_reg_tag (mem : Concrete.memory t) (tg : word t) : option (tag unit) :=
  let: [wu ut; w']%w := Word.unpack [:: 29; 1] tg in
  if w' == Word.one then
    if ut == Word.zero then Some (USER tt)
    else None
  else None.

Definition decode_data_tag (mem : Concrete.memory t) (tg : word t) : option (tag (Sym.data_tag t)) :=
  let: [wu ut; w']%w := Word.unpack [:: 29; 1] tg in
  if w' == Word.zero then None
  else if (w' == Word.one) || (w' == Word.repr 2) then
    let addr : word t := Word.castu ut in
    do! cid <- read_kernel_word mem addr;
    do! Iaddr <- read_kernel_word  mem (addr + 1)%w;
    do! I <- read_set mem Iaddr;
    do! Waddr <- read_kernel_word mem (addr + 2)%w;
    do! W <- read_set mem Waddr;
    let tg := Sym.DATA cid I W in
    if w' == Word.one then Some (USER tg)
    else Some (ENTRY tg)
  else None.

Lemma decode_data_tag_user_inv mem tg ut :
  decode_data_tag mem tg = Some (USER ut) ->
  ~~ Concrete.is_kernel_tag tg.
Proof.
  move=> Hdec.
  apply/negP => /eqP E.
  by rewrite {}E {tg} in Hdec.
Qed.

Definition decode_pc_tag (mem : Concrete.memory t) (tg : word t) : option (tag (Sym.pc_tag t)) :=
  let: [wu ut; w']%w := Word.unpack [:: 29; 1] tg in
  if w' == Word.zero then None
  else if (w' == Word.one) || (w' == Word.repr 2) then
    let: [wu wf; cid_addr]%w := Word.unpack [:: 0; 28] ut in
    let wf := if wf == Word.zero then INTERNAL
              else JUMPED in
    let cid_addr := Word.castu cid_addr in
    do! cid <- read_kernel_word mem cid_addr;
    let tg := Sym.PC wf cid in
    if w' == Word.one then Some (USER tg)
    else Some (ENTRY tg)
  else None.

Instance encodable_stags : encodable t (@Sym.stags t) := {
  decode tk mem tg :=
    match tk with
    | Symbolic.R => decode_reg_tag mem tg
    | Symbolic.M => decode_data_tag mem tg
    | Symbolic.P => decode_pc_tag mem tg
    end
}.
Proof.
  - move=> mem mem' addr x y ct st ct' st' [] //.
    + move=> Hget /decode_data_tag_user_inv Hnk Hupd
                  /decode_data_tag_user_inv Hnk' addr'.
      rewrite /decode_data_tag.
      case: (Word.unpack _ _) => [ut [w' []]].
      case: (w' == 0%w) => //.
      case: (_ || _) => //.
      rewrite !(read_kernel_word_monotonic Hget Hnk Hupd Hnk').
      case: (read_kernel_word _ (Word.castu ut + 1)%w) => [Iaddr|] //=.
      rewrite (read_set_monotonic Hget Hnk Hupd Hnk').
      case: (read_kernel_word _ (Word.castu ut + 2)%w) => [Waddr|] //=.
      by rewrite (read_set_monotonic Hget Hnk Hupd Hnk').
    + move=> Hget /decode_data_tag_user_inv Hnk Hupd
                  /decode_data_tag_user_inv Hnk' addr'.
      rewrite /decode_pc_tag.
      case: (Word.unpack _ _) => [ut [w' []]].
      case: (w' == 0%w) => //.
      case: (_ || _) => //.
      case: (Word.unpack _ _) => [wf [cid_addr []]].
      by rewrite (read_kernel_word_monotonic Hget Hnk Hupd Hnk').
  - by case.
Qed.

Context {monitor_invariant : kernel_invariant}
        {syscall_addrs : compartmentalization_syscall_addrs t}.

Inductive refine_state (ast : Abs.state t) (cst : Concrete.state t) : Prop :=
| rs_intro : forall (sst : Symbolic.state t),
               Abs.good_state ast ->
               refinement_common.refine_state monitor_invariant Sym.syscalls sst cst ->
               refinementSA.refine ast sst ->
               refine_state ast cst.
Hint Constructors refine_state.

Hypothesis implementation_correct :
  kernel_code_correctness monitor_invariant Sym.syscalls.

Lemma backwards_refinement_as ast sst sst' :
  Abs.good_state ast ->
  refinementSA.refine ast sst ->
  exec (Symbolic.step Sym.syscalls) sst sst' ->
  exists ast',
    exec (fun ast ast' => Abs.step ast ast') ast ast' /\
    Abs.good_state ast' /\
    refinementSA.refine ast' sst'.
Proof.
  move => GOOD REF EXEC.
  elim: EXEC ast GOOD REF => {sst sst'} [sst _ |sst sst' sst'' _ STEPS EXEC IH] ast GOOD REF; first by eauto 7.
  exploit backward_simulation; eauto.
  intros (ast' & STEPA & REF').
  have GOOD' := Abs.good_state_preserved (spec := concrete_int_32_ops_spec)
                                         STEPA GOOD.
  exploit IH; eauto.
  intros (ast'' & EXECA & GOOD'' & REF'').
  eauto 7.
Qed.

Lemma backwards_refinement ast cst cst' :
  refine_state ast cst ->
  exec (@Concrete.step t _ masks) cst cst' ->
  in_user cst' = true ->
  exists ast',
    exec (fun ast ast' => Abs.step ast ast') ast ast' /\
    refine_state ast' cst'.
Proof.
  move => [sst GOOD SC AS] EXECC INUSER.
  exploit @backward.backwards_refinement; eauto.
  intros (sst' & EXECS & SC').
  exploit backwards_refinement_as; eauto.
  intros (ast' & EXECA & GOOD' & AS'). eauto 7.
Qed.

End Refinement.
