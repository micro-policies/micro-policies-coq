From mathcomp Require Import ssreflect ssrfun ssrbool eqtype fintype seq ssrint finset.
From extructures Require Import ord fmap.
From CoqUtils Require Import hseq word.

Require Import lib.utils lib.fmap_utils.
Require Import common.types.
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

Let mt := concrete_int_32_mt.
Let sp := @Sym.sym_compartmentalization mt.
Existing Instance concrete_int_32_ops.
Existing Instance concrete_int_32_ops_spec.
Existing Instance sp.

Implicit Type mem : Concrete.memory mt.

Definition read_monitor_word mem (addr : mword mt) : option (mword mt) :=
  do! x <- mem addr;
  if Concrete.is_monitor_tag (taga x) then Some (vala x)
  else None.

Lemma read_monitor_word_monotonic mem addr x ct x' ct' :
  mem addr = Some x@ct ->
  ~~ Concrete.is_monitor_tag ct ->
  ~~ Concrete.is_monitor_tag ct' ->
  read_monitor_word (setm mem addr x'@ct') =1 read_monitor_word mem.
Proof.
  move=> Hget Hnk Hnk' addr'.
  rewrite /read_monitor_word setmE.
  have [-> {addr'} /=|//] := altP (addr' =P addr).
  by rewrite Hget /= (negbTE Hnk) (negbTE Hnk').
Qed.

Fixpoint read_monitor_array (mem : Concrete.memory mt) (addr : mword mt) (count : nat) : option (seq (mword mt)) :=
  match count with
  | 0 => Some [::]
  | S count =>
    do! x <- read_monitor_word mem addr;
    do! arr <- read_monitor_array mem (addr + 1)%w count;
    Some (x :: arr)
  end.

Lemma read_monitor_array_monotonic mem addr x ct x' ct' :
  mem addr = Some x@ct ->
  ~~ Concrete.is_monitor_tag ct ->
  ~~ Concrete.is_monitor_tag ct' ->
  read_monitor_array mem =2 read_monitor_array (setm mem addr x'@ct').
Proof.
  move=> Hget Hnk Hnk' addr' count.
  elim: count addr' => [|count IH] addr' //=.
  by rewrite (read_monitor_word_monotonic x' Hget Hnk Hnk') IH.
Qed.

Definition read_set (mem : Concrete.memory mt) (addr : mword mt) : option {set mword mt} :=
  do! count <- mem addr;
  if Concrete.is_monitor_tag (taga count) then
    omap (fun arr => [set x : [finType of mword mt] in arr])
         (read_monitor_array mem (addr + 1)%w (nat_of_ord (ord_of_word (vala count))))
  else
    None.

Lemma read_set_monotonic mem addr x ct x' ct' :
  mem addr = Some x@ct ->
  ~~ Concrete.is_monitor_tag ct ->
  ~~ Concrete.is_monitor_tag ct' ->
  read_set mem =1 read_set (setm mem addr x'@ct').
Proof.
  move=> Hget Hnk Hnk' addr'.
  rewrite /read_set setmE.
  have [-> {addr'} /=|_] := altP (addr' =P addr).
    by rewrite Hget /= (negbTE Hnk) (negbTE Hnk').
  case: (mem addr') => [count|] //=.
  by rewrite (read_monitor_array_monotonic x' Hget Hnk Hnk').
Qed.

Definition decode_reg_tag (mem : Concrete.memory mt) (tg : mword mt) : option unit :=
  let: [hseq ut; w']%w := @wunpack [:: 30; 2] tg in
  if w' == 1%w then
    if ut == 0%w then Some tt
    else None
  else None.

Definition decode_data_tag (mem : Concrete.memory mt) (tg : mword mt) :
  option (mtag (@Sym.stags mt)) :=
  let: [hseq ut; w']%w := @wunpack [:: 30; 2] tg in
  if w' == 0%w then None
  else if (w' == 1%w) || (w' == as_word 2) then
    let addr : mword mt := as_word (ord_of_word ut) in
    do! cid <- read_monitor_word mem addr;
    do! Iaddr <- read_monitor_word  mem (addr + 1)%w;
    do! I <- read_set mem Iaddr;
    do! Waddr <- read_monitor_word mem (addr + as_word 2)%w;
    do! W <- read_set mem Waddr;
    let tg := Sym.DATA cid I W in
    if w' == 1%w then Some (@User Sym.stags tg)
    else Some (@Entry Sym.stags tg)
  else None.

Lemma decode_data_tag_user_inv mem tg ut :
  decode_data_tag mem tg = Some (User ut) ->
  ~~ Concrete.is_monitor_tag tg.
Proof.
move=> Hdec; apply/negP => /eqP E; move: Hdec.
by rewrite {}E /decode_data_tag 2!wunpackS.
Qed.

Definition decode_pc_tag (mem : Concrete.memory mt) (tg : mword mt) : option (Sym.pc_tag mt) :=
  let: [hseq ut; w']%w := @wunpack [:: 30; 2] tg in
  if w' == 0%w then None
  else if (w' == 1%w) || (w' == as_word 2) then
    let: [hseq wf; cid_addr]%w := @wunpack [:: 1; 29] ut in
    let wf := if wf == 0%w then INTERNAL
              else JUMPED in
    let cid_addr := as_word (ord_of_word cid_addr) in
    do! cid <- read_monitor_word mem cid_addr;
    let tg := Sym.PC wf cid in
    if w' == 1%w then Some tg
    else None
  else None.

Instance encodable_stags : encodable mt (@Sym.stags mt) := {
  decode tk :=
    match tk return Concrete.memory mt -> mword mt -> option (wtag (@Sym.stags mt) tk) with
    | Symbolic.R => decode_reg_tag
    | Symbolic.M => decode_data_tag
    | Symbolic.P => decode_pc_tag
    end
}.
Proof.
- move=> mem addr x y ct st ct' st' [] //.
  + move=> Hget /decode_data_tag_user_inv Hnk
                /decode_data_tag_user_inv Hnk' addr'.
    rewrite /decode_data_tag.
    case: (wunpack _) => [ut [w' []]].
    case: (w' == 0%w) => //.
    case: (_ || _) => //.
    rewrite !(read_monitor_word_monotonic _ Hget Hnk Hnk').
    case: (read_monitor_word _ (as_word (ord_of_word ut) + 1)%w) => [Iaddr|] //=.
    rewrite -(read_set_monotonic _ Hget Hnk Hnk').
    case: (read_monitor_word _ (as_word (ord_of_word ut) + as_word 2)%w) => [Waddr|] //=.
    by rewrite -(read_set_monotonic _ Hget Hnk Hnk').
  + move=> Hget /decode_data_tag_user_inv Hnk
                /decode_data_tag_user_inv Hnk' addr'.
    rewrite /decode_pc_tag.
    case: (wunpack _) => [ut [w' []]].
    case: (w' == 0%w) => //.
    case: (_ || _) => //.
    case: (wunpack _) => [wf [cid_addr []]].
    by rewrite (read_monitor_word_monotonic _ Hget Hnk Hnk').
- move=> [] m /=.
  + by rewrite /decode_reg_tag 2!wunpackS.
  + by rewrite /decode_data_tag 2!wunpackS.
  by rewrite /decode_pc_tag 2!wunpackS.
Qed.

Context {monitor_invariant : monitor_invariant}
        {syscall_addrs : compartmentalization_syscall_addrs mt}.

Inductive refine_state (ast : Abs.state mt) (cst : Concrete.state mt) : Prop :=
| rs_intro : forall (sst : Symbolic.state mt),
               Abs.good_state ast ->
               refinement_common.refine_state monitor_invariant Sym.syscalls sst cst ->
               refinementSA.refine ast sst ->
               refine_state ast cst.
Hint Constructors refine_state.

Hypothesis implementation_correct :
  monitor_code_bwd_correctness monitor_invariant Sym.syscalls.

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
have [ast' [STEPA REF']] := backward_simulation GOOD REF STEPS.
have GOOD' : Abs.good_state ast'
  by eapply Abs.good_state_preserved; eauto with typeclass_instances.
have [ast'' [EXECA [GOOD'' REF'']]] := IH _ GOOD' REF'.
by eauto 7.
Qed.

Lemma backwards_refinement ast cst cst' :
  refine_state ast cst ->
  exec (@Concrete.step mt _ masks) cst cst' ->
  in_user cst' = true ->
  exists ast',
    exec (fun ast ast' => Abs.step ast ast') ast ast' /\
    refine_state ast' cst'.
Proof.
move => [sst GOOD SC AS] EXECC INUSER.
have [sst' EXECS SC'] := backward.backwards_refinement SC EXECC INUSER.
have [ast' [EXECA [GOOD' AS']]] := backwards_refinement_as GOOD AS EXECS.
by eauto 7.
Qed.

End Refinement.
