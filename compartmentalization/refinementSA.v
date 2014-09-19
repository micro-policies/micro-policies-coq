Require Import List. Import ListNotations.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype finset.

Require Import lib.Integers lib.utils lib.ordered lib.partial_maps common.common.
Require Import symbolic.symbolic symbolic.rules.
Require Import lib.haskell_notation.
Require Import lib.ssr_list_utils.
Require Import compartmentalization.common compartmentalization.isolate_sets.
Require Import compartmentalization.abstract compartmentalization.symbolic.

Set Bullet Behavior "Strict Subproofs".
Import DoNotation.

Section RefinementSA.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import PartMaps.
Import Abs.Notations.
Import Abs.Hints.
Import Sym.EnhancedDo.

(* ssreflect exposes `succn' as a synonym for `S' *)
Local Notation II := Logic.I.

Context
  (t            : machine_types)
  {ops          : machine_ops t}
  {spec         : machine_ops_spec ops}
  {scr          : @syscall_regs t}
  {cmp_syscalls : compartmentalization_syscall_addrs t}.

Notation word     := (word t).
Notation pc_tag   := (Sym.pc_tag t).
Notation data_tag := (Sym.data_tag t).
Notation sym_compartmentalization := (@Sym.sym_compartmentalization t).

Notation spcatom := (atom word pc_tag).
Notation smatom  := (atom word data_tag).
Notation sratom  := (atom word unit).
Notation svalue  := (@val word _).
Notation slabel  := (@common.tag word _).

Notation astate    := (@Abs.state t).
Notation sstate    := (@Symbolic.state t sym_compartmentalization).
Notation AState    := (@Abs.State t).
Notation SState    := (@Symbolic.State t sym_compartmentalization).
Notation SInternal := (@Sym.Internal t).

Notation astep := Abs.step.
Notation sstep := Sym.step.

Hint Immediate word_map_axioms.
Hint Immediate reg_map_axioms.

(* Avoiding some type class resolution problems *)

Arguments Sym.sget {_ _} s p : simpl never.
Arguments Sym.supd {_ _} s p tg : simpl never.

Canonical compartment_eqType :=
  Eval hnf in EqType (Abs.compartment t) (Abs.compartment_eqMixin t).

(* We check the compartment stuff later *)
Definition refine_pc_b (apc : word) (spc : spcatom) :=
  match spc with
    | spc' @ _ => apc == spc'
  end.

(* We check the compartment stuff later *)
Definition refine_mem_loc_b (ax : word) (sx : smatom) : bool :=
  match sx with
    | sx' @ _ => ax == sx'
  end.

Definition refine_reg_b (ar : word) (sr : sratom) : bool :=
  match sr with
    | sr' @ _ => ar == sr'
  end.

Definition refine_memory : memory t -> Sym.memory t -> Prop :=
  pointwise refine_mem_loc_b.

Definition refine_registers : registers t -> Sym.registers t -> Prop :=
  pointwise refine_reg_b.

Section WithSym.
Import Sym.

Definition get_compartment_id (sst : sstate)
                              (c   : Abs.compartment t) : option word :=
  [pick cid |
    ((omap data_tag_compartment \o Sym.sget sst) @: Abs.address_space c) ==
    [set Some cid]].

Definition well_defined_compartments (sst : sstate)
                                     (C   : seq (Abs.compartment t)) : Prop :=
  forall p, sget sst p -> Abs.in_compartment_opt C p.

Definition well_defined_ids (sst : sstate)
                            (C   : seq (Abs.compartment t)) : Prop :=
  forall c, c \in C -> get_compartment_id sst c.

(* AAA: Does this imply disjointness? *)
Definition unique_ids (sst : sstate)
                      (C   : seq (Abs.compartment t)) : Prop :=
  forall c1 c2,
    c1 \in C ->
    c2 \in C ->
    get_compartment_id sst c1 = get_compartment_id sst c2 ->
    c1 = c2.

Definition well_formed_targets (targets : Abs.compartment t -> {set word})
                               (sources : data_tag _        -> {set word})
                               (sst     : sstate)
                               (C       : seq (Abs.compartment t)) : Prop :=
  forall c cid,
    c \in C ->
    get_compartment_id sst c = Some cid ->
    targets c =
    [set p | oapp (fun s : {set word} => cid \in s) false
                  (omap sources (Sym.sget sst p)) ].

Definition well_formed_jump_targets : sstate -> seq (Abs.compartment t) -> Prop :=
  well_formed_targets (fun c => Abs.jump_targets c) data_tag_incoming.

Definition well_formed_store_targets : sstate -> seq (Abs.compartment t) -> Prop :=
  well_formed_targets (fun c => Abs.store_targets c) data_tag_writers.

End WithSym.

Definition refine_previous_b (sk : where_from) (prev : Abs.compartment t)
                             (sst : sstate) : bool :=
  match Symbolic.pc sst with
    | _ @ (Sym.PC F cid) => (sk == F) &&
                            (get_compartment_id sst prev == Some cid)
  end.

Definition refine_syscall_addrs_b (AM : memory t) (SM : Sym.memory t) : bool :=
  [&& [seq get AM x | x <- syscall_addrs] == [:: None; None; None] ,
      [seq get SM x | x <- syscall_addrs] == [:: None; None; None] &
      uniq syscall_addrs ].

Record refine (ast : astate) (sst : sstate) : Prop := RefineState
  { pc_refined           : refine_pc_b               (Abs.pc           ast)
                                                     (Symbolic.pc      sst)
  ; regs_refined         : refine_registers          (Abs.regs         ast)
                                                     (Symbolic.regs    sst)
  ; mems_refined         : refine_memory             (Abs.mem          ast)
                                                     (Symbolic.mem     sst)
  ; compartments_wd      : well_defined_compartments sst
                                                     (Abs.compartments ast)
  ; ids_well_defined     : well_defined_ids          sst
                                                     (Abs.compartments ast)
  ; ids_unique           : unique_ids                sst
                                                     (Abs.compartments ast)
  ; jump_targets_wf      : well_formed_jump_targets  sst
                                                     (Abs.compartments ast)
  ; store_targets_wf     : well_formed_store_targets sst
                                                     (Abs.compartments ast)
  ; previous_refined     : refine_previous_b         (Abs.step_kind    ast)
                                                     (Abs.previous     ast)
                                                     sst
  ; syscalls_refined     : refine_syscall_addrs_b    (Abs.mem          ast)
                                                     (Symbolic.mem     sst)
  ; internal_refined     : Sym.good_internal         sst }.

Generalizable All Variables.

Theorem refine_good : forall `(REFINE : refine ast sst),
  Abs.good_state ast ->
  Sym.good_state sst.
Proof.
  move=> [Apc AR AM AC Ask Aprev]
         [SM SR [Spc Lpc] [Snext SiT SaJT SaST]]
         [RPC RREGS RMEMS WDCOMPS WDIDS UIDS WFJTS WFSTS RPREV RSCS RINT]
         /and4P [ELEM GOODS SS SP];
    simpl in *.
  repeat split.
  - destruct Lpc; try discriminate.
    move: RPREV => /andP [/eqP? /eqP RPREV]; subst.
    rewrite /get_compartment_id in RPREV.
    case: pickP RPREV => //= => x /eqP RPREV.
    have: Some x == Some x by apply eq_refl.
    rewrite -(in_set1 (Some x)) -RPREV => /imsetP [y IN_y ->] SGET.
      clear x RPREV.
      exists y; move: SGET.
    case SGET: (Sym.sget _ y) => [L|//].
    case: L SGET => //=  [c' I W] SGET.
    + rewrite SGET /= => [[?]]. subst c'.
      by eauto.
    + by have /= -> := SGET.
  - assumption.
Qed.

Ltac unoption :=
  repeat match goal with
    | EQ  : Some _ = Some _ |- _ => inversion EQ; subst; clear EQ
    | NEQ : Some _ = None   |- _ => discriminate
    | NEQ : None   = Some   |- _ => discriminate
    | EQ  : None   = None   |- _ => clear EQ
  end.

Lemma get_compartment_id_in_compartment_eq (C : seq (Abs.compartment t)) sst c p :
  well_defined_compartments sst C ->
  well_defined_ids sst C ->
  unique_ids sst C ->
  c \in C ->
  (get_compartment_id sst c == (omap Sym.data_tag_compartment (Sym.sget sst p))) =
  (p \in Abs.address_space c).
Proof.
  move=> /(_ p) WDC WDID UNIQUE IN.
  move: (WDID c IN).
  case ID: (get_compartment_id sst c) => [cid|] // _.
  apply/(sameP idP)/(iffP idP).

  - move: ID.
    rewrite /get_compartment_id.
    case: pickP => // cid' /eqP Hcid' [E]. subst cid'.
    move/(mem_imset (omap Sym.data_tag_compartment \o Sym.sget sst)) => /=.
    rewrite Hcid' in_set1.
    by rewrite eq_sym.

  - case GET: (Sym.sget sst p) WDC => [[cid' Ia Sa]|] //= /(_ erefl).
    case E: (Abs.in_compartment_opt C p) => [c'|] // _ /eqP [E']. subst cid'.
    case/Abs.in_compartment_opt_correct/andP: E => IN' INp.
    suff {UNIQUE} ID' : get_compartment_id sst c' = Some cid.
    { rewrite -ID' in ID.
      by rewrite (UNIQUE _ _ IN IN' ID). }
    move: (WDID c' IN').
    rewrite /get_compartment_id.
    case: pickP => // cid' /eqP Hcid' _.
    move/(mem_imset (omap Sym.data_tag_compartment \o Sym.sget sst)): INp.
    rewrite Hcid' in_set1 /= GET /=.
    by move/eqP=> ->.
Qed.

Lemma get_compartment_id_in_compartment (C : seq (Abs.compartment t)) sst c p :
  well_defined_compartments sst C ->
  well_defined_ids sst C ->
  unique_ids sst C ->
  c \in C ->
  (get_compartment_id sst c = (omap Sym.data_tag_compartment (Sym.sget sst p))) ->
  (p \in Abs.address_space c).
Proof.
  move=> WDC WDID UNIQUE IN H.
  by rewrite -(get_compartment_id_in_compartment_eq _ WDC WDID UNIQUE IN) H.
Qed.

Lemma in_compartment_get_compartment_id (C : seq (Abs.compartment t)) sst c p :
  well_defined_compartments sst C ->
  well_defined_ids sst C ->
  unique_ids sst C ->
  c \in C ->
  (p \in Abs.address_space c) ->
  get_compartment_id sst c = (omap Sym.data_tag_compartment (Sym.sget sst p)).
Proof.
  move=> WDC WDID UNIQUE IN H.
  apply/eqP.
  by rewrite (get_compartment_id_in_compartment_eq _ WDC WDID UNIQUE IN) H.
Qed.

Lemma refined_reg_value : forall AR SR,
  refine_registers AR SR ->
  forall r, get AR r = (svalue <$> get SR r).
Proof.
  move=> AR SR REFINE r;
    rewrite /refine_registers /refine_reg_b /pointwise in REFINE.
  specialize REFINE with r.
  set oax := get AR r in REFINE *; set osv := get SR r in REFINE *;
    destruct oax as [|], osv as [[? []]|]; simpl in *; try done.
  by move/eqP in REFINE; subst.
Qed.

Lemma refined_mem_value : forall AM SM,
  refine_memory AM SM ->
  forall p, get AM p = (svalue <$> get SM p).
Proof.
  move=> AM SM REFINE p;
    rewrite /refine_memory /refine_mem_loc_b /pointwise in REFINE.
  specialize REFINE with p.
  set oax := get AM p in REFINE *; set osv := get SM p in REFINE *;
    destruct oax as [|], osv as [[? []]|]; simpl in *; try done.
  by move/eqP in REFINE; subst.
Qed.

Definition equilabeled (sst1 sst2 : sstate) : Prop :=
  forall p,
    match Sym.sget sst1 p , Sym.sget sst2 p with
      | Some L1 , Some L2 => L1 = L2
      | None    , None        => True
      | _       , _           => False
    end.

Definition equicompartmental (sst1 sst2 : sstate) : Prop :=
  forall p,
    match Sym.sget sst1 p , Sym.sget sst2 p with
      | Some L1 , Some L2 => Sym.data_tag_compartment L1 =
                             Sym.data_tag_compartment L2
      | None    , None        => True
      | _       , _           => False
    end.

Definition tags_subsets (sst1 sst2 : sstate) : Prop :=
  forall p,
    match Sym.sget sst1 p , Sym.sget sst2 p with
      | Some (Sym.DATA c1 I1 W1) , Some (Sym.DATA c2 I2 W2) =>
        c1 = c2 /\ I1 \subset I2 /\ W1 \subset W2
      | None , None =>
        True
      | _ , _ =>
        False
    end.

Definition tags_subsets_in (ps : {set word}) (sst1 sst2 : sstate) : Prop :=
  forall p,
    match Sym.sget sst1 p , Sym.sget sst2 p with
      | Some (Sym.DATA c1 I1 W1) , Some (Sym.DATA c2 I2 W2) =>
        (p \in ps -> c1 = c2) /\ I1 \subset I2 /\ W1 \subset W2
      | None , None =>
        True
      | _ , _ =>
        False
    end.

Definition tags_subsets_cid (cid : word) (sst1 sst2 : sstate) : Prop :=
  forall p,
    match Sym.sget sst1 p , Sym.sget sst2 p with
      | Some (Sym.DATA c1 I1 W1) , Some (Sym.DATA c2 I2 W2) =>
        (c1 = cid \/ c2 = cid -> c1 = c2) /\
        I1 \subset I2 /\ W1 \subset W2
      | None , None =>
        True
      | _ , _ =>
        False
    end.

Definition tags_subsets_add_1 (c' : word)
                              (sst1 sst2 : sstate) : Prop :=
  forall p,
    match Sym.sget sst1 p , Sym.sget sst2 p with
      | Some (Sym.DATA c1 I1 W1) , Some (Sym.DATA c2 I2 W2) =>
        c1 = c2                    /\
        (I1 = I2 \/ c' |: I1 = I2) /\
        (W1 = W2 \/ c' |: W1 = W2)
      | None , None =>
        True
      | _ , _ =>
        False
    end.

Definition tags_subsets_add_1_in (ps : {set word})
                                 (c' : word)
                                 (sst1 sst2 : sstate) : Prop :=
  forall p,
    match Sym.sget sst1 p , Sym.sget sst2 p with
      | Some (Sym.DATA c1 I1 W1) , Some (Sym.DATA c2 I2 W2) =>
        (p \in ps -> c1 = c2)      /\
        (I1 = I2 \/ c' |: I1 = I2) /\
        (W1 = W2 \/ c' |: W1 = W2)
      | None , None =>
        True
      | _ , _ =>
        False
    end.

Lemma tags_subsets_in_tail : forall p ps sst sst',
  tags_subsets_in (p |: ps) sst sst' ->
  tags_subsets_in ps sst sst'.
Proof.
  rewrite /tags_subsets_in /=; move=> p ps sst sst' TSI a.
  specialize TSI with a.
  destruct (Sym.sget sst  a) as [[ ]|],
           (Sym.sget sst' a) as [[ ]|];
    try done.
  move: TSI => [EQ [? ?]]; repeat split; auto => Hin.
  suff: a \in p |: ps by auto.
  by rewrite in_setU1 Hin orbT.
Qed.

Lemma tags_subsets_trans : forall sst sst' sst'',
  tags_subsets sst  sst'  ->
  tags_subsets sst' sst'' ->
  tags_subsets sst  sst''.
Proof.
  move=> sst sst' sst'' TSI TSI' p.
  specialize (TSI p); specialize (TSI' p).
  destruct (Sym.sget sst   p) as [[ ]|],
           (Sym.sget sst'  p) as [[ ]|],
           (Sym.sget sst'' p) as [[ ]|];
    try done.
  repeat invh and; subst; auto.
  by eauto using subset_trans.
Qed.

Lemma tags_subsets_in_trans : forall ps sst sst' sst'',
  tags_subsets_in ps sst  sst'  ->
  tags_subsets_in ps sst' sst'' ->
  tags_subsets_in ps sst  sst''.
Proof.
  move=> ps sst sst' sst'' TSI TSI' p.
  specialize (TSI p); specialize (TSI' p).
  destruct (Sym.sget sst   p) as [[ ]|],
           (Sym.sget sst'  p) as [[ ]|],
           (Sym.sget sst'' p) as [[ ]|];
    try done.
  move: TSI TSI' => [H1 [H2 H3]] [H1' [H2' H3']].
  repeat split; solve [intuition congruence|eauto using subset_trans].
Qed.

Lemma tags_subsets_add_1_trans : forall c' sst sst' sst'',
  tags_subsets_add_1 c' sst  sst'  ->
  tags_subsets_add_1 c' sst' sst'' ->
  tags_subsets_add_1 c' sst  sst''.
Proof.
  move=> c' sst sst' sst'' TSA TSA' p.
  specialize (TSA p); specialize (TSA' p).
  destruct (Sym.sget sst   p) as [[ ]|],
           (Sym.sget sst'  p) as [[ ]|],
           (Sym.sget sst'' p) as [[ ]|];
    try done.
  move: TSA TSA' => [H1 [H2 H3]] [H1' [H2' H3']].
  repeat split.
  - by subst.
  - destruct H2,H2'; subst; try rewrite setUA setUid; auto.
  - destruct H3,H3'; subst; try rewrite setUA setUid; auto.
Qed.

Lemma tags_subsets_add_1_in_trans : forall ps c' sst sst' sst'',
  tags_subsets_add_1_in ps c' sst  sst'  ->
  tags_subsets_add_1_in ps c' sst' sst'' ->
  tags_subsets_add_1_in ps c' sst  sst''.
Proof.
  move=> ps c' sst sst' sst'' TSAI TSAI' p.
  specialize (TSAI p); specialize (TSAI' p).
  destruct (Sym.sget sst   p) as [[ ]|],
           (Sym.sget sst'  p) as [[ ]|],
           (Sym.sget sst'' p) as [[ ]|];
    try done.
  move: TSAI TSAI' => [H1 [H2 H3]] [H1' [H2' H3']].
  repeat split.
  - intuition congruence.
  - destruct H2,H2'; subst; try rewrite setUA setUid; auto.
  - destruct H3,H3'; subst; try rewrite setUA setUid; auto.
Qed.

Lemma tags_subsets_any_in : forall ps sst sst',
  tags_subsets       sst sst' ->
  tags_subsets_in ps sst sst'.
Proof.
  move=> ps sst sst' TS p; specialize (TS p).
  destruct (Sym.sget sst  p) as [[ ]|],
           (Sym.sget sst' p) as [[ ]|];
    try done.
  repeat invh and; subst; auto.
Qed.

Lemma tags_subsets_add_1_any_in : forall ps c' sst sst',
  tags_subsets_add_1       c' sst sst' ->
  tags_subsets_add_1_in ps c' sst sst'.
Proof.
  move=> ps c' sst sst' TSA p; specialize (TSA p).
  destruct (Sym.sget sst  p) as [[ ]|],
           (Sym.sget sst' p) as [[ ]|];
    try done.
  repeat invh and; subst; auto.
Qed.

Lemma get_compartment_id_same : forall sst sst' c,
  equilabeled sst sst' ->
  get_compartment_id sst c = get_compartment_id sst' c.
Proof.
  intros sst sst' [A J S] SAME.
  rewrite /get_compartment_id.
  apply eq_pick => p.
  apply f_equal2 => //.
  apply eq_imset => {p} p /=.
  move: (SAME p).
  case: (Sym.sget sst p) => [l|]; case: (Sym.sget sst' p) => [l'|] //.
  congruence.
Qed.

Theorem isolate_create_set_refined : forall AM SM,
  refine_memory AM SM ->
  forall p, isolate_create_set id AM p = isolate_create_set svalue SM p.
Proof.
  move=> AM SM REFINE p;
    rewrite /refine_memory /refine_mem_loc_b /pointwise in REFINE.
  rewrite /isolate_create_set.

  erewrite refined_mem_value; [|eassumption].
  set G := get SM p; destruct G as [[wpairs ?]|]; subst; simpl; try done.

  remember (BinInt.Z.to_nat (Word.signed wpairs)) as pairs; clear Heqpairs.
  remember (p + 1)%w as start; clear Heqstart; move: start.

  induction pairs as [|pairs]; simpl; [reflexivity | intros start].
  rewrite IHpairs; f_equal.
  rewrite /isolate_get_range.

  repeat (erewrite refined_mem_value; [|eassumption]).
  set G := get SM start; destruct G as [[low ?]|]; subst; simpl; try done.
  by set G := get SM (start + 1)%w; destruct G as [[high ?]|]; subst; simpl.
Qed.

Theorem retag_set_preserves_memory_refinement : forall ok retag ps sst sst' AM,
  Sym.retag_set ok retag ps sst ?= sst' ->
  refine_memory AM (Symbolic.mem sst) ->
  refine_memory AM (Symbolic.mem sst').
Proof.
  rewrite /Sym.retag_set /Sym.retag_one.
  intros ok retag ps; induction ps as [|p ps]; simpl;
    intros sst sst'' AM RETAG REFINE.
  - by inversion RETAG; subst.
  - let I := fresh "I"
    in undo1 RETAG sst'; undoDATA def_sst' x c I W; undo1 def_sst' OK;
       destruct (retag p c I W) as [c' I' W'] eqn:TAG; try discriminate.
    apply IHps with (AM := AM) in RETAG; [assumption|].
    rewrite /refine_memory /refine_mem_loc_b /pointwise in REFINE *; intros a;
      specialize REFINE with a.
    destruct (get AM a) as [w|],
             (get (Symbolic.mem sst) a) as [[w' []]|] eqn:GET';
      rewrite GET' in REFINE; try done;
      try (move/eqP in REFINE; subst w').
    + destruct (a == p) eqn:EQ; move/eqP in EQ; subst.
      * generalize def_sst' => SUPD.
        eapply Sym.sget_supd_eq in def_sst'.
        destruct sst as [SM SR SPC [snext SiT SaJT SaST]];
          rewrite /Sym.sget /= GET' in def_xcIW.
        inversion def_xcIW; subst.
        eapply Sym.get_supd_eq in SUPD; [|eassumption].
        by rewrite SUPD.
      * eapply Sym.get_supd_neq in def_sst'; try eassumption.
        by rewrite def_sst' GET'.
    + eapply Sym.get_supd_none in def_sst'; [|eassumption].
      by rewrite def_sst'.
Qed.

Lemma in_compartment_update A J Sa J' Sa' AC p c :
  AC ⊢ p ∈ c ->
  exists c', <<A,J,Sa>> :: rem_all <<A,J',Sa'>> AC ⊢ p ∈ c'.
Proof.
  rewrite /rem_all.
  elim: AC => [|c' AC IH]; first by rewrite /Abs.in_compartment.
  rewrite /Abs.in_compartment in_cons => /andP [/orP [/eqP <-| Hin] Has].
  - rewrite /=.
    have [E|NE] := altP (c =P <<A,J',Sa'>>).
    + exists <<A,J,Sa>> => /=.
      rewrite E in Has.
      by rewrite Has /= in_cons eqxx.
    + exists c.
      by rewrite Has /= !inE eqxx orbT.
  - have /IH {IH} [c'' /andP [Hin' ?]] : AC ⊢ p ∈ c by rewrite /Abs.in_compartment Has Hin.
    exists c''.
    apply/andP; split => //.
    rewrite !inE in Hin' *.
    case/orP: Hin' => [-> //| Hin' /=].
    have [E|NE] := altP (c' =P <<A,J',Sa'>>).
    + by rewrite /= Hin' orbT.
    + by rewrite inE Hin' !orbT.
Qed.

Lemma in_compartment_update' A J Sa J' Sa' AC p :
  Abs.in_compartment_opt AC p ->
  Abs.in_compartment_opt (<<A,J,Sa>> :: rem_all <<A,J',Sa'>> AC) p.
Proof.
  case E: (Abs.in_compartment_opt _ _) => [c|] // _.
  move/Abs.in_compartment_opt_correct in E.
  suff [? -> //] : exists c', Abs.in_compartment_opt (<<A,J,Sa>> :: rem_all <<A,J',Sa'>> AC) p ?= c'.
  have [c' Hc'] := @in_compartment_update A J Sa J' Sa' AC p c E.
  by apply/Abs.in_compartment_opt_present.
Qed.

Lemma supd_refine_memory AM sst sst' p c i w :
  Sym.supd sst p (Sym.DATA c i w) ?= sst' ->
  refine_memory AM (Symbolic.mem sst) ->
  refine_memory AM (Symbolic.mem sst').
Proof.
  case: sst => m r pc [? ? ? ?]; case: sst' => m' r' pc' [? ? ? ?].
  rewrite /Sym.supd /=.
  move=> UPD REF p'.
  case REP: (rep m p _) UPD => [m''|].
  - generalize (get_rep REP p') => {REP} REP [<- _ _ _ _ _ _].
    rewrite REP.
    have [->|NE] := (p' =P p); last exact: REF.
    move: {REF} (REF p).
    case: (get AM p) => [v1|];
    by case: (get m p) => [[v2 [? ? ?]]|].
  - repeat case: (p =P _) => _ //=; move=> [<- _ _ _ _ _ _]; by apply REF.
Qed.

Lemma supd_refine_syscall_addrs_b AM sst sst' p l :
  Sym.supd sst p l ?= sst' ->
  refine_syscall_addrs_b AM (Symbolic.mem sst) ->
  refine_syscall_addrs_b AM (Symbolic.mem sst').
Proof.
  move=> UPD /and3P [Ha /eqP [Hs1 Hs2 Hs3] Hu].
  apply/and3P.
  split=> // {Ha Hu}.
  by rewrite /syscall_addrs !map_cons
             (Sym.get_supd_none _ _ _ _ _ Hs1 UPD)
             (Sym.get_supd_none _ _ _ _ _ Hs2 UPD)
             (Sym.get_supd_none _ _ _ _ _ Hs3 UPD).
Qed.

Lemma sget_supd_good_internal (sst sst' : sstate) p c I1 W1 I2 W2 :
  (forall c', c' \in I2 :|: W2 -> (c' <? Sym.next_id (Symbolic.internal sst))) ->
  Sym.sget sst p ?= Sym.DATA c I1 W1 ->
  Sym.supd sst p (Sym.DATA c I2 W2) ?= sst' ->
  Sym.good_internal sst ->
  Sym.good_internal sst'.
Proof.
  case: sst => m r pc [? [? ? ?] [? ? ?] [? ? ?]];
  rewrite /Sym.sget /Sym.supd /Sym.good_internal /rep //=.
  case: sst' => m' r' pc' [? ? ? ?] /= OK.
  case GET: (get m p) => [[? tg]|].
  - move=> [Ht] /= [<- _ _ <- <- <- <-] [H1 [H2 [H3 H4]]].
    subst tg.
    do 3?split; trivial.
    move=> p' x c' I' W'.
    have [->|NE] := (p' =P p).
    + rewrite get_set_eq.
      move=> [_ <- <- <-].
      by apply H4 in GET; case: GET.
    + rewrite (get_set_neq _ _ NE).
      by apply H4.
  - repeat case: (p =P _) => ? //; move=> [<- ? ?] [<- ? ? <- <- <- <- H]; subst.
    + case: H => [NOTIN [NEXT [IWS WITH_GET]]].
      split; [|split; [|split; [|move => p x c' I' W' GET'; split]]];
        try done; try by apply WITH_GET in GET'; case: GET'.
      apply/forall_inP => /= x IN.
      move/forall_inP in IWS.
      rewrite !inE -!orbA in IN.
      repeat case/orP: IN => IN; try by apply IWS; rewrite !inE IN /= ?orbT.
      * by apply OK; rewrite inE IN.
      * by apply OK; rewrite inE IN orbT.
    + case: H => [NOTIN [NEXT [IWS WITH_GET]]].
      split; [|split; [|split; [|move => p x c' I' W' GET'; split]]];
        try done; try by apply WITH_GET in GET'; case: GET'.
      apply/forall_inP => /= x IN.
      move/forall_inP in IWS.
      rewrite !inE -!orbA in IN.
      repeat case/orP: IN => IN; try by apply IWS; rewrite !inE IN /= ?orbT.
      * by apply OK; rewrite inE IN.
      * by apply OK; rewrite inE IN orbT.
    + case: H => [NOTIN [NEXT [IWS WITH_GET]]].
      split; [|split; [|split; [|move => p x c' I' W' GET'; split]]];
        try done; try by apply WITH_GET in GET'; case: GET'.
      apply/forall_inP => /= x IN.
      move/forall_inP in IWS.
      rewrite !inE -!orbA in IN.
      repeat case/orP: IN => IN; try by apply IWS; rewrite !inE IN /= ?orbT.
      * by apply OK; rewrite inE IN.
      * by apply OK; rewrite inE IN orbT.
Qed.

Lemma sget_irrelevancies r' pc' m int r pc :
  Sym.sget (SState m r pc int) =
  Sym.sget (SState m r' pc' int).
Proof. reflexivity. Qed.

Lemma sget_next_irrelevant next' next m r pc iT aJT aST :
  Sym.sget (SState m r pc (SInternal next  iT aJT aST)) =
  Sym.sget (SState m r pc (SInternal next' iT aJT aST)).
Proof. reflexivity. Qed.

Lemma supd_tags_subsets sst sst' p c I1 W1 I2 W2 :
  Sym.sget sst p ?= Sym.DATA c I1 W1 ->
  Sym.supd sst p (Sym.DATA c I2 W2) ?= sst' ->
  I1 \subset I2 -> W1 \subset W2 ->
  tags_subsets sst sst'.
Proof.
  move=> GET UPD HI HW p'.
  have [{p'} -> //|NE] := altP (p' =P p).
  { by rewrite GET (Sym.sget_supd _ _ _ _ UPD) eqxx. }
  rewrite (Sym.sget_supd _ _ _ _ UPD) (negbTE NE).
  by case: (Sym.sget _ _) => [[]|] //=.
Qed.

Lemma tags_subsets_irrelevancies r' pc' m int r pc sst :
  tags_subsets sst (SState m r' pc' int) ->
  tags_subsets sst (SState m r pc int).
Proof.
  move=> H p.
  move: H => /(_ p).
  by rewrite (sget_irrelevancies r' pc').
Qed.

Lemma get_compartment_id_supd_same sst sst' p cid I1 W1 I2 W2 :
  Sym.sget sst p = Some (Sym.DATA cid I1 W1) ->
  Sym.supd sst p (Sym.DATA cid I2 W2) = Some sst' ->
  get_compartment_id sst =1 get_compartment_id sst'.
Proof.
  move=> GET UPD c.
  apply/eq_pick => c'.
  apply/f_equal2 => // {c'}.
  apply/eq_imset => p' /=.
  rewrite (Sym.sget_supd _ _ _ _ UPD).
  have [{p'} -> /=|//] := (p' =P p); by rewrite GET.
Qed.

Lemma get_compartment_id_irrelevancies r' pc' m int r pc :
  get_compartment_id (SState m r pc int) =1
  get_compartment_id (SState m r' pc' int).
Proof. by []. Qed.

Lemma get_compartment_id_irrelevancies' r' pc' next' m r pc next a b c :
  get_compartment_id (SState m r pc (Sym.Internal next a b c)) =
  get_compartment_id (SState m r' pc' (Sym.Internal next' a b c)).
Proof. by []. Qed.

Lemma unique_ids_replace sst sst' p pcid I1 I2 W1 W2 C A J1 J2 S1 S2 :
  unique_ids sst C ->
  Sym.sget sst p = Some (Sym.DATA pcid I1 W1) ->
  Sym.supd sst p (Sym.DATA pcid I2 W2) = Some sst' ->
  <<A,J1,S1>> \in C ->
  unique_ids sst' (<<A,J2,S2>> :: rem_all <<A,J1,S1>> C).
Proof.
  move=> UNIQUE GET UPD IN c1 c2.
  rewrite !in_cons !mem_filter.
  case/orP=> [/eqP -> {c1}|/andP [not_prev1 IN1]];
  case/orP=> [/eqP -> {c2}|/andP [not_prev2 IN2]] //.
  - rewrite -!(get_compartment_id_supd_same GET UPD) => /(UNIQUE _ _ IN IN2) E.
    by rewrite -E /= eqxx in not_prev2.
  - rewrite -!(get_compartment_id_supd_same GET UPD) => /(UNIQUE _ _ IN1 IN) E.
    by rewrite -E /= eqxx in not_prev1.
  - by rewrite -!(get_compartment_id_supd_same GET UPD) => /(UNIQUE _ _ IN1 IN2) E.
Qed.

Lemma well_formed_targets_augment (targets : Abs.compartment t -> {set word})
                                  (sources : data_tag -> {set word})
                                  sst sst' p pcid I1 I2 W1 W2 Ss C c cid c' :
  well_formed_targets targets sources sst C ->
  unique_ids sst C ->
  Sym.sget sst p = Some (Sym.DATA pcid I1 W1) ->
  Sym.supd sst p (Sym.DATA pcid I2 W2) = Some sst' ->
  get_compartment_id sst c = Some cid ->
  c \in C ->
  Abs.address_space c = Abs.address_space c' ->
  targets c' = p |: targets c ->
  sources (Sym.DATA pcid I2 W2) = cid |: Ss ->
  sources (Sym.DATA pcid I1 W1) = Ss ->
  well_formed_targets targets sources sst' (c' :: rem_all c C).
Proof.
  move=> WF UNIQUE GET UPD ID c_in_C AS TARGETS SOURCES2 SOURCES1  c'' cid''.
  rewrite in_cons mem_filter
          -(get_compartment_id_supd_same GET UPD)
          => /orP [/eqP ->|/= /andP [Hneq c''_in_C]] ID'.
  - have {cid'' ID'} ->: cid'' = cid.
    { rewrite /get_compartment_id ?AS in ID ID'.
      congruence. }
    rewrite TARGETS (WF _ _ c_in_C ID).
    apply/eqP. rewrite eqEsubset. apply/andP. split.
    + rewrite subUset sub1set in_set (Sym.sget_supd _ _ _ _ UPD)
              eqxx /= SOURCES2 /= in_setU1 eqxx /=.
      apply/subsetP => p'.
      rewrite !in_set (Sym.sget_supd _ _ _ _ UPD).
      have [{p'} -> /=|//] := (p' =P p).
      by rewrite SOURCES2 /= in_setU1 eqxx.
    + apply/subsetP => p'.
      rewrite !in_set (Sym.sget_supd _ _ _ _ UPD).
      by have [{p'} ->|] := (p' =P p).
  - rewrite (WF _ _ c''_in_C ID').
    apply/eqP. rewrite eqEsubset. apply/andP.
    split; apply/subsetP => p';
    rewrite !in_set
            (Sym.sget_supd _ _ _ _ UPD);
    have [{p'} ->|] //= := (p' =P p);
    rewrite SOURCES2 GET /= SOURCES1 /= in_setU1; first by rewrite orbC => ->.
    case/orP => [/eqP E|//].
    rewrite E -?ID{cid'' E} in ID' *.
    by rewrite (UNIQUE _ _ c''_in_C c_in_C ID') eqxx in Hneq.
Qed.

Lemma well_formed_targets_same (targets : Abs.compartment t -> {set word})
                               (sources : data_tag -> {set word})
                               sst sst' p pcid I1 I2 W1 W2 Ss C c cid c' :
  well_formed_targets targets sources sst C ->
  unique_ids sst C ->
  Sym.sget sst p = Some (Sym.DATA pcid I1 W1) ->
  Sym.supd sst p (Sym.DATA pcid I2 W2) = Some sst' ->
  get_compartment_id sst c = Some cid ->
  c \in C ->
  Abs.address_space c = Abs.address_space c' ->
  targets c' = targets c ->
  sources (Sym.DATA pcid I2 W2) = Ss ->
  sources (Sym.DATA pcid I1 W1) = Ss ->
  well_formed_targets targets sources sst' (c' :: rem_all c C).
Proof.
  move=> WF UNIQUE GET UPD ID c_in_C AS TARGETS SOURCES2 SOURCES1  c'' cid''.
  rewrite in_cons mem_filter
          -(get_compartment_id_supd_same GET UPD)
          => /orP [/eqP ->|/= /andP [Hneq c''_in_C]] ID'.
  - have {cid'' ID'} ->: cid'' = cid.
    { rewrite /get_compartment_id ?AS in ID ID'.
      congruence. }
    rewrite TARGETS (WF _ _ c_in_C ID).
    apply/eqP. rewrite eqEsubset. apply/andP. split.
    + apply/subsetP => p'.
      rewrite !in_set (Sym.sget_supd _ _ _ _ UPD).
      have [{p'} -> /=|//] := (p' =P p).
      by rewrite SOURCES2 GET /= SOURCES1 /=.
    + apply/subsetP => p'.
      rewrite !in_set (Sym.sget_supd _ _ _ _ UPD).
      have [{p'} ->/=|//] := (p' =P p).
      by rewrite SOURCES2 /= GET /= SOURCES1 /=.
  - rewrite (WF _ _ c''_in_C ID').
    apply/eqP. rewrite eqEsubset. apply/andP.
    by split; apply/subsetP => p';
    rewrite !in_set
            (Sym.sget_supd _ _ _ _ UPD);
    have [{p'} ->/=|//] := (p' =P p);
    rewrite SOURCES2 GET /= SOURCES1 /=.
Qed.

Lemma unique_ids_irrelevancies r' pc' m int r pc :
  unique_ids (SState m r pc int) =
  unique_ids (SState m r' pc' int).
Proof. by []. Qed.

Lemma well_formed_targets_irrelevancies r' pc' m int r pc targets sources :
  well_formed_targets targets sources (SState m r pc int) =
  well_formed_targets targets sources (SState m r' pc' int).
Proof. by []. Qed.

Theorem add_to_jump_targets_refined : forall ast sst sst',
  Abs.good_state ast ->
  refine ast sst ->
  Sym.add_to_jump_targets sst ?= sst' ->
  exists ast',
    Abs.semantics (Abs.add_to_jump_targets (t:=t)) ast ?= ast' /\
    refine ast' sst'.
Proof.
  move=> ast sst sst' AGOOD REFINE ADD.
  assert (SGOOD : Sym.good_state sst) by (eapply refine_good; eassumption).
  destruct REFINE as [RPC RREGS RMEMS COMPSWD IDSWD IDSU JTWF STWF RPREV RSC RINT],
           ast    as [Apc AR    AM    AC    Ask Aprev],
           sst    as [SM SR Spc [Snext SiT SaJT SaST]].
  generalize SGOOD; move=> [SGPC SGINT].
  case/and4P: (AGOOD) => AIN /andP [ANOL ACC] ASS ASP.
  rewrite /Abs.semantics /Abs.add_to_jump_targets
          /Abs.add_to_compartment_component
          (lock Abs.in_compartment_opt);
    simpl in *.
  rewrite /refine_pc_b in RPC.
  destruct Spc as [pc [F cid']]; try done; move/eqP in RPC; subst.

  move/id in ADD;
    undo1 ADD LI;
    undo1 ADD cid_sys;
    destruct LI as [cid I W]; try discriminate;
    undo1 ADD NEQ_cid_sys;
    undo2 ADD p Lp;
    undoDATA ADD x cid'' I'' W'';
    undo1 ADD OK;
    undo1 ADD s';
    undo2 ADD pc' Lpc';
    undoDATA ADD i' cid_next I_next W_next;
    undo1 ADD NEXT_EQ; move/eqP in NEXT_EQ; subst cid_next;
    undo1 ADD NEXT;
    destruct s' as [M_next R_next not_pc si_next];
    unoption.

  move: (COMPSWD pc).
  rewrite def_LI => /(_ erefl).
  case IN_c: (Abs.in_compartment_opt AC pc) => [c_sys|] _ //.
  move/Abs.in_compartment_opt_correct in IN_c.

  rewrite /Sym.can_execute /= in def_cid_sys.
  undo1 def_cid_sys COND; unoption.

  move: RPREV => /andP [/eqP ? /eqP RPREV]; subst.
  have -> /=: Abs.permitted_now_in AC F Aprev pc ?= c_sys.
  { rewrite /Abs.permitted_now_in
            (Abs.in_compartment_opt_sound _ _ _ ANOL IN_c) /=.
    rewrite eq_sym (negbTE NEQ_cid_sys) /= in COND.
    case/andP: COND => /eqP -> Hin.
    by rewrite eqxx /= (JTWF _ _ AIN RPREV) in_set def_LI /= Hin orbT. }

  have R_c_sys: get_compartment_id
                      (SState SM SR pc@(Sym.PC F cid')
                              (SInternal Snext SiT SaJT SaST))
                      c_sys
                    = Some cid_sys.
  { case/andP: IN_c => IN1 IN2.
    by rewrite (in_compartment_get_compartment_id COMPSWD IDSWD IDSU IN1 IN2) def_LI. }

  rewrite /Sym.good_pc_tag in SGPC; move: SGPC => [p' [I' [W' def_cid']]].

  assert (SYS_SEP : Aprev != c_sys). {
    apply/eqP; intro; subst.
    replace cid_sys with cid' in * by congruence.
    rewrite eq_refl in NEQ_cid_sys; discriminate.
  }
  rewrite SYS_SEP; simpl.

  move/(_ syscall_arg1): (RREGS).
  rewrite def_p_Lp.
  destruct (get AR syscall_arg1) as [Ap|]; destruct Lp; try done;
    move/eqP => ?; subst; simpl.

  destruct Aprev as [Aprev Jprev Sprev]; simpl.

  have IC_p': p' \in Aprev.
  { apply/(get_compartment_id_in_compartment COMPSWD IDSWD IDSU AIN).
    by rewrite def_cid'. }

  have ->: p \in Aprev :|: Jprev. {
    rewrite in_setU. apply/orP.
    case/orP: OK => [/eqP E|OK].
    - subst cid''. left.
      apply/(get_compartment_id_in_compartment COMPSWD IDSWD IDSU AIN).
      by rewrite RPREV def_xcIW.
    - right.
      have /= -> := JTWF _ _ AIN RPREV.
      by rewrite in_set def_xcIW.
  }

  move/(_ ra): (RREGS).
  rewrite def_pc'_Lpc'.
  destruct (get AR ra) as [Apc'|]; destruct Lpc'; try done;
    move/eqP => ?; subst Apc'; simpl.

  have IN_pc' : pc' \in Aprev.
  { apply/(get_compartment_id_in_compartment COMPSWD IDSWD IDSU AIN).
    have [E|NE] := (pc' =P p).
    - subst pc'.
      rewrite (Sym.sget_supd_eq _ _ _ _ def_s') in def_xcIW0.
      rewrite def_xcIW /=.
      congruence.
    - by rewrite -(Sym.sget_supd_neq _ _ _ _ _ NE def_s') def_xcIW0 /=. }

  rewrite -(lock _) /= IN_pc' /= eq_refl.

  have IN_Jsys : pc' \in Abs.jump_targets c_sys. {
    rewrite eq_sym (negbTE NEQ_cid_sys) /= in COND.
    case/andP: IN_c => IC_c _.
    rewrite (JTWF _ _ IC_c R_c_sys) in_set.
    have [E|NE] := (pc' =P p).
    - subst pc'.
      rewrite def_xcIW /=.
      rewrite (Sym.sget_supd _ _ _ _ def_s') eqxx in def_xcIW0.
      move: def_xcIW0 => [? ? ?]; subst cid'' I_next W_next.
      by rewrite (in_setU1 cid_sys) eq_sym (negbTE NEQ_cid_sys) /= in NEXT.
    - by rewrite -(Sym.sget_supd_neq _ _ _ _ _ NE def_s') def_xcIW0 /=.
  }

  rewrite IN_Jsys. eexists; split; [reflexivity|].
  have /= E := Sym.supd_preserves_regs _ _ _ _ def_s'.
  subst R_next.

  constructor => //=.
  - exact: (supd_refine_memory def_s' RMEMS).
  - move=> p''.
    rewrite (sget_irrelevancies SR not_pc).
    move=> /(Sym.sget_supd_inv _ _ _ _ _ def_s')/COMPSWD.
    by apply/in_compartment_update'.
  - move=> c''.
    rewrite  (get_compartment_id_irrelevancies SR not_pc)
            -(get_compartment_id_supd_same def_xcIW def_s')
             in_cons mem_filter => /orP [/eqP {c''} -> | /andP [_ Hc'']].
    + exact: (IDSWD _ AIN).
    + exact: (IDSWD _ Hc'').
  - rewrite (unique_ids_irrelevancies SR not_pc).
    apply/(unique_ids_replace IDSU def_xcIW def_s' AIN).
  - rewrite /well_formed_jump_targets
            (well_formed_targets_irrelevancies SR not_pc).
    apply/(well_formed_targets_augment JTWF IDSU def_xcIW def_s' RPREV AIN);
    try reflexivity.
  - rewrite /well_formed_store_targets
            (well_formed_targets_irrelevancies SR not_pc).
    apply/(well_formed_targets_same STWF IDSU def_xcIW def_s' RPREV AIN);
    try reflexivity.
  - by rewrite /refine_previous_b /=
               (get_compartment_id_irrelevancies SR not_pc)
              -(get_compartment_id_supd_same def_xcIW def_s')
               R_c_sys.
  - exact: (supd_refine_syscall_addrs_b def_s').
  - have in_range : forall c' : word_finType t,
                      c' \in (cid' |: I'') :|: W'' ->
                      c' <? Sym.next_id
                              (Symbolic.internal
                                 (SState SM SR
                                         pc@(Sym.PC F cid')
                                         (SInternal Snext SiT SaJT SaST))).
    {
      move=> c'; rewrite !inE -orbA => /= /or3P [/eqP->{c'} | IN_I'' | IN_W''].
      - rewrite /Sym.good_internal /= in SGINT.
        rewrite /Sym.sget /= in def_cid'.
        destruct SiT,SaJT,SaST; try by [].
        move: SGINT => [_ [/and4P [? ? ? _] [ALL GOOD]]].
        move: def_cid'; case GET: (get SM p') => [[]|] /=.
        + move=> []?; subst.
          apply GOOD in GET.
          by case: GET.
        + by repeat (case: (p' == _); first by move=> [] *; subst).
      - rewrite /Sym.good_internal /= in SGINT.
        rewrite /Sym.sget /= in def_xcIW.
        destruct SiT,SaJT,SaST; try by [].
        move: SGINT => [_ [/and4P [? ? ? _] [ALL GOOD]]].
        move: def_xcIW; case GET: (get SM p) => [[]|] /=.
        + move=> []?; subst.
          apply GOOD in GET.
          case: GET => [_ _ GOOD'].
          by apply GOOD'; rewrite inE IN_I''.
        + by repeat (case: (p == _);
                     first by move=> [] *; subst;
                              move/forall_inP in ALL; apply ALL;
                              rewrite !inE IN_I'' ?orbT).
      - rewrite /Sym.good_internal /= in SGINT.
        rewrite /Sym.sget /= in def_xcIW.
        destruct SiT,SaJT,SaST; try by [].
        move: SGINT => [_ [/and4P [? ? ? _] [ALL GOOD]]].
        move: def_xcIW; case GET: (get SM p) => [[]|] /=.
        + move=> []?; subst.
          apply GOOD in GET.
          case: GET => [_ _ GOOD'].
          by apply GOOD'; rewrite inE IN_W'' orbT.
        + by repeat (case: (p == _);
                     first by move=> [] *; subst;
                              move/forall_inP in ALL; apply ALL;
                              rewrite !inE IN_W'' ?orbT).
    }
    exact: (sget_supd_good_internal in_range def_xcIW def_s').
Qed.

Theorem add_to_store_targets_refined : forall ast sst sst',
  Abs.good_state ast ->
  refine ast sst ->
  Sym.add_to_store_targets sst ?= sst' ->
  exists ast',
    Abs.semantics (Abs.add_to_store_targets (t:=t)) ast ?= ast' /\
    refine ast' sst'.
Proof.
  move=> ast sst sst' AGOOD REFINE ADD.
  assert (SGOOD : Sym.good_state sst) by (eapply refine_good; eassumption).
  destruct REFINE as [RPC RREGS RMEMS COMPSWD IDSWD IDSU JTWF STWF RPREV RSC RINT],
           ast    as [Apc AR    AM    AC    Ask Aprev],
           sst    as [SM SR Spc [Snext SiT SaJT SaST]].
  generalize SGOOD; move=> [SGPC SGINT].
  case/and4P: (AGOOD) => AIN /andP [ANOL ACC] ASS ASP.
  rewrite /Abs.semantics /Abs.add_to_store_targets
          /Abs.add_to_compartment_component
          (lock Abs.in_compartment_opt);
    simpl in *.
  rewrite /refine_pc_b in RPC.
  destruct Spc as [pc [F cid']]; try done; move/eqP in RPC; subst.

  move/id in ADD;
    undo1 ADD LI;
    undo1 ADD cid_sys;
    destruct LI as [cid I W]; try discriminate;
    undo1 ADD NEQ_cid_sys;
    undo2 ADD p Lp;
    undoDATA ADD x cid'' I'' W'';
    undo1 ADD OK;
    undo1 ADD s';
    undo2 ADD pc' Lpc';
    undoDATA ADD i' cid_next I_next W_next;
    undo1 ADD NEXT_EQ; move/eqP in NEXT_EQ; subst cid_next;
    undo1 ADD NEXT;
    destruct s' as [M_next R_next not_pc si_next];
    unoption.

  move: (COMPSWD pc).
  rewrite def_LI => /(_ erefl).
  case IN_c: (Abs.in_compartment_opt AC pc) => [c_sys|] _ //.
  move/Abs.in_compartment_opt_correct in IN_c.

  rewrite /Sym.can_execute /= in def_cid_sys.
  undo1 def_cid_sys COND; unoption.

  move: RPREV => /andP [/eqP ? /eqP RPREV]; subst.
  have -> /=: Abs.permitted_now_in AC F Aprev pc ?= c_sys.
  { rewrite /Abs.permitted_now_in
            (Abs.in_compartment_opt_sound _ _ _ ANOL IN_c) /=.
    rewrite eq_sym (negbTE NEQ_cid_sys) /= in COND.
    case/andP: COND => /eqP -> Hin.
    by rewrite eqxx /= (JTWF _ _ AIN RPREV) in_set def_LI /= Hin orbT. }

  have R_c_sys: get_compartment_id
                      (SState SM SR pc@(Sym.PC F cid')
                              (SInternal Snext SiT SaJT SaST))
                      c_sys
                    = Some cid_sys.
  { case/andP: IN_c => IN1 IN2.
    by rewrite (in_compartment_get_compartment_id COMPSWD IDSWD IDSU IN1 IN2) def_LI. }

  rewrite /Sym.good_pc_tag in SGPC; move: SGPC => [p' [I' [W' def_cid']]].

  have -> /=: Aprev != c_sys. {
    apply/eqP; intro; subst.
    replace cid_sys with cid' in * by congruence.
    rewrite eq_refl in NEQ_cid_sys; discriminate.
  }

  move/(_ syscall_arg1): (RREGS).
  rewrite def_p_Lp.
  destruct (get AR syscall_arg1) as [Ap|]; destruct Lp; try done;
    move/eqP => ?; subst Ap; simpl.

  destruct Aprev as [Aprev Jprev Sprev]; simpl.

  have IC_p': p' \in Aprev.
  { apply/(get_compartment_id_in_compartment COMPSWD IDSWD IDSU AIN).
    by rewrite def_cid'. }

  have ->: p \in Aprev :|: Sprev. {
    rewrite in_setU. apply/orP.
    case/orP: OK => [/eqP E|OK].
    - subst cid''. left.
      apply/(get_compartment_id_in_compartment COMPSWD IDSWD IDSU AIN).
      by rewrite RPREV def_xcIW.
    - right.
      have /= -> := STWF _ _ AIN RPREV.
      by rewrite in_set def_xcIW.
  }

  move/(_ ra): (RREGS).
  rewrite def_pc'_Lpc'.
  destruct (get AR ra) as [Apc'|]; destruct Lpc'; try done;
    move/eqP=> ?; subst Apc'; simpl.

  have IN_pc' : pc' \in Aprev.
  { apply/(get_compartment_id_in_compartment COMPSWD IDSWD IDSU AIN).
    have [E|NE] := (pc' =P p).
    - subst pc'.
      rewrite (Sym.sget_supd_eq _ _ _ _ def_s') in def_xcIW0.
      rewrite def_xcIW /=.
      congruence.
    - by rewrite -(Sym.sget_supd_neq _ _ _ _ _ NE def_s') def_xcIW0 /=. }

  rewrite -(lock _) /= IN_pc' /= eq_refl.

  have IN_Jsys : pc' \in Abs.jump_targets c_sys. {
    rewrite eq_sym (negbTE NEQ_cid_sys) /= in COND.
    case/andP: IN_c => IC_c _.
    rewrite (JTWF _ _ IC_c R_c_sys) in_set.
    have [E|NE] := (pc' =P p).
    - subst pc'.
      rewrite def_xcIW /=.
      rewrite (Sym.sget_supd _ _ _ _ def_s') eqxx in def_xcIW0.
      by move: def_xcIW0 => [? ? ?]; subst cid'' I_next W_next.
    - by rewrite -(Sym.sget_supd_neq _ _ _ _ _ NE def_s') def_xcIW0 /=.
  }

  rewrite IN_Jsys. eexists; split; [reflexivity|].
  have /= E := Sym.supd_preserves_regs _ _ _ _ def_s'.
  subst R_next.

  constructor => //=.
  - exact: (supd_refine_memory def_s' RMEMS).
  - move=> p''.
    rewrite (sget_irrelevancies SR not_pc).
    move=> /(Sym.sget_supd_inv _ _ _ _ _ def_s')/COMPSWD.
    by apply/in_compartment_update'.
  - move=> c''.
    rewrite  (get_compartment_id_irrelevancies SR not_pc)
            -(get_compartment_id_supd_same def_xcIW def_s')
             in_cons mem_filter => /orP [/eqP {c''} -> | /andP [_ Hc'']].
    + exact: (IDSWD _ AIN).
    + exact: (IDSWD _ Hc'').
  - rewrite (unique_ids_irrelevancies SR not_pc).
    apply/(unique_ids_replace IDSU def_xcIW def_s' AIN).
  - rewrite /well_formed_jump_targets
            (well_formed_targets_irrelevancies SR not_pc).
    apply/(well_formed_targets_same JTWF IDSU def_xcIW def_s' RPREV AIN);
    try reflexivity.
  - rewrite /well_formed_store_targets
            (well_formed_targets_irrelevancies SR not_pc).
    apply/(well_formed_targets_augment STWF IDSU def_xcIW def_s' RPREV AIN);
    try reflexivity.
  - by rewrite /refine_previous_b /=
               (get_compartment_id_irrelevancies SR not_pc)
              -(get_compartment_id_supd_same def_xcIW def_s')
               R_c_sys.
  - exact: (supd_refine_syscall_addrs_b def_s').
  - have in_range : forall c' : word_finType t,
                      c' \in I'' :|: (cid' |: W'') ->
                      c' <? Sym.next_id
                              (Symbolic.internal
                                 (SState SM SR
                                         pc@(Sym.PC F cid')
                                         (SInternal Snext SiT SaJT SaST))).
    {
      move=> c'; rewrite !inE => /= /or3P [IN_I'' | /eqP->{c'} | IN_W''].
      - rewrite /Sym.good_internal /= in SGINT.
        rewrite /Sym.sget /= in def_xcIW.
        destruct SiT,SaJT,SaST; try by [].
        move: SGINT => [_ [/and4P [? ? ? _] [ALL GOOD]]].
        move: def_xcIW; case GET: (get SM p) => [[]|] /=.
        + move=> []?; subst.
          apply GOOD in GET.
          case: GET => [_ _ GOOD'].
          by apply GOOD'; rewrite inE IN_I''.
        + by repeat (case: (p == _);
                     first by move=> [] *; subst;
                              move/forall_inP in ALL; apply ALL;
                              rewrite !inE IN_I'' ?orbT).
      - rewrite /Sym.good_internal /= in SGINT.
        rewrite /Sym.sget /= in def_cid'.
        destruct SiT,SaJT,SaST; try by [].
        move: SGINT => [_ [/and4P [? ? ? _] [ALL GOOD]]].
        move: def_cid'; case GET: (get SM p') => [[]|] /=.
        + move=> []?; subst.
          apply GOOD in GET.
          by case: GET.
        + by repeat (case: (p' == _); first by move=> [] *; subst).
      - rewrite /Sym.good_internal /= in SGINT.
        rewrite /Sym.sget /= in def_xcIW.
        destruct SiT,SaJT,SaST; try by [].
        move: SGINT => [_ [/and4P [? ? ? _] [ALL GOOD]]].
        move: def_xcIW; case GET: (get SM p) => [[]|] /=.
        + move=> []?; subst.
          apply GOOD in GET.
          case: GET => [_ _ GOOD'].
          by apply GOOD'; rewrite inE IN_W'' orbT.
        + by repeat (case: (p == _);
                     first by move=> [] *; subst;
                              move/forall_inP in ALL; apply ALL;
                              rewrite !inE IN_W'' ?orbT).
    }
    exact: (sget_supd_good_internal in_range def_xcIW def_s').
Qed.

Lemma retag_set_get_compartment_id_disjoint ok retag (ps : {set word}) sst sst' c cid :
  Sym.retag_set ok retag (enum ps) sst = Some sst' ->
  [disjoint Abs.address_space c & ps] ->
  get_compartment_id sst c = Some cid ->
  get_compartment_id sst' c = Some cid.
Proof.
  rewrite /Sym.retag_set /Sym.retag_one.
  move=> Hretag /pred0P Hdis Hid.
  have {Hdis} Hdis: forall p, p \in Abs.address_space c -> p \notin enum ps.
  { move=> p Hin_c.
    apply/negP => Hin_ps.
    move: (Hdis p) => /=.
    by rewrite Hin_c -(mem_enum (mem ps)) Hin_ps. }
  elim: {ps} (enum ps) sst Hid Hretag Hdis => [|p ps IH] sst Hid /=; first congruence.
  case GET: (Sym.sget sst p) => [[cid' I' W']|] //=.
  case: (ok p cid' I' W') => //.
  case: (retag p cid' I' W') => [cid'' I'' W''] //.
  case UPD: (Sym.supd _ _ _) => [sst''|] //= Hretag Hdis.
  apply (IH sst'') => //.
  - move: Hid.
    rewrite /get_compartment_id.
    case: pickP => [cid''' /eqP Hcid'''|] // [E].
    subst cid'''.
    move: (set11 (Some cid)).
    rewrite -Hcid''' => /imsetP [p' H1 H2].
    suff ->: [set (omap Sym.data_tag_compartment \o @Sym.sget _ cmp_syscalls sst'') x | x in Abs.address_space c] =
             [set (omap Sym.data_tag_compartment \o @Sym.sget _ cmp_syscalls sst) x | x in Abs.address_space c].
    { rewrite Hcid'''.
      case: pickP => [cid''' /eqP/set1_inj H//|/(_ cid) contra].
      by rewrite eqxx in contra. }
    apply/eq_in_imset => pp /(Hdis _).
    rewrite in_cons /= => /norP [pp_n_p pp_notin_ps].
    by rewrite (Sym.sget_supd _ _ _ _ UPD) (negbTE pp_n_p).
  - move=> pp Hin.
    by case/norP: (Hdis pp Hin).
Qed.

Lemma get_compartment_id_subset sst c c' cid p :
  p \in Abs.address_space c' ->
  Abs.address_space c' \subset Abs.address_space c ->
  get_compartment_id sst c = Some cid ->
  get_compartment_id sst c' = Some cid.
Proof.
  move=> Hp Hsub.
  rewrite /get_compartment_id.
  case: pickP => [cid' /eqP Hcid|] // [E].
  subst cid'.
  suff ->: [set (omap Sym.data_tag_compartment \o @Sym.sget _ cmp_syscalls sst) x | x in Abs.address_space c'] =
           [set (omap Sym.data_tag_compartment \o @Sym.sget _ cmp_syscalls sst) x | x in Abs.address_space c].
  { rewrite Hcid.
    case: pickP => [cid''' /eqP/set1_inj H//|/(_ cid) contra].
    by rewrite eqxx in contra. }
  apply/eqP. rewrite eqEsubset.
  rewrite imsetS //= Hcid sub1set.
  apply/imsetP.
  exists p => //.
  apply/eqP. rewrite eq_sym -in_set1 -Hcid.
  apply/imsetP.
  exists p => //.
  move/subsetP: Hsub.
  by apply.
Qed.

Lemma retag_set_get_compartment_id_same_ids ok retag ps sst sst' c cid :
  Sym.retag_set ok retag ps sst = Some sst' ->
  (forall p c I1 W1, Sym.data_tag_compartment (retag p c I1 W1) = c) ->
  get_compartment_id sst c = Some cid ->
  get_compartment_id sst' c = Some cid.
Proof.
  rewrite /Sym.retag_set /Sym.retag_one.
  move=> Hretag_set Hretag.
  elim: ps sst Hretag_set => [|p ps IH] sst //=; first congruence.
  case GET: (Sym.sget _ _) => [[cid1 I1 W1]|] //=.
  case: (ok _ _ _ _) => //.
  move: Hretag => /(_ p cid1 I1 W1).
  case RETAG: (retag _ _ _ _) => [cid2 I2 W2] //= E.
  subst cid2.
  case UPD: (Sym.supd _ _ _) => [sst''|] //= Hretag_set Hcid.
  suff : get_compartment_id sst'' c = Some cid by apply IH.
  move: (Hcid).
  rewrite /get_compartment_id.
  case: pickP => [cid' /eqP Hcid1|]//= [E].
  subst cid'.
  suff -> : [set (omap Sym.data_tag_compartment \o @Sym.sget _ cmp_syscalls sst'') x | x in Abs.address_space c] =
            [set (omap Sym.data_tag_compartment \o @Sym.sget _ cmp_syscalls sst) x | x in Abs.address_space c].
  { apply Hcid. }
  apply/eq_in_imset => p' /= p'_in.
  rewrite (Sym.sget_supd _ _ _ _ UPD).
  have [-> //=|//] := (p' =P p).
  by rewrite GET.
Qed.

Lemma retag_set_get_compartment_id_new_id ok retag sst sst' c cid :
  Sym.retag_set ok retag (enum (Abs.address_space c)) sst = Some sst' ->
  Abs.address_space c != set0 ->
  (forall p c I1 W1, Sym.data_tag_compartment (retag p c I1 W1) = cid) ->
  get_compartment_id sst' c = Some cid.
Proof.
  case: c => [Aprev Jprev Sprev] /= Hretag_set not0 Hretag.
  have AprevP : Aprev = [set p in enum Aprev].
  { apply/setP => p.
    by rewrite in_set (mem_enum (mem Aprev)). }
  rewrite AprevP {AprevP} in not0 *.
  move: {Aprev} (enum Aprev) Hretag_set not0 => [|p ps] Hretag_set not0.
  { by rewrite eqxx in not0. }

  move=> {not0}.

  have {sst Hretag_set} [sst Hretag_set Hstart]:
    exists2 sst, Sym.retag_set ok retag ps sst = Some sst' &
                 get_compartment_id sst <<[set p],Jprev,Sprev>> = Some cid.
  { move: Hretag_set => /=.
    rewrite /Sym.retag_set /Sym.retag_one /=.
    case GET1: (Sym.sget sst p) => [[cid1 I1 W1]|] //=.
    case: (ok p cid1 I1 W1) => //.
    move: (Hretag p cid1 I1 W1).
    case: (retag _ _ _ _) => [cid1' I1' W1'] //= [E].
    subst cid1'.
    case UPD1: (Sym.supd sst p (Sym.DATA cid I1' W1')) => [sst''|] //=.
    eexists; eauto.
    rewrite /get_compartment_id /= imset_set1 /=
            (Sym.sget_supd _ _ _ _ UPD1) eqxx /=.
    case: pickP => [x /eqP/set1_inj Hx|/(_ cid) contra]; first by apply esym.
    by rewrite eqxx in contra. }

  suff  {Hstart Hretag_set} H: forall (ps ps' : seq word) sst,
            @Sym.retag_set _ cmp_syscalls ok retag ps sst = Some sst' ->
            get_compartment_id sst <<[set p : word in ps'],Jprev,Sprev>> = Some cid ->
            get_compartment_id sst' <<[set p : word in ps'] :|: [set p : word in ps],Jprev,Sprev>> = Some cid.
  { move: (H ps [:: p] _ Hretag_set).
    rewrite !set_cons setU0. by apply. }

  rewrite /Sym.retag_set /Sym.retag_one.
  elim=> {p ps sst} [|p ps IH] ps' sst /=.
  { have -> : [set p : word in [::]] = set0 by [].
    rewrite setU0.
    congruence. }
  case GET: (Sym.sget sst p) => [[ cid' I' W']|] //=.
  case: (ok p cid' I' W') => //.
  move: (Hretag p cid' I' W').
  case: (retag _ _ _ _) => [cid'' I'' W''] //= [E].
  subst cid''.
  case UPD: (Sym.supd _ _ _) => [sst''|] //= Hretag_set Hcid.
  rewrite set_cons setUA (setUC _ [set p]) -set_cons.
  apply (IH _ sst'') => //.
  move: Hcid.
  rewrite /get_compartment_id.
  case: pickP => /= [cid'' /eqP E|] //= [?].
  subst cid''.
  rewrite set_cons imsetU1 /= (Sym.sget_supd _ _ _ _ UPD) eqxx /=.
  suff -> : [set (do!X <- @Sym.sget _ cmp_syscalls sst'' x; Some (Sym.data_tag_compartment X)) | x in [set x : word in ps']] =
            [set (do!X <- @Sym.sget _ cmp_syscalls sst x; Some (Sym.data_tag_compartment X)) | x in [set x : word in ps']].
  { rewrite E setUid.
    case: pickP => [cid''' /eqP/set1_inj H//|/(_ cid) contra].
    by rewrite eqxx in contra. }
  apply/eq_in_imset => p'.
  rewrite (Sym.sget_supd _ _ _ _ UPD).
  have [{p'} ->//=|//] := (p' =P p).
  move => Hin.
  apply/esym/eqP.
  rewrite -(in_set1 _ (Some cid)) -E.
  apply/imsetP.
  eexists; eauto.
Qed.

Lemma bounded_tags sst p c c' II WW :
  Sym.good_internal sst ->
  Sym.sget sst p = Some (Sym.DATA c II WW) ->
  c' \in II :|: WW ->
  c' <? (Sym.next_id (Symbolic.internal sst)).
Proof.
  destruct sst.
  destruct internal.
  rewrite /Sym.good_internal.
  destruct isolate_tag, add_to_jump_targets_tag, add_to_store_targets_tag => //=.
  case=> _ [_ [/forall_inP G1 G2]].
  rewrite /Sym.sget.
  case E: (get mem p) => [[v tg]|].
  { move => [?]. subst tg.
    move: (G2 p _ _ _ _ E) => [_ G3].
    eauto. }
  have [EE|NEE] := (p =P isolate_addr).
  { rewrite /=.
    move => [? ? ?] H. subst.
    apply G1.
    by rewrite 4!in_setU H. }
  have [EE|_] := (p =P add_to_jump_targets_addr).
  { rewrite /=.
    move => [? ? ?] H. subst.
    apply G1.
    by rewrite -(setUA _ _ WW) 3!in_setU H !orbT. }
  have [_|//=] := (p =P add_to_store_targets_addr).
  { rewrite /=.
    move => [? ? ?] H. subst.
    apply G1.
    by rewrite -(setUA _ _ WW) 3!in_setU H !orbT. }
Qed.

Theorem isolate_refined : forall ast sst sst',
  Abs.pc ast = isolate_addr ->
  Abs.good_state ast ->
  refine ast sst ->
  Sym.isolate sst ?= sst' ->
  exists ast',
    Abs.isolate_fn ast ?= ast' /\
    refine ast' sst'.
Proof.
  move=> ast sst sst' IS_ISOLATE AGOOD REFINE ISOLATE;
    rewrite (lock eq) in IS_ISOLATE.
  have [SGPC SGINT] : Sym.good_state sst by eapply refine_good; eassumption.
  destruct REFINE as [RPC RREGS RMEMS COMPSWD IDSWD IDSU JTWF STWF RPREV RSC RINT],
           ast    as [Apc AR    AM    AC    Ask Aprev],
           sst    as [SM SR Spc [Snext SiT SaJT SaST]].
  case/and4P: (AGOOD) => AIN /andP [ANOL ACC] ASS ASP.
  rewrite /Abs.semantics /Abs.isolate /Abs.isolate_fn
          (lock Abs.in_compartment_opt);
    simpl in *.

  rewrite /refine_pc_b in RPC.
  destruct Spc as [pc [F cid]]; try done; move/eqP in RPC; subst.

  move/id in ISOLATE;
    undo1 ISOLATE LI;
    undo1 ISOLATE cid_sys;
    destruct LI as [cid' I_sys W_sys]; try discriminate;
    rewrite /Sym.can_execute /= in def_cid_sys;
    generalize def_cid_sys => TEMP; rewrite (lock orb) in def_cid_sys;
      undo1 TEMP COND_sys; move: TEMP => [?]; subst cid';
      rewrite -(lock orb) in def_cid_sys;
    undo2 ISOLATE c' si';
    undo2 ISOLATE pA LpA; undo2 ISOLATE pJ LpJ; undo2 ISOLATE pS LpS;
    undo1 ISOLATE A'; undo1 ISOLATE NE_A'; undo1 ISOLATE sA;
    undo1 ISOLATE J'; undo1 ISOLATE sJ;
    undo1 ISOLATE S'; undo1 ISOLATE sS;
    undo2 ISOLATE pc' Lpc';
    undoDATA ISOLATE i' cid_next I_next W_next;
    undo1 ISOLATE NEXT_EQ; move/eqP in NEXT_EQ; subst cid_next;
    undo1 ISOLATE NEXT;
    destruct sS as [MS RS pcS siS];
    unoption.

  move: (COMPSWD pc).
  rewrite def_LI => /(_ erefl).
  case IN_c: (Abs.in_compartment_opt AC pc) => [c_sys|] _ //.
  case/Abs.in_compartment_opt_correct/andP: (IN_c) => c_sys_in_AC pc_in_c_sys {COND_sys}.

  undo1 def_cid_sys COND; unoption.

  repeat (erewrite refined_reg_value; [|eassumption]).
  rewrite def_pA_LpA def_pJ_LpJ def_pS_LpS def_pc'_Lpc' /=.

  move: RPREV => /andP [/eqP ? /eqP RPREV]; subst Ask.
  have -> /=: Abs.permitted_now_in AC F Aprev pc ?= c_sys.
  { rewrite /Abs.permitted_now_in IN_c /=.
    case/orP: COND => [/eqP E| /andP [/eqP E cid_in_I_sys]].
    - subst cid_sys.
      suff ->: c_sys = Aprev by rewrite eqxx.
      apply/(IDSU _ _ c_sys_in_AC AIN).
      by rewrite RPREV
                 (in_compartment_get_compartment_id COMPSWD IDSWD IDSU c_sys_in_AC pc_in_c_sys)
                 def_LI.
    - by rewrite E {E} eqxx /= (JTWF _ _ AIN RPREV) in_set def_LI /= cid_in_I_sys orbT. }

  destruct Aprev as [Aprev Jprev Sprev].

  repeat (erewrite isolate_create_set_refined; [|eassumption]).
  rewrite def_A' def_J' def_S' /= NE_A' /=.

  assert (SGINT' : Sym.good_internal (SState SM SR pc@(Sym.PC F cid) si')). {
    fold (Sym.fresh (SInternal Snext SiT SaJT SaST)) in def_c'_si'.
    eapply Sym.fresh_preserves_good in def_c'_si'; eassumption.
  }
  rewrite /Sym.good_pc_tag in SGPC; move: SGPC => [p [I [W def_cid]]].
  destruct (Snext == max_word t) eqn:SMALL_Snext; move/eqP in SMALL_Snext;
    inversion def_c'_si'; subst c' si'; clear def_c'_si'.

  have SUBSET_A' : A' \subset Aprev. {
    apply/subsetP; intros a IN.
    have := (Sym.retag_set_forall _ _ _ _ _ (enum_uniq (mem A')) def_sA a).
    rewrite (mem_enum (mem A')) IN => /(_ erefl).
    move=> /= [c' [I' [W' [SGET /eqP OK]]]]; subst c'.
    apply/(get_compartment_id_in_compartment COMPSWD IDSWD IDSU AIN).
    rewrite /Sym.sget /= in SGET *.
    by rewrite SGET.
  }
  rewrite SUBSET_A'.

  have IN_A' : forall a I' W',
                    Sym.sget sA a ?= Sym.DATA Snext I' W' ->
                    a \in A'. {
    intros until 0; intros SGET.
    have [// | NIN] := boolP (a \in A').
    have := (Sym.retag_set_not_in _ _ _ _ _ def_sA a).
    rewrite (mem_enum (mem A')) NIN => /(_ erefl) SGET'.
    rewrite -SGET' in SGET.
    eapply Sym.sget_lt_next in RINT; [simpl in RINT | exact: SGET].
    by rewrite ltb_irrefl in RINT.
  }

  have SUBSET_J' : J' \subset Aprev :|: Jprev. {
    apply/subsetP; move=> a IN.
    rewrite in_setU. apply/orP.
    generalize def_sA => def_sA';
      apply @Sym.retag_set_or with (p := a) in def_sA'; try assumption.
    have := Sym.retag_set_forall _ _ _ _ _ (enum_uniq (mem J')) def_sJ a.
    rewrite (mem_enum (mem J')) IN => /(_ erefl) /= [c' [I' [W' [SGET /orP [/orP [/eqP? | /eqP?] | ELEM]]]]];
      [subst c'; left | subst c'; left | right].
   - have := Sym.retag_set_in _ _ _ _ _ (enum_uniq (mem J')) def_sJ a.
     rewrite (mem_enum (mem J')) IN => /(_ erefl) [? [? [? [/esym EQ NOW]]]]; move: EQ => [] *; subst.
     rewrite SGET in def_sA'; move: def_sA' => [OLD | NEW].
     + apply/(get_compartment_id_in_compartment COMPSWD IDSWD IDSU AIN).
       rewrite /Sym.sget in OLD *.
       by rewrite OLD /=.
     + move: NEW => [cnew [Inew [Wnew [NEW /esym[]]]]] *; subst.
       move/id in SGET. apply IN_A' in SGET.
       move/subsetP in SUBSET_A'; auto.
   - apply IN_A' in SGET.
     move/subsetP in SUBSET_A'; auto.
   - case: def_sA' => [OLD | NEW].
     + have /= -> := JTWF _ _ AIN RPREV.
       rewrite in_set.
       rewrite {1}/Sym.sget /= in OLD.
       by rewrite /Sym.sget OLD SGET.
     + move: NEW => [cnew [Inew [Wnew [NEW SGET']]]] *; subst.
       rewrite SGET in SGET'.
       move: SGET' SGET NEW => [-> <- <-] {c' Inew Wnew} SGET NEW.
       have /= -> := JTWF _ _ AIN RPREV.
       rewrite in_set.
       rewrite /Sym.sget /= in NEW *.
       by rewrite NEW.
   - by apply (enum_uniq (mem A')).
  }
  rewrite SUBSET_J'.

  have IN_A'_sJ : forall a I' W',
                      Sym.sget sJ a ?= Sym.DATA Snext I' W' ->
                      a \in A'. {
    intros until 0; intros SGET.
    apply @Sym.retag_set_or with (p := a) in def_sJ; try assumption.
    rewrite SGET in def_sJ.
    destruct def_sJ as [OLD | NEW].
    - by apply IN_A' in OLD.
    - move: NEW => [cnew [Inew [Wnew [SGET' /esym[]]]]] *; subst.
      by apply IN_A' in SGET'.
    - by apply (enum_uniq (mem J')).
  }

  have SUBSET_S' : S' \subset Aprev :|: Sprev. {
    apply/subsetP; move=> a IN.
    rewrite in_setU. apply/orP.
    generalize def_sA => def_sA';
      apply @Sym.retag_set_or with (p := a) in def_sA'; try assumption.
    generalize def_sJ => def_sJ';
      apply @Sym.retag_set_or with (p := a) in def_sJ'; try assumption.
    set scompartment := fun sst =>
      do! DATA c _ _ <- Sym.sget sst a;
      Some c.
    assert (COMPARTMENT :
                 scompartment (SState SM SR pc@(Sym.PC F cid)
                                      (SInternal (Snext + 1)%w SiT SaJT SaST))
                   = scompartment sJ
              \/ a \in A'). {
      subst scompartment; simpl.
      destruct def_sJ' as [OLD | NEW].
      - rewrite -OLD.
        destruct def_sA' as [OLD' | NEW'].
        + rewrite OLD'.
          by left.
        + move: NEW' => [? [? [? [_ NEW']]]].
          rewrite NEW' /=.
          apply IN_A' in NEW'.
          by right.
      - destruct NEW as [? [? [? [SGET_sA SGET_sJ]]]].
        rewrite SGET_sJ /=.
        destruct def_sA' as [OLD' | NEW'].
        + rewrite OLD' SGET_sA /=.
          by left.
        + move: NEW' => [? [? [? [_ NEW']]]].
          rewrite NEW' in SGET_sA.
          inversion SGET_sA; subst.
          apply IN_A' in NEW'.
          by right.
    }
    move/subsetP in SUBSET_A'.
    subst scompartment; simpl in *.
    have := Sym.retag_set_forall _ _ _ _ _ (enum_uniq (mem S')) def_sS a.
    rewrite (mem_enum (mem S')) IN => /(_ erefl) /= [c' [I' [W' [SGET /orP [/orP [/eqP? | /eqP?] | ELEM]]]]];
      [subst c'; left | subst c'; left | ].
   - rewrite SGET /= in COMPARTMENT.
     move: COMPARTMENT => [OLD | DONE]; auto.
     undoDATA OLD xold cold Iold Wold.
     move: OLD => [] /esym?; subst.
     apply/(get_compartment_id_in_compartment COMPSWD IDSWD IDSU AIN).
     rewrite /Sym.sget in def_xcIW0 *.
     by rewrite def_xcIW0.
   - apply IN_A'_sJ in SGET; auto.
   - assert (SAME_W : forall c I W c' I' W',
                        Sym.sget
                          (SState SM SR pc@(Sym.PC F cid)
                                  (SInternal (Snext + 1)%w SiT SaJT SaST))
                          a ?= Sym.DATA c I W ->
                        Sym.sget sJ a ?= Sym.DATA c' I' W' ->
                        W' = W). {
       intros; repeat invh or; repeat invh ex; repeat invh and; congruence.
     }
     rewrite SGET /= in COMPARTMENT.
     move: COMPARTMENT => [OLD | DONE]; auto.
     undoDATA OLD xold cold Iold Wold.
     move: OLD => [] /esym?; subst.
     assert (W' = Wold). {
       destruct def_sJ' as [OLD | NEW].
       - rewrite OLD in def_sA'.
         destruct def_sA' as [OLD' | NEW'].
         + rewrite -OLD' in SGET.
           by move: SGET => [].
         + move: NEW' => [? [? [? [_ NEW']]]].
           rewrite NEW' in SGET; move: SGET => [] *; subst.
           eapply SAME_W; eauto 1.
       - destruct NEW as [? [? [? [SGET_sA SGET_sJ]]]].
         rewrite SGET_sJ /= in SGET.
         move: SGET => [] *; subst.
         destruct def_sA' as [OLD' | NEW'].
         + rewrite -OLD' in SGET_sA.
           by move: SGET_sA => [].
         + move: NEW' => [? [? [? [_ NEW']]]].
           rewrite NEW' in SGET_sA; move: SGET_sA => [] *; subst.
           eapply SAME_W; eauto 1.
     }
     right.
     have /= -> := STWF _ _ AIN RPREV.
     rewrite in_set.
     rewrite /Sym.sget /= in def_xcIW0 *.
     rewrite def_xcIW0 /=.
     by subst Wold.
   - exact: enum_uniq (mem J').
   - exact: enum_uniq (mem A').
  }
  rewrite SUBSET_S'.

  have COMPARTMENTS :
        forall p,
          match
            Sym.sget (SState SM SR pc@(Sym.PC F cid)
                             (SInternal Snext SiT SaJT SaST))
                     p
            ,
            Sym.sget (SState MS RS pc'@(Sym.PC JUMPED cid_sys) siS)
                     p
          with
            | Some (Sym.DATA cid1 _ _) , Some (Sym.DATA cid2 _ _) =>
              cid1 = cid2 \/ (cid1 = cid /\ cid2 = Snext)
            | None , None =>
              True
            | _ , _ =>
              False
          end. {
    intros a.
    rewrite -[Sym.sget _ _]/(Sym.sget (SState SM SR pc@(Sym.PC F cid)
                                              (SInternal (Snext + 1)%w SiT SaJT SaST))
                                      a)
            -[Sym.sget (SState MS _ _ _) _]/(Sym.sget (SState MS RS pcS siS) a).
    let cleanup X := try first [assumption | exact (enum_uniq (mem X))]
    in generalize def_sA => def_sA';
        apply @Sym.retag_set_or_ok with (p := a) in def_sA'; cleanup A';
       generalize def_sJ => def_sJ';
        apply @Sym.retag_set_or with (p := a) in def_sJ'; cleanup J';
      generalize def_sS => def_sS';
        apply @Sym.retag_set_or with (p := a) in def_sS'; cleanup S'.
    idtac;
      case: def_sA' => [OLD_A | [cA [IA [WA [THEN_A [OK_A NOW_A]]]]]];
      case: def_sJ' => [OLD_J | [cJ [IJ [WJ [THEN_J NOW_J]]]]];
      case: def_sS' => [OLD_S | [cS [IS [WS [THEN_S NOW_S]]]]];
      try move/eqP in OK_A; subst;
      first [move/id in OLD_A | move/id in THEN_A; move/id in NOW_A];
      first [move/id in OLD_J | move/id in THEN_J; move/id in NOW_J];
      first [move/id in OLD_S | move/id in THEN_S; move/id in NOW_S].
    - rewrite OLD_A OLD_J OLD_S.
      by case: (Sym.sget _ a) => [[]|]; auto.
    - by rewrite OLD_A OLD_J THEN_S NOW_S; left.
    - by rewrite OLD_A THEN_J -OLD_S NOW_J; left.
    - rewrite OLD_A THEN_J NOW_S.
      rewrite THEN_S in NOW_J.
      by inversion NOW_J; subst; left.
    - rewrite THEN_A -OLD_S -OLD_J NOW_A.
      by right.
    - rewrite THEN_A NOW_S.
      rewrite NOW_A THEN_S in OLD_J.
      by inversion OLD_J; subst; right.
    - rewrite THEN_A -OLD_S NOW_J.
      rewrite NOW_A in THEN_J.
      by inversion THEN_J; subst; right.
    - rewrite THEN_A NOW_S.
      rewrite NOW_A in THEN_J.
      rewrite THEN_S in NOW_J.
      by inversion THEN_J; inversion NOW_J; subst; right.
  }

  have IN_pc' : pc' \in Aprev.
  { apply/(get_compartment_id_in_compartment COMPSWD IDSWD IDSU AIN).
    move/(_ pc') in COMPARTMENTS.
    rewrite /Sym.sget /= in def_xcIW.
    rewrite {2 3}/Sym.sget /= def_xcIW in COMPARTMENTS.
    case SGET: (Sym.sget _ _) COMPARTMENTS => [[cpc' Ipc' Wpc']|] //=.
    rewrite RPREV.
    by intuition congruence. }

  have DIFF : cid <> Snext. {
    intros ?; subst.
    eapply Sym.sget_lt_next in RINT; [simpl in RINT | eassumption].
    by rewrite ltb_irrefl in RINT.
  }

  have DIFF_sys : cid_sys <> Snext. {
    intros ?; subst.
    eapply Sym.sget_lt_next in RINT; [simpl in RINT | eassumption].
    by rewrite ltb_irrefl in RINT.
  }

  have NIN : pc' \notin A'. {
    apply/negP => IN.
    have := Sym.retag_set_in_ok _ _ _ _ _ (enum_uniq (mem A')) def_sA pc'.
    rewrite (mem_enum (mem A')) => /(_ IN) [cpc' [Ipc' [Wpc' [THEN [OK NOW]]]]].
    move/eqP in OK; subst cpc'.
    move/id in def_xcIW.
    have := Sym.retag_set_or _ _ _ _ _ (enum_uniq (mem S')) def_sS pc'.
    have := Sym.retag_set_or _ _ _ _ _ (enum_uniq (mem J')) def_sJ pc'.
    case=> [OLD_J | [cJ [IJ [WJ [THEN_J NOW_J]]]]];
    case=> [OLD_S | [cS [IS [WS [THEN_S NOW_S]]]]];
      first [move/id in OLD_J | move/id in THEN_J; move/id in NOW_J];
      first [move/id in OLD_S | move/id in THEN_S; move/id in NOW_S].
    - rewrite -OLD_J NOW def_xcIW in OLD_S.
      abstract congruence.
    - rewrite -OLD_J NOW in THEN_S.
      rewrite def_xcIW in NOW_S.
      abstract congruence.
    - rewrite NOW_J def_xcIW in OLD_S.
      rewrite NOW in THEN_J.
      abstract congruence.
    - rewrite def_xcIW in NOW_S.
      rewrite NOW in THEN_J.
      abstract congruence.
  }

  rewrite -(lock _) /= in_setD IN_pc' NIN /= eqxx.

  have c_sys_id : get_compartment_id (SState SM SR pc@(Sym.PC F cid)
                                             (SInternal Snext SiT SaJT SaST)) c_sys = Some cid_sys.
  { by rewrite (in_compartment_get_compartment_id COMPSWD IDSWD IDSU c_sys_in_AC pc_in_c_sys)
               def_LI. }

  have IN_Jsys : pc' \in Abs.jump_targets c_sys. {
    have /= -> := JTWF _ cid_sys c_sys_in_AC c_sys_id.
    rewrite in_set.
    move/(_ pc'): COMPARTMENTS.
    rewrite (sget_irrelevancies RS pcS MS) def_xcIW.
    case SGET': (Sym.sget _ _) => [[cpc' Ipc' Wpc']|] //= Hcpc'.
    have {Hcpc'} Hcpc': cpc' = cid by clear -Hcpc'; abstract tauto.
    rewrite Hcpc' {Hcpc' cpc'} in SGET'.
    let cleanup X := try first [assumption | exact (enum_uniq (mem X))]
    in generalize def_sA => def_sA';
         apply @Sym.retag_set_or with (p := pc') in def_sA'; cleanup A';
       generalize def_sJ => def_sJ';
         apply @Sym.retag_set_or with (p := pc') in def_sJ'; cleanup J';
       generalize def_sS => def_sS';
         apply @Sym.retag_set_or with (p := pc') in def_sS'; cleanup S'.
    idtac;
      destruct def_sA' as [OLD_A | [cA [IA [WA [THEN_A NOW_A]]]]];
      destruct def_sJ' as [OLD_J | [cJ [IJ [WJ [THEN_J NOW_J]]]]];
      destruct def_sS' as [OLD_S | [cS [IS [WS [THEN_S NOW_S]]]]];
      try move/eqP in OK_A; subst;
      first [move/id in OLD_A | move/id in THEN_A; move/id in NOW_A];
      first [move/id in OLD_J | move/id in THEN_J; move/id in NOW_J];
      first [move/id in OLD_S | move/id in THEN_S; move/id in NOW_S];
      move/id in def_xcIW;
      try abstract congruence.
    - rewrite (sget_next_irrelevant (Snext+1)%w)
              OLD_A OLD_J OLD_S def_xcIW
        in SGET'.
      by case: SGET' => <- _.
    - rewrite (sget_next_irrelevant (Snext+1)%w) OLD_A OLD_J THEN_S in SGET'.
      rewrite NOW_S in def_xcIW.
      case: SGET'; case: def_xcIW => *; subst.
      by subst. (* Yeah, `subst` needs to happen again.  It's weird. *)
    - rewrite (sget_next_irrelevant (Snext+1)%w) OLD_A THEN_J in SGET'.
      rewrite -OLD_S NOW_J in def_xcIW.
      case: SGET'; case: def_xcIW => *; subst.
      rewrite inE in_set1 in NEXT.
      by case/orP: NEXT => [/eqP?|].
    - rewrite (sget_next_irrelevant (Snext+1)%w) OLD_A THEN_J in SGET'.
      rewrite NOW_S in def_xcIW.
      rewrite NOW_J in THEN_S.
      case: SGET'; case: def_xcIW; case: THEN_S => *; subst.
      subst. (* Again, for some reason `subst` needs to happen an extra time. *)
      rewrite inE in_set1 in NEXT.
      by case/orP: NEXT => [/eqP?|].
  }

  rewrite IN_Jsys.

  eexists; split; [reflexivity|].

  (* Some useful lemmas *)

  move: (RSC) => /and3P; rewrite {1 2}/syscall_addrs.
  move => [ /eqP [] ANGET_i ANGET_aJ ANGET_aS
            /eqP [] SNGET_i SNGET_aJ SNGET_aS
            RSCU ].
  move: (RSCU);
    rewrite /= !inE negb_or -!andbA => /and4P[] NEQiaJ NEQiaS NEQaJaS _.

  have NIN_any : forall a, get AM a = None -> a \notin A'. {
    move=> a ANGET; apply/negP; move=> IN.
    move: ASS => /forallb_forall/(_ _ (elimT (inP _ _ _) AIN))/orP [UAS | SAS].
    - have IN' : a \in Aprev by move/subsetP in SUBSET_A'; apply SUBSET_A'.
      move/forall_inP/(_ _ IN') in UAS.
      by rewrite ANGET in UAS.
    - rewrite /Abs.syscall_address_space /Abs.address_space /= in SAS.
      move: SAS => /existsP [sc /and3P [NONE ELEM /eqP?]]; subst Aprev.
      move: SUBSET_A'; rewrite subset1; move => /orP [] /eqP?; subst A'.
      + move: IN_pc' IN NIN; rewrite !in_set1; move=> /eqP->.
        by rewrite eq_refl.
      + by rewrite in_set0 in IN.
  }
  have NIN_i  : isolate_addr              \notin A' by apply NIN_any.
  have NIN_aJ : add_to_jump_targets_addr  \notin A' by apply NIN_any.
  have NIN_aS : add_to_store_targets_addr \notin A' by apply NIN_any.

  move: (def_sA) => /Sym.retag_set_preserves_get_definedness GETS_sA.
  move: (def_sJ) => /Sym.retag_set_preserves_get_definedness GETS_sJ.
  move: (def_sS) => /Sym.retag_set_preserves_get_definedness GETS_sS.
  simpl in *.

  have SNGET_sA_i : ~~ get (Symbolic.mem sA) isolate_addr
    by rewrite -GETS_sA SNGET_i.
  have SNGET_sA_aJ : ~~ get (Symbolic.mem sA) add_to_jump_targets_addr
    by rewrite -GETS_sA SNGET_aJ.
  have SNGET_sA_aS : ~~ get (Symbolic.mem sA) add_to_store_targets_addr
    by rewrite -GETS_sA SNGET_aS.

  have SNGET_sJ_i  : ~~ get (Symbolic.mem sJ) isolate_addr
    by rewrite -GETS_sJ.
  have SNGET_sJ_aJ : ~~ get (Symbolic.mem sJ) add_to_jump_targets_addr
    by rewrite -GETS_sJ.
  have SNGET_sJ_aS : ~~ get (Symbolic.mem sJ) add_to_store_targets_addr
    by rewrite -GETS_sJ.

  have SNGET_sS_i : ~~ get MS isolate_addr
    by rewrite -GETS_sS.
  have SNGET_sS_aJ : ~~ get MS add_to_jump_targets_addr
    by rewrite -GETS_sS.
  have SNGET_sS_aS : ~~ get MS add_to_store_targets_addr
    by rewrite -GETS_sS.

  have TSAI_s'_sA : forall X : {set word},
                      [disjoint A' & X] ->
                      tags_subsets_add_1_in
                        X
                        Snext
                        (SState SM SR pc@(Sym.PC F cid)
                                (SInternal (Snext + 1)%w SiT SaJT SaST))
                        sA.
  {
    move=> X DJX a.
    have NIN_a : a \in X -> ~ a \in A'. {
      move=> IN_a IN'_a.
      rewrite -setI_eq0 in DJX; move/eqP in DJX.
      have: a \in A' :&: X by rewrite inE; apply/andP.
      by rewrite DJX inE.
    }
    case M_IN: (a \in X); [move: M_IN => IN_X | move: M_IN => NIN_X].
    - specialize (NIN_a IN_X).
      generalize def_sA => def_sA';
        apply @Sym.retag_set_not_in with (p := a) in def_sA'; try assumption.
      + rewrite def_sA'.
        by destruct (Sym.sget sA a) as [[]|]; auto.
      + by rewrite (mem_enum (mem A')) /=; apply/negP.
    - generalize def_sA => def_sA';
        apply @Sym.retag_set_or_ok with (p := a) in def_sA';
        try first [assumption | exact (enum_uniq (mem A'))].
      move: def_sA' => [OLD | [cnew [Inew [Wnew [THEN [OK NOW]]]]]].
      + rewrite OLD.
        by destruct (Sym.sget sA a) as [[]|]; auto.
      + by rewrite THEN NOW; repeat split; auto.
  }

  have TSA_sA_sJ : tags_subsets_add_1 Snext sA sJ. {
    move=> a.
    generalize def_sJ => def_sJ';
      apply @Sym.retag_set_or with (p := a) in def_sJ';
      try first [assumption | exact (enum_uniq (mem J'))].
    move: def_sJ' => [OLD | [cnew [Inew [Wnew [THEN NOW]]]]].
    - rewrite -OLD.
      destruct (Sym.sget sA a) as [[]|]; auto.
    - rewrite THEN NOW; auto.
  }

  have TSA_sJ_sS : tags_subsets_add_1 Snext sJ (SState MS RS pcS siS). {
    move=> a.
    generalize def_sS => def_sS';
      apply @Sym.retag_set_or with (p := a) in def_sS';
      try first [assumption | exact (enum_uniq (mem S'))].
    move: def_sS' => [OLD | [cnew [Inew [Wnew [THEN NOW]]]]].
    - rewrite -OLD.
      destruct (Sym.sget sJ a) as [[]|]; auto.
    - rewrite THEN NOW; auto.
  }

  have TSAI_s0_sS' : forall X : {set word},
                       [disjoint A' & X] ->
                       tags_subsets_add_1_in
                         X
                         Snext
                         (SState SM SR pc@(Sym.PC F cid)
                                 (SInternal Snext SiT SaJT SaST))
                         (SState MS RS pc'@(Sym.PC JUMPED cid_sys) siS).
  {
    intros X DJX.
    eapply tags_subsets_add_1_in_trans.
    - apply TSAI_s'_sA; assumption.
    - eapply tags_subsets_add_1_in_trans.
      + apply tags_subsets_add_1_any_in; eassumption.
      + apply tags_subsets_add_1_any_in.
        apply TSA_sJ_sS; assumption.
  }

  have TSAI_rest : forall c,
                     c \in rem_all <<Aprev,Jprev,Sprev>> AC ->
                     tags_subsets_add_1_in
                       (Abs.address_space c)
                       Snext
                       (SState SM SR pc@(Sym.PC F cid)
                               (SInternal Snext SiT SaJT SaST))
                       (SState MS RS pc'@(Sym.PC JUMPED cid_sys) siS).
  {
    move=> c; rewrite in_rem_all => /andP [NEQ IN] a.
    apply TSAI_s0_sS'.
    have DJ' : [disjoint Aprev & Abs.address_space c]. {
      replace Aprev with (Abs.address_space <<Aprev,Jprev,Sprev>>)
        by reflexivity.
      have IN2 : list_utils.In2 <<Aprev,Jprev,Sprev>> c AC. {
        apply list_utils.in_neq_in2; try by apply/inP.
        by apply/eqP; rewrite eq_sym NEQ.
      }
      apply Abs.good_compartments__in2_disjoint in IN2.
      - by move: IN2; rewrite /Abs.disjoint_comp /= => /andP[].
      - eapply Abs.good_state_decomposed__good_compartments; eassumption.
    }
    eapply disjoint_trans; [|exact DJ'].
    exact SUBSET_A'.
  }

  have RC_rest : forall c,
                   c \in rem_all <<Aprev,Jprev,Sprev>> AC ->
                   get_compartment_id
                     (SState SM SR pc@(Sym.PC F cid)
                             (SInternal Snext SiT SaJT SaST))
                     c
                   = get_compartment_id
                       (SState MS RS pc'@(Sym.PC JUMPED cid_sys) siS) c.
  {
    move=> c c_in_AC'.
    apply eq_pick => /= a; apply/f_equal2 => //; clear a.
    apply eq_in_imset => a IN_a.
    move: TSAI_rest => /(_ c c_in_AC' a) /=.
    case: (Sym.sget _ a) => [[]|] //=.
    - move=> c1 I1 W1.
      case: (Sym.sget _ a) => [[]|] //=.
      by move=> c2 I2 W2 [/(_ IN_a)-> _].
    - by case: (Sym.sget _ a).
  }

  have NOT_SYSCALL_prev : ~ Abs.syscall_address_space
                              AM <<Aprev,Jprev,Sprev>>.
  {
    rewrite /Abs.syscall_address_space /=; move=> /existsP [sc].
    rewrite !inE => /and3P [NGET /or3P EQ_sc /eqP?]; subst Aprev.
    move: IN_pc'; rewrite in_set1 => /eqP?; subst sc.
    move: SUBSET_A'; rewrite subset1 => /orP [] /eqP?; subst A'.
    - by rewrite in_set1 eq_refl in NIN.
    - by rewrite eq_refl in NE_A'.
  }

  have USER_prev : Abs.user_address_space AM <<Aprev,Jprev,Sprev>>. {
    move/forallb_forall in ASS.
    by move: (ASS _ (elimT (inP _ _ _) AIN)) => /orP [UAS | SAS].
  }

  have NOT_USER_c_sys : ~ Abs.user_address_space AM c_sys. {
    move=> /forall_inP UAS.
    specialize (UAS _ pc_in_c_sys); simpl in UAS.
    rewrite -(lock eq) in IS_ISOLATE; subst.
    by rewrite ANGET_i in UAS.
  }

  have SYSCALL_c_sys : Abs.syscall_address_space AM c_sys. {
    move/forallb_forall in ASS.
    by move: (ASS _ (elimT (inP _ _ _) c_sys_in_AC)) => /orP [UAS | SAS].
  }

  have DIFF_prev_c_sys : <<Aprev,Jprev,Sprev>> <> c_sys
    by move=> ?; subst.

  have R_c_sys' : get_compartment_id
                    (SState MS RS pc'@(Sym.PC JUMPED cid_sys) siS)
                    c_sys
                    ?= cid_sys.
  {
    rewrite RC_rest in c_sys_id => //.
    rewrite in_rem_all; apply/andP; split=> //.
    by rewrite eq_sym; apply/eqP.
  }

(* REFINEMENT *)

  have Hres: get_compartment_id (SState MS RS pc'@(Sym.PC JUMPED cid_sys) siS)
                                <<Aprev :\: A',Jprev,Sprev>> = Some cid.
  { rewrite (get_compartment_id_irrelevancies RS pcS).
    apply (retag_set_get_compartment_id_same_ids def_sS); first by [].
    apply (retag_set_get_compartment_id_same_ids def_sJ); first by [].
    apply (retag_set_get_compartment_id_disjoint def_sA).
    { rewrite disjoint_subset /=.
      apply/subsetP => p''.
      by rewrite in_setD => /andP []. }
    rewrite (get_compartment_id_irrelevancies' SR pc@(Sym.PC F cid) Snext).
    have := (get_compartment_id_subset _ _ RPREV).
    apply.
    - exact: pc'.
    - by rewrite in_setD IN_pc' NIN.
    - by rewrite subDset subsetUr. }

  have Hnew: get_compartment_id (SState MS RS pc'@(Sym.PC JUMPED cid_sys) siS)
                                <<A',J',S'>> = Some Snext.
  { rewrite (get_compartment_id_irrelevancies RS pcS).
    apply (retag_set_get_compartment_id_same_ids def_sS); first by [].
    apply (retag_set_get_compartment_id_same_ids def_sJ); first by [].
    by apply (@retag_set_get_compartment_id_new_id _ _ _ _ <<A',J',S'>> Snext def_sA). }

  constructor=> //=.
  - rewrite /=.
    suff -> : RS = SR by [].
    have //= <- := (Sym.retag_set_preserves_regs _ _ _ _ _ def_sS).
    by rewrite -(Sym.retag_set_preserves_regs _ _ _ _ _ def_sJ)
               -(Sym.retag_set_preserves_regs _ _ _ _ _ def_sA).
  - move/id in def_sA; move/id in def_sJ; move/id in def_sS;
      eapply retag_set_preserves_memory_refinement in def_sA; [|eassumption];
      eapply retag_set_preserves_memory_refinement in def_sJ; [|eassumption];
      eapply retag_set_preserves_memory_refinement in def_sS; [|eassumption];
      simpl in *.
    assumption.
  - move=> p' Hp'.
    move: (COMPSWD p').
    rewrite (Sym.retag_set_preserves_definedness _ _ _ _ _ def_sA p')
            (Sym.retag_set_preserves_definedness _ _ _ _ _ def_sJ)
            (Sym.retag_set_preserves_definedness _ _ _ _ _ def_sS) => /(_ Hp') {Hp'}.
    case Hp': (Abs.in_compartment_opt AC p') => [cp'|] // _.
    case/Abs.in_compartment_opt_correct/andP: Hp'.
    have [{cp'} ->|NE] := altP (cp' =P <<Aprev,Jprev,Sprev>>) => cp'_in_AC p'_in_cp'.
    { rewrite /= in_setD p'_in_cp' andbT.
      by case: (p' \in A'). }
    apply (Abs.in_compartment_opt_is_some _ _ cp').
    by rewrite /Abs.in_compartment !in_cons in_rem_all NE cp'_in_AC !orbT /=.
  - move=> c'.
    rewrite !in_cons => /or3P [/eqP -> {c'}|/eqP -> {c'}|c'_in].
    + by rewrite Hres.
    + by rewrite Hnew.
    + rewrite -RC_rest //.
      apply IDSWD.
      rewrite in_rem_all in c'_in.
      by case/andP: c'_in.
  - move=> c1 c2.
    rewrite !in_cons /=
            => /or3P [/eqP -> {c1}|/eqP -> {c1}|c1_in_AC]
               /or3P [/eqP -> {c2}|/eqP -> {c2}|c2_in_AC] //=;
    rewrite ?Hres ?Hnew; try congruence.
    + rewrite -RPREV -RC_rest // => NEW.
      rewrite in_rem_all in c2_in_AC.
      case/andP: c2_in_AC => [/eqP ? ?].
      by apply IDSU in NEW; try congruence.
    + rewrite -RC_rest // /get_compartment_id.
      case: pickP => [cid'' /eqP Hcid''|]//= [E].
      subst cid''.
      move: (set11 (Some Snext)).
      rewrite -Hcid'' => /imsetP /= [p' _].
      case GETp': (Sym.sget _ _) => [[cp' Ip' Wp']|] //= [E].
      subst cp'.
      move: (Sym.sget_lt_next _ _ _ _ _ RINT GETp') => /=.
      by rewrite ltb_irrefl.
    + rewrite -RPREV -RC_rest // => NEW.
      rewrite in_rem_all in c1_in_AC.
      case/andP: c1_in_AC => [/eqP ? ?].
      by apply IDSU in NEW; try congruence.
    + rewrite -RC_rest // /get_compartment_id.
      case: pickP => [cid'' /eqP Hcid''|]//= [E].
      subst cid''.
      move: (set11 (Some Snext)).
      rewrite -Hcid'' => /imsetP /= [p' _].
      case GETp': (Sym.sget _ _) => [[cp' Ip' Wp']|] //= [E].
      subst cp'.
      move: (Sym.sget_lt_next _ _ _ _ _ RINT GETp') => /=.
      by rewrite ltb_irrefl.
    + rewrite -!RC_rest //.
      rewrite !in_rem_all in c1_in_AC c2_in_AC.
      case/andP: c1_in_AC => ? ?; case/andP: c2_in_AC => ? ?.
      by apply IDSU.
  - move=> c' cid'.
    rewrite !inE => /or3P [ /eqP{c'}-> | /eqP{c'}-> | c'_in_AC'].
    + (* This case (Aprev :\: A') ends up being very similar to the third
         (neither Aprev :\: A' nor A') -- in fact, after a certain point,
         identical (up to some stylistic changes. *)
      rewrite Hres; move=> [] <-{cid'} /=.
      move/(_ <<Aprev,Jprev,Sprev>> cid AIN RPREV) in JTWF; simpl in JTWF.
      rewrite JTWF.
      apply/setP; rewrite /eq_mem /= => a; rewrite !in_set.
      have DJ : [disjoint A' & Aprev :\: A']
        by rewrite -setI_eq0 setIDA setIC -setIDA setDv setI0.
      move: TSAI_s0_sS' => /(_ (Aprev :\: A') DJ a).
      case: (Sym.sget _ a) => [[cid1 I1 W1]|] //=;
        [|by case: (Sym.sget _ a) => [[]|] //].
      case: (Sym.sget _ a) => [[cid2 I2 W2]|] //=.
      move=> [cid_eq [OR_Is OR_Ws]].
      case: OR_Is => [-> // | <-{I2}].
      rewrite inE in_set1.
      suff: cid != Snext by move=> /negbTE-> //.
      apply/eqP; move=> H; apply eq__nlt in H; contradict H; apply ltb_lt.
      move: RPREV; rewrite /get_compartment_id.
      case: pickP => // x /eqP cid_set []?; subst x.
      have: Some cid == Some cid by apply eq_refl.
      rewrite -(in_set1 (Some cid)) -cid_set => /imsetP [p' p'_in_prev] /=.
      case SGET: (Sym.sget _ p') => [[d I' W']|] //= => [[?]]; subst d.
      replace Snext
        with (Sym.next_id
                (Symbolic.internal
                   (SState SM SR pc@(Sym.PC F cid)
                           (SInternal Snext SiT SaJT SaST))))
        by reflexivity.
      eapply Sym.sget_lt_next; eassumption.
    + rewrite Hnew /= => [[E]]. subst cid'.
      apply/setP => p'.
      rewrite in_set.
      have [INp'|NINp'] := boolP (p' \in J').
      * { have [Hs|Hs] := Sym.retag_set_or_ok _ _ _ _ _ (enum_uniq (mem S')) def_sS p'.
          - rewrite (sget_irrelevancies RS pcS) -Hs.
            rewrite -(mem_enum (mem J')) in INp'.
            have [? [? [? [? H]]]] := Sym.retag_set_in _ _ _ _ _ (enum_uniq (mem J')) def_sJ _ INp'.
            by rewrite H /= in_setU1 eqxx.
          - case: Hs => ? [? [? [H'' [H' H]]]].
            rewrite (sget_irrelevancies RS pcS) H {H} /=.
            rewrite -(mem_enum (mem J')) in INp'.
            have [? [? [? [? H]]]] := Sym.retag_set_in _ _ _ _ _ (enum_uniq (mem J')) def_sJ _ INp'.
            rewrite H in H''.
            move: H'' => [? ? ?]. subst.
            by rewrite in_setU1 eqxx. }
      * { have [Hs|Hs] := Sym.retag_set_or_ok _ _ _ _ _ (enum_uniq (mem S')) def_sS p'.
          - rewrite (sget_irrelevancies RS pcS) -Hs.
            rewrite -(mem_enum (mem J')) in NINp'.
            have <- := Sym.retag_set_not_in _ _ _ _ _ def_sJ _ NINp'.
            have [Ha|Ha] := Sym.retag_set_or_ok _ _ _ _ _ (enum_uniq (mem A')) def_sA p'.
            + rewrite -Ha.
              case Gp': (Sym.sget _ _) => [[cp' Ip' Wp']|] //=.
              * have [IN|//] := boolP (Snext \in Ip').
                have contra: Snext <? Snext.
                { apply (bounded_tags RINT Gp').
                  by rewrite in_setU IN. }
                by rewrite ltb_irrefl in contra.
            + case: Ha => ca [Ia [Wa [a1 [/eqP a2 a3]]]].
              subst ca.
              rewrite a3 /=.
              have [IN|//] := boolP (Snext \in Ia).
              have contra: Snext <? Snext.
              { apply (bounded_tags RINT a1).
                by rewrite in_setU IN. }
              by rewrite ltb_irrefl in contra.
          - case: Hs => a [aa [aaa [H'' [H' H]]]].
            rewrite (sget_irrelevancies RS pcS) H {H} /=.
            rewrite -(mem_enum (mem J')) in NINp'.
            have H := Sym.retag_set_not_in _ _ _ _ _ def_sJ _ NINp'.
            rewrite -H in H''.
            have [IN|//] := boolP (Snext \in aa).
            have [Ha|Ha] := Sym.retag_set_or_ok _ _ _ _ _ (enum_uniq (mem A')) def_sA p'.
            + rewrite -Ha in H''.
              have contra: Snext <? Snext.
              { apply (bounded_tags RINT H'').
                by rewrite in_setU IN. }
              by rewrite ltb_irrefl in contra.
            + case: Ha => x [xx [xxx [xxxx [xxxxx xxxxxx]]]].
              rewrite xxxxxx in H''.
              move: H'' => [? ? ?]. subst.
              have contra: a <? a.
              { apply (bounded_tags RINT xxxx).
                by rewrite in_setU IN. }
              by rewrite ltb_irrefl in contra. }
    + move/(_ c' c'_in_AC') in RC_rest.
      rewrite -RC_rest => GCI_cid'.
      move: (c'_in_AC'); rewrite in_rem_all => /andP [c'_neq_prev c'_in_AC].
      move/(_ c' cid' c'_in_AC GCI_cid') in JTWF.
      rewrite JTWF.
      apply/setP.
      rewrite /eq_mem /= => a; rewrite !in_set.
      move: TSAI_rest => /(_ c' c'_in_AC' a).
      case: (Sym.sget _ a) => [[]|] //=; [|by case: (Sym.sget _ a) => [[]|]].
      move=> cid1 I1 W1.
      case: (Sym.sget _ a) => [[]|] //=.
      move=> cid2 I2 W2.
      move=> [cid_eq [OR_Is OR_Ws]].
      case: OR_Is => [-> // | <-{I2}].
      rewrite inE in_set1.
      suff: cid' != Snext by move=> /negbTE-> //.
      apply/eqP; move=> H; apply eq__nlt in H; contradict H; apply ltb_lt.
      move: GCI_cid'; rewrite /get_compartment_id.
      case: pickP => // x /eqP cid'_set []?; subst x.
      have: Some cid' == Some cid' by apply eq_refl.
      rewrite -(in_set1 (Some cid')) -cid'_set => /imsetP [p' p'_in_c'] /=.
      case SGET: (Sym.sget _ p') => [[d I' W']|] //= => [[?]]; subst d.
      replace Snext
        with (Sym.next_id
                (Symbolic.internal
                   (SState SM SR pc@(Sym.PC F cid)
                           (SInternal Snext SiT SaJT SaST))))
        by reflexivity.
      eapply Sym.sget_lt_next; eassumption.
  - move=> c' cid'.
    rewrite !inE => /or3P [ /eqP{c'}-> | /eqP{c'}-> | c'_in_AC'].
    + (* This case (Aprev :\: A') ends up being very similar to the third
         (neither Aprev :\: A' nor A') -- in fact, after a certain point,
         identical (up to some stylistic changes. *)
      rewrite Hres; move=> [] <-{cid'} /=.
      move/(_ <<Aprev,Jprev,Sprev>> cid AIN RPREV) in STWF; simpl in STWF.
      rewrite STWF.
      apply/setP; rewrite /eq_mem /= => a; rewrite !in_set.
      have DJ : [disjoint A' & Aprev :\: A']
        by rewrite -setI_eq0 setIDA setIC -setIDA setDv setI0.
      move: TSAI_s0_sS' => /(_ (Aprev :\: A') DJ a).
      case: (Sym.sget _ a) => [[cid1 I1 W1]|] //=;
        [|by case: (Sym.sget _ a) => [[]|] //].
      case: (Sym.sget _ a) => [[cid2 I2 W2]|] //=.
      move=> [cid_eq [OR_Is OR_Ws]].
      case: OR_Ws => [-> // | <-{W2}].
      rewrite inE in_set1.
      suff: cid != Snext by move=> /negbTE-> //.
      apply/eqP; move=> H; apply eq__nlt in H; contradict H; apply ltb_lt.
      move: RPREV; rewrite /get_compartment_id.
      case: pickP => // x /eqP cid_set []?; subst x.
      have: Some cid == Some cid by apply eq_refl.
      rewrite -(in_set1 (Some cid)) -cid_set => /imsetP [p' p'_in_prev] /=.
      case SGET: (Sym.sget _ p') => [[d I' W']|] //= => [[?]]; subst d.
      replace Snext
        with (Sym.next_id
                (Symbolic.internal
                   (SState SM SR pc@(Sym.PC F cid)
                           (SInternal Snext SiT SaJT SaST))))
        by reflexivity.
      eapply Sym.sget_lt_next; eassumption.
    + rewrite Hnew /= => [[E]]. subst cid'.
      apply/setP => p'.
      rewrite in_set (sget_irrelevancies RS pcS).
      have [INs|NINs] := boolP (p' \in S').
      * { rewrite -(mem_enum (mem S')) in INs.
          have := Sym.retag_set_in _ _ _ _ _ (enum_uniq (mem S')) def_sS p' INs.
          move => [cs [Is [Ws [H1 H2]]]].
          rewrite H2 /=.
          by rewrite in_setU1 eqxx /=. }
      * { rewrite -(mem_enum (mem S')) in NINs.
          have  DEFp' := Sym.retag_set_not_in _ _ _ _ _ def_sS p' NINs.
          rewrite -DEFp' {DEFp'}.
          have := Sym.retag_set_or _ _ _ _ _ (enum_uniq (mem J')) def_sJ p'.
          case=> [DEFp | [ca [Ia [Wa [H1 H2]]]]].
          { rewrite -DEFp {DEFp}.
            have [DEFp|H]:= Sym.retag_set_or _ _ _ _ _ (enum_uniq (mem A')) def_sA p'.
            - rewrite -DEFp {DEFp}.
              case GET: (Sym.sget _ _) => [[ca Ia Wa] |] //=.
              + have [INwa|NINwa] // := boolP (Snext \in Wa).
                have := (bounded_tags RINT GET).
                move=> /(_ Snext).
                rewrite in_setU. rewrite INwa. rewrite orbT.
                move => /(_ erefl).
                rewrite /=.
                by rewrite ltb_irrefl.
            - case: H => ca [ia [wa [H1 H2]]].
              rewrite H2 /=.
              have [INwa|NINwa] // := boolP (Snext \in wa).
              have := (bounded_tags RINT H1).
              move=> /(_ Snext).
              rewrite in_setU. rewrite INwa. rewrite orbT.
              move => /(_ erefl).
              rewrite /=.
              by rewrite ltb_irrefl. }
          have [DEFp|H]:= Sym.retag_set_or _ _ _ _ _ (enum_uniq (mem A')) def_sA p'.
          - rewrite -DEFp in H1.
            simpl.
            rewrite H2 /=.
            have [INwa|NINwa] // := boolP (Snext \in Wa).
            have := (bounded_tags RINT H1).
            move=> /(_ Snext).
            rewrite in_setU. rewrite INwa. rewrite orbT.
            move => /(_ erefl).
            rewrite /=.
            by rewrite ltb_irrefl.
          - rewrite H2 /=.
            case: H => ca' [Ia' [wa' [H1' H2']]].
            rewrite H1 in H2'.
            move: H2' => [? ? ?]. subst.
            have [INwa|NINwa] // := boolP (Snext \in wa').
            have := (@bounded_tags (SState SM SR pc@(Sym.PC F cid) (SInternal Snext SiT SaJT SaST)) _ _ _ _ _ RINT H1').
            move=> /(_ Snext).
            rewrite in_setU. rewrite INwa. rewrite orbT.
            move => /(_ erefl).
            rewrite /=.
            by rewrite ltb_irrefl. }
    + move/(_ c' c'_in_AC') in RC_rest.
      rewrite -RC_rest => GCI_cid'.
      move: (c'_in_AC'); rewrite in_rem_all => /andP [c'_neq_prev c'_in_AC].
      move/(_ c' cid' c'_in_AC GCI_cid') in STWF.
      rewrite STWF.
      apply/setP.
      rewrite /eq_mem /= => a; rewrite !in_set.
      move: TSAI_rest => /(_ c' c'_in_AC' a).
      case: (Sym.sget _ a) => [[]|] //=; [|by case: (Sym.sget _ a) => [[]|]].
      move=> cid1 I1 W1.
      case: (Sym.sget _ a) => [[]|] //=.
      move=> cid2 I2 W2.
      move=> [cid_eq [OR_Is OR_Ws]].
      case: OR_Ws => [-> // | <-{W2}].
      rewrite inE in_set1.
      suff: cid' != Snext by move=> /negbTE-> //.
      apply/eqP; move=> H; apply eq__nlt in H; contradict H; apply ltb_lt.
      move: GCI_cid'; rewrite /get_compartment_id.
      case: pickP => // x /eqP cid'_set []?; subst x.
      have: Some cid' == Some cid' by apply eq_refl.
      rewrite -(in_set1 (Some cid')) -cid'_set => /imsetP [p' p'_in_c'] /=.
      case SGET: (Sym.sget _ p') => [[d I' W']|] //= => [[?]]; subst d.
      replace Snext
        with (Sym.next_id
                (Symbolic.internal
                   (SState SM SR pc@(Sym.PC F cid)
                           (SInternal Snext SiT SaJT SaST))))
        by reflexivity.
      eapply Sym.sget_lt_next; eassumption.
  - apply/andP; split; [apply eq_refl | apply/eqP; apply R_c_sys'].
  - rewrite /refine_syscall_addrs_b.
    case/and3P: RSC => ? /eqP [/eqP H1 /eqP H2 /eqP H3] ?.
    apply/and3P.
    split=> //.
    have H o : (o == None) = ~~ o by case: o.
    rewrite eqE /=.
    rewrite !H in H1 H2 H3 *.
    by rewrite -!(Sym.retag_set_preserves_get_definedness _ _ _ _ _ def_sS)
               -!(Sym.retag_set_preserves_get_definedness _ _ _ _ _ def_sJ)
               -!(Sym.retag_set_preserves_get_definedness _ _ _ _ _ def_sA) H1 H2 H3 /=.
  - have SGINT_sA : Sym.good_internal sA. {
      eapply Sym.retag_set_updating_preserves_good_internal;
        try apply def_sA; try eauto 1; simpl;
        try (by rewrite (mem_enum (mem A'))).
      - by rewrite SNGET_i.
      - by rewrite SNGET_aJ.
      - by rewrite SNGET_aS.
      - exact (enum_uniq (pred_of_set A')).
    }

    have SGINT_sJ : Sym.good_internal sJ. {
      generalize def_sJ => GETS;
        move/Sym.retag_set_preserves_get_definedness in GETS.
      eapply Sym.good_internal_equiv; try apply SGINT_sA; try (by apply/eqP);
        auto.
      - intros a.
        generalize def_sJ => def_sJ';
          apply @Sym.retag_set_or with (p := a) in def_sJ'; try assumption.
        move: def_sJ' => [OLD | [cnew [Inew [Wnew [THEN NOW]]]]].
        + rewrite OLD.
          by destruct (Sym.sget sJ a) as [[]|].
        + by rewrite THEN NOW.
        + exact (enum_uniq (pred_of_set J')).
      - eapply Sym.retag_set_preserves_next_id; eassumption.
      - move=> x.
        let cleanup X := try first [assumption | exact (enum_uniq (mem X))]
        in generalize def_sA => def_sA';
             apply @Sym.retag_set_or with (p := x) in def_sA'; cleanup A';
           generalize def_sJ => def_sJ';
             apply @Sym.retag_set_or with (p := x) in def_sJ'; cleanup J'.
        idtac;
          case: def_sA' => [OLD_A | [cA [IA [WA [THEN_A NOW_A]]]]];
          case: def_sJ' => [OLD_J | [cJ [IJ [WJ [THEN_J NOW_J]]]]];
          try move/eqP in OK_A; subst;
          first [move/id in OLD_A | move/id in THEN_A; move/id in NOW_A];
          first [move/id in OLD_J | move/id in THEN_J; move/id in NOW_J].
        + rewrite -OLD_J -OLD_A.
          rewrite (sget_next_irrelevant Snext).
          case SGET: (Sym.sget _ x) => [[cid1 I1 W1]|] //= cid' IN_cid'.
          apply Sym.sget_IW_lt_next with (c' := cid') in SGET; try assumption.
          rewrite -(Sym.retag_set_preserves_next_id _ _ _ _ _ def_sJ)
                  -(Sym.retag_set_preserves_next_id _ _ _ _ _ def_sA).
          simpl in *.
          by apply Sym.succ_trans.
        + rewrite NOW_J /=.
          move=> cid'; rewrite -setUA inE in_set1 => /orP [/eqP->{cid'} | IN].
          * rewrite -(Sym.retag_set_preserves_next_id _ _ _ _ _ def_sJ)
                    -(Sym.retag_set_preserves_next_id _ _ _ _ _ def_sA)
                    /=.
            move: (lew_max Snext) => /le_iff_lt_or_eq [LT | //].
            eapply ranges.lebw_succ; eassumption.
          * rewrite THEN_J in OLD_A.
            apply Sym.sget_IW_lt_next with (c' := cid') in OLD_A;
              try assumption.
            rewrite -(Sym.retag_set_preserves_next_id _ _ _ _ _ def_sJ)
                    -(Sym.retag_set_preserves_next_id _ _ _ _ _ def_sA)
                    /=.
            exact OLD_A.
        + rewrite -OLD_J NOW_A.
          move=> cid' IN.
          apply Sym.sget_IW_lt_next with (c' := cid') in THEN_A;
            try assumption.
          rewrite -(Sym.retag_set_preserves_next_id _ _ _ _ _ def_sJ)
                  -(Sym.retag_set_preserves_next_id _ _ _ _ _ def_sA)
                  /=.
          exact THEN_A.
        + rewrite NOW_J /=.
          move=> cid'; rewrite -setUA inE in_set1 => /orP [/eqP->{cid'} | IN].
          * rewrite -(Sym.retag_set_preserves_next_id _ _ _ _ _ def_sJ)
                    -(Sym.retag_set_preserves_next_id _ _ _ _ _ def_sA)
                    /=.
            move: (lew_max Snext) => /le_iff_lt_or_eq [LT | //].
            eapply ranges.lebw_succ; eassumption.
          * rewrite THEN_J in NOW_A; case: NOW_A => *; subst.
            apply Sym.sget_IW_lt_next with (c' := cid') in THEN_A;
              try assumption.
            rewrite -(Sym.retag_set_preserves_next_id _ _ _ _ _ def_sJ)
                    -(Sym.retag_set_preserves_next_id _ _ _ _ _ def_sA)
                    /=.
            exact THEN_A.
    }

    have SGINT_sS : Sym.good_internal (SState MS RS pcS siS). {
      generalize def_sS => GETS;
        move/Sym.retag_set_preserves_get_definedness in GETS.
      eapply Sym.good_internal_equiv; try apply SGINT_sJ; try (by apply/eqP);
        auto.
      - intros a.
        generalize def_sS => def_sS';
          apply @Sym.retag_set_or with (p := a) in def_sS'; try assumption.
        move: def_sS' => [OLD | [cnew [Inew [Wnew [THEN NOW]]]]].
        + rewrite OLD.
          by destruct (Sym.sget (SState MS RS pcS siS) a) as [[]|].
        + by rewrite THEN NOW.
        + exact (enum_uniq (pred_of_set S')).
      - eapply Sym.retag_set_preserves_next_id; eassumption.
      - move=> x.
        move: (def_sS) => def_sS';
           apply @Sym.retag_set_or with (p := x) in def_sS';
           try first [assumption | exact (enum_uniq (mem S'))].
        case: def_sS' => [OLD_S | [cS [IS [WS [THEN_S NOW_S]]]]];
          first [move/id in OLD_S | move/id in THEN_S; move/id in NOW_S].
        + rewrite -OLD_S.
          case SGET: (Sym.sget sJ x) => [[cid' I' W']|] // cid'' IN''.
          rewrite -(Sym.retag_set_preserves_next_id _ _ _ _ _ def_sS).
          by apply Sym.sget_IW_lt_next with (c' := cid'') in SGET.
        + rewrite NOW_S.
          rewrite -(Sym.retag_set_preserves_next_id _ _ _ _ _ def_sS).
          move=> cid'.
          rewrite setUC -setUA inE in_set1 setUC => /orP [/eqP->{cid'} | IN].
          * rewrite -(Sym.retag_set_preserves_next_id _ _ _ _ _ def_sJ)
                    -(Sym.retag_set_preserves_next_id _ _ _ _ _ def_sA)
                    /=.
            move: (lew_max Snext) => /le_iff_lt_or_eq [LT | //].
            eapply ranges.lebw_succ; eassumption.
          * by apply Sym.sget_IW_lt_next with (c' := cid') in THEN_S.
    }

    exact SGINT_sS.
Qed.

Lemma prove_permitted_now_in AR AM AC Ask Aprev mem reg pc extra c i cid cid' cid'' II WW F :
  let ast := AState pc AR AM AC Ask Aprev in
  let sst := SState mem reg pc@(Sym.PC F cid') extra in
  Abs.good_state ast ->
  Sym.good_state sst ->
  get (Symbolic.mem sst) (common.val (Symbolic.pc sst)) ?= i@(Sym.DATA cid'' II WW) ->
  (do! guard (cid'' == cid') || (F == JUMPED) && (cid' \in II);
   Some cid'') ?= cid ->
  refine_previous_b (Abs.step_kind ast) (Abs.previous ast) sst ->
  well_defined_compartments sst AC ->
  well_defined_ids sst AC ->
  unique_ids sst AC ->
  well_formed_jump_targets sst AC ->
  Abs.in_compartment_opt (Abs.compartments ast) (common.val (Symbolic.pc sst)) ?= c ->
  Abs.permitted_now_in (Abs.compartments ast) (Abs.step_kind ast) (Abs.previous ast) (common.val (Symbolic.pc sst)) ?= c.
Proof.
  rewrite /=.
  move=> AGOOD SGOOD PC def_cid RPREV COMPSWD IDSWD IDSU JTWF COMP.
 undo1 def_cid COND.
        have ? : cid'' = cid by congruence.
        subst cid''.
        rewrite /Abs.permitted_now_in COMP /=.
        case/Abs.in_compartment_opt_correct/andP: COMP => c_in_AC pc_in_c.
        rewrite/refine_previous_b /= in RPREV.
        case/andP: RPREV => /eqP ? /eqP Aprev_id. subst Ask.
        case: SGOOD => [[SGMEM ? ?] ].
        have c_id : get_compartment_id (SState mem reg pc@(Sym.PC F cid') extra) c ?= cid.
        { rewrite (in_compartment_get_compartment_id COMPSWD IDSWD IDSU c_in_AC pc_in_c).
          by rewrite /Sym.sget PC /=. }
        case/and4P: AGOOD => /= Aprev_in_AC *.
        case/orP: COND => [/eqP ? | /andP [/eqP ? cid'_in_I]].
          subst cid'.
          suff -> : c = Aprev by rewrite eqxx.
          apply (IDSU _ _ c_in_AC Aprev_in_AC).
          by rewrite c_id Aprev_id.
        subst F. rewrite eqxx /=.
        by rewrite (JTWF _ _ Aprev_in_AC Aprev_id) in_set /Sym.sget PC /= cid'_in_I orbT.
Qed.

Lemma prove_get_compartment_id AC mem reg pc F cid cid' cid'' extra i II WW c :
  Sym.good_state (SState mem reg pc@(Sym.PC F cid') extra) ->
  get mem pc ?= i@(Sym.DATA cid'' II WW) ->
  (do! guard (cid'' == cid') || (F == JUMPED) && (cid' \in II);
   Some cid'') ?= cid ->
  well_defined_compartments (SState mem reg pc@(Sym.PC F cid') extra) AC ->
  well_defined_ids(SState mem reg pc@(Sym.PC F cid') extra) AC ->
  unique_ids (SState mem reg pc@(Sym.PC F cid') extra) AC ->
  Abs.in_compartment_opt AC pc ?= c ->
  get_compartment_id (SState mem reg pc@(Sym.PC F cid') extra) c == Some cid.
Proof.
  move=> SGOOD PC def_cid COMPSWD IDSWD IDSU /Abs.in_compartment_opt_correct/andP [c_in_AC pc_in_c].
  apply/eqP.
  case: SGOOD => [[SGMEM _] _].
  rewrite (in_compartment_get_compartment_id COMPSWD IDSWD IDSU c_in_AC pc_in_c)
          /Sym.sget PC.
  by undo1 def_cid COND; unoption.
Qed.

Theorem backward_simulation : forall ast sst sst',
  Abs.good_state ast ->
  refine ast sst ->
  sstep sst sst' ->
  exists ast',
    astep ast ast' /\
    refine ast' sst'.
Proof.
  move=> ast sst sst' AGOOD REFINE SSTEP.
  assert (SGOOD : Sym.good_state sst) by (eapply refine_good; eassumption).
  destruct REFINE as [RPC RREGS RMEMS COMPSWD IDSWD IDSU JTWF STWF RPREV RSC RINT],
           ast    as [Apc AR    AM    AC    Ask Aprev];
    simpl in *.
  destruct SSTEP; subst; try subst mvec;
    unfold Symbolic.next_state_reg, Symbolic.next_state_pc,
           Symbolic.next_state_reg_and_pc, Symbolic.next_state in *;
    simpl in *;
    unfold Sym.rvec_next, Sym.rvec_jump, Sym.rvec_store, Sym.rvec_simple,
           Sym.rvec_step in *;
    simpl in *.

  - (* Nop *)
    undo1 NEXT rvec; undo1 def_rvec cid;
      unfold Sym.can_execute,Sym.compartmentalization_rvec in *;
      unoption; simpl in *.
    destruct tpc as [F cid']; try discriminate;
      destruct ti as [cid'' I W]; try discriminate.
    move/eqP in RPC; subst Apc.
    move: (COMPSWD pc).
    rewrite /Sym.sget PC => /(_ erefl).
    case COMP: (Abs.in_compartment_opt _ _) => [c|] // _.
    exists (AState (pc+1)%w AR AM AC INTERNAL c). split.
    + eapply Abs.step_nop; try reflexivity.
      * unfold Abs.decode.
        unfold refine_memory,pointwise,refine_mem_loc_b in RMEMS;
          specialize RMEMS with pc; rewrite PC in RMEMS;
          destruct (get AM pc); [simpl|contradiction].
        move/eqP in RMEMS; subst; assumption.
      * by apply (prove_permitted_now_in AGOOD SGOOD PC def_cid).
    + constructor; simpl;
        try solve [done | eapply (prove_get_compartment_id SGOOD);
                          solve [ eassumption
                                | rewrite /Sym.sget /= PC; reflexivity ]].

  - (* Const *)
    undo1 NEXT rvec;
      destruct told; try discriminate;
      undo1 def_rvec cid;
      undo1 NEXT regs';
      unfold Sym.can_execute,Sym.compartmentalization_rvec in *;
      unoption; simpl in *.
    destruct tpc as [F cid']; try discriminate;
      destruct ti as [cid'' I W]; try discriminate.
    move/eqP in RPC; subst Apc.
    move: (COMPSWD pc).
    rewrite /Sym.sget PC => /(_ erefl).
    case COMP: (Abs.in_compartment_opt _ _) => [c|] // _.
    evar (AR' : registers t);
      exists (AState (pc+1)%w AR' AM AC INTERNAL c); split;
      subst AR'.
    + eapply Abs.step_const; try reflexivity.
      * unfold Abs.decode.
        unfold refine_memory,pointwise,refine_mem_loc_b in RMEMS;
          specialize RMEMS with pc; rewrite PC in RMEMS;
          destruct (get AM pc); [simpl|contradiction].
        move/eqP in RMEMS; subst; eassumption.
      * by apply (prove_permitted_now_in AGOOD SGOOD PC def_cid).
      * unfold upd; rewrite /refine_registers /pointwise in RREGS;
          specialize RREGS with r.
        case: (get AR r) RREGS => [a|] RREGS;
          [reflexivity | rewrite OLD in RREGS; done].
    + constructor; simpl;
        try solve [done | eapply (prove_get_compartment_id SGOOD);
                          solve [ eassumption
                                | rewrite /Sym.sget /= PC; reflexivity ]].
      rewrite /refine_registers /pointwise in RREGS *; intros r'.
      destruct (r == r') eqn:EQ_r; move/eqP in EQ_r; [subst r'|].
      * erewrite get_set_eq, get_upd_eq by eauto.
        by unfold refine_reg_b.
      * erewrite get_set_neq, get_upd_neq with (m' := regs') by eauto.
        apply RREGS.

  - (* Mov *)
    undo1 NEXT rvec;
      destruct t1,told; try discriminate;
      undo1 def_rvec cid;
      undo1 NEXT regs';
      unfold Sym.can_execute,Sym.compartmentalization_rvec in *;
      unoption; simpl in *.
    destruct tpc as [F cid']; try discriminate;
      destruct ti as [cid'' I W]; try discriminate.
    move/eqP in RPC; subst Apc.
    move: (COMPSWD pc).
    rewrite /Sym.sget PC => /(_ erefl).
    case COMP: (Abs.in_compartment_opt _ _) => [c|] // _.
    rewrite /refine_registers /pointwise in RREGS.
    destruct (get AR r1) as [x1|] eqn:GET1;
      [| specialize RREGS with r1; rewrite R1W GET1 in RREGS; done].
    destruct (get AR r2) as [x2|] eqn:GET2;
      [| specialize RREGS with r2; rewrite OLD GET2 in RREGS; done].
    evar (AR' : registers t);
      exists (AState (pc+1)%w AR' AM AC INTERNAL c); split;
      subst AR'.
    + eapply Abs.step_mov; try reflexivity.
      * unfold Abs.decode.
        unfold refine_memory,pointwise,refine_mem_loc_b in RMEMS;
          specialize RMEMS with pc; rewrite PC in RMEMS;
          destruct (get AM pc); [simpl|contradiction].
        move/eqP in RMEMS; subst; eassumption.
      * by apply (prove_permitted_now_in AGOOD SGOOD PC def_cid).
      * eassumption.
      * unfold upd; rewrite GET2; reflexivity.
    + constructor; simpl;
        try solve [done | eapply (prove_get_compartment_id SGOOD);
                          solve [ eassumption
                                | rewrite /Sym.sget /= PC; reflexivity ]].
      rewrite /refine_registers /pointwise in RREGS *; intros r2'.
      destruct (r2 == r2') eqn:EQ_r2; move/eqP in EQ_r2; [subst r2'|].
      * erewrite get_set_eq, get_upd_eq by eauto.
        by specialize RREGS with r1; rewrite GET1 R1W /refine_reg_b in RREGS *.
      * erewrite get_set_neq, get_upd_neq with (m' := regs') by eauto.
        apply RREGS.

  - (* Binop *)
    undo1 NEXT rvec;
      destruct t1,t2,told; try discriminate;
      undo1 def_rvec cid;
      undo1 NEXT regs';
      unfold Sym.can_execute,Sym.compartmentalization_rvec in *;
      unoption; simpl in *.
    destruct tpc as [F cid']; try discriminate;
      destruct ti as [cid'' I W]; try discriminate.
    move/eqP in RPC; subst Apc.
    move: (COMPSWD pc).
    rewrite /Sym.sget PC => /(_ erefl).
    case COMP: (Abs.in_compartment_opt _ _) => [c|] // _.
    rewrite /refine_registers /pointwise in RREGS.
    destruct (get AR r1) as [x1|] eqn:GET1;
      [| specialize RREGS with r1; rewrite R1W GET1 in RREGS; done].
    destruct (get AR r2) as [x2|] eqn:GET2;
      [| specialize RREGS with r2; rewrite R2W GET2 in RREGS; done].
    destruct (get AR r3) as [x3|] eqn:GET3;
      [| specialize RREGS with r3; rewrite OLD GET3 in RREGS; done].
    evar (AR' : registers t);
      exists (AState (pc+1)%w AR' AM AC INTERNAL c); split;
      subst AR'.
    + eapply Abs.step_binop; try reflexivity.
      * unfold Abs.decode.
        unfold refine_memory,pointwise,refine_mem_loc_b in RMEMS;
          specialize RMEMS with pc; rewrite PC in RMEMS;
          destruct (get AM pc); [simpl|contradiction].
        move/eqP in RMEMS; subst; eassumption.
      * by apply (prove_permitted_now_in AGOOD SGOOD PC def_cid).
      * eassumption.
      * eassumption.
      * unfold upd; rewrite GET3; reflexivity.
    + constructor; simpl;
        try solve [done | eapply (prove_get_compartment_id SGOOD);
                          solve [ eassumption
                                | rewrite /Sym.sget /= PC; reflexivity ]].
      unfold upd; rewrite /refine_registers /pointwise in RREGS *; intros r3'.
      destruct (r3 == r3') eqn:EQ_r3; move/eqP in EQ_r3; [subst r3'|].
      * erewrite get_set_eq, get_upd_eq by eauto.
        { unfold refine_reg_b. apply/eqP; f_equal.
          - by specialize RREGS with r1;
               rewrite GET1 R1W /refine_reg_b in RREGS *; apply/eqP.
          - by specialize RREGS with r2;
               rewrite GET2 R2W /refine_reg_b in RREGS *; apply/eqP. }
      * erewrite get_set_neq, get_upd_neq with (m' := regs') by eauto.
        apply RREGS.

  - (* Load *)
    undo1 NEXT rvec;
      destruct t1,t2,told; try discriminate;
      undo1 def_rvec cid;
      undo1 NEXT regs';
      unfold Sym.can_execute,Sym.compartmentalization_rvec in *;
      unoption; simpl in *.
    destruct tpc as [F cid']; try discriminate;
      destruct ti as [cid'' I'' W'']; try discriminate.
    move/eqP in RPC; subst Apc.
    move: (COMPSWD pc).
    rewrite /Sym.sget PC => /(_ erefl).
    case COMP: (Abs.in_compartment_opt _ _) => [ac|] // _.
    rewrite /refine_registers /refine_memory /pointwise  in RREGS RMEMS.
    destruct (get AR r1) as [x1|] eqn:GET1;
      [| specialize RREGS with r1; rewrite R1W GET1 in RREGS; done].
    destruct (get AR r2) as [xold|] eqn:GET2;
      [| specialize RREGS with r2; rewrite OLD GET2 in RREGS; done].
    assert (EQ1 : x1 = w1) by
      (by specialize RREGS with r1;
          rewrite R1W GET1 /refine_reg_b in RREGS; move/eqP in RREGS);
      subst x1.
    destruct (get AM w1) as [x2|] eqn:GETM1;
      [|specialize RMEMS with w1; rewrite MEM1 GETM1 in RMEMS; done].
    evar (AR' : registers t);
      exists (AState (pc+1)%w AR' AM AC INTERNAL ac); split;
      subst AR'.
    + eapply Abs.step_load; try reflexivity.
      * unfold Abs.decode.
        unfold refine_memory,pointwise,refine_mem_loc_b in RMEMS;
          specialize RMEMS with pc; rewrite PC in RMEMS;
          destruct (get AM pc); [simpl|contradiction].
        move/eqP in RMEMS; subst; eassumption.
      * by apply (prove_permitted_now_in AGOOD SGOOD PC def_cid).
      * eassumption.
      * eassumption.
      * unfold upd; rewrite GET2; reflexivity.
    + constructor; simpl;
        try solve [done | eapply (prove_get_compartment_id SGOOD);
                          (* eassumption picked the wrong thing first *)
                          solve [ apply def_cid
                                | eassumption
                                | rewrite /Sym.sget /= PC; reflexivity ]].
      unfold upd; rewrite /refine_registers /pointwise in RREGS *; intros r2'.
      destruct (r2 == r2') eqn:EQ_r2; move/eqP in EQ_r2; [subst r2'|].
      * erewrite get_set_eq, get_upd_eq by eauto.
        by specialize RMEMS with w1;
           rewrite GETM1 MEM1 /refine_mem_loc_b /refine_reg_b in RMEMS *.
      * erewrite get_set_neq, get_upd_neq with (m' := regs') by eauto.
        apply RREGS.

  - (* Store *)
    undo1 NEXT rvec;
      destruct t1,t2,told; try discriminate;
      undo1 def_rvec cid;
      undo1 def_rvec WRITE_OK;
      undo1 NEXT mem';
      unfold Sym.can_execute,Sym.compartmentalization_rvec in *;
      unoption; simpl in *.
    destruct tpc as [F cid']; try discriminate;
      destruct ti as [cid'' I'' W'']; try discriminate.
    move/eqP in RPC; subst Apc.
    move: (COMPSWD pc).
    rewrite /Sym.sget PC => /(_ erefl).
    case COMP: (Abs.in_compartment_opt _ _) => [ac|] // _.
    rewrite /refine_registers /refine_memory /pointwise  in RREGS RMEMS.
    destruct (get AR r1) as [x1|] eqn:GET1;
      [| specialize RREGS with r1; rewrite R1W GET1 in RREGS; done].
    destruct (get AR r2) as [x2|] eqn:GET2;
      [| specialize RREGS with r2; rewrite R2W GET2 in RREGS; done].
    assert (EQ1 : x1 = w1) by
      (by specialize RREGS with r1;
          rewrite R1W GET1 /refine_reg_b in RREGS; move/eqP in RREGS);
      subst x1.
    assert (EQ1 : x2 = w2) by
      (by specialize RREGS with r2;
          rewrite R2W GET2 /refine_reg_b in RREGS; move/eqP in RREGS);
      subst x2.
    destruct (get AM w1) as [xold|] eqn:GETM1;
      [|specialize RMEMS with w1; rewrite OLD GETM1 in RMEMS; done].
    evar (AM' : memory t);
      exists (AState (pc+1)%w AR AM' AC INTERNAL ac); split;
      subst AM'.
    + eapply Abs.step_store; try reflexivity.
      * unfold Abs.decode.
        unfold refine_memory,pointwise,refine_mem_loc_b in RMEMS;
          specialize RMEMS with pc; rewrite PC in RMEMS;
          destruct (get AM pc); [simpl|contradiction].
        move/eqP in RMEMS; subst; eassumption.
      * by apply (prove_permitted_now_in AGOOD SGOOD PC def_cid).
      * eassumption.
      * eassumption.
      * { have ac_cid: get_compartment_id (SState mem reg pc@(Sym.PC F cid') extra) ac ?= cid.
            apply/eqP.
            by eapply prove_get_compartment_id; eauto.
          undo1 def_cid COND; unoption.
          rewrite in_setU.
          case/Abs.in_compartment_opt_correct/andP: COMP => ac_in_AC ?.
          case/orP: WRITE_OK => [/eqP ?|cid_in_W].
          - subst cid.
            case: SGOOD => [[SGMEM _] _].
            apply/orP. left.
            apply (get_compartment_id_in_compartment COMPSWD IDSWD IDSU ac_in_AC).
            by rewrite /Sym.sget OLD /=.
          - by rewrite (STWF _ _ ac_in_AC ac_cid) in_set /Sym.sget OLD /= cid_in_W orbT. }
      * unfold upd; rewrite GETM1; reflexivity.
    + assert (SAME :
                equilabeled
                  (SState mem  reg pc@(Sym.PC F cid')             extra)
                  (SState mem' reg (pc+1)%w@(Sym.PC INTERNAL cid) extra)). {
        rewrite /equilabeled; intros p.
        destruct (p == w1) eqn:EQ_w1; move/eqP in EQ_w1; [subst p|].
        - apply get_upd_eq in def_mem'; auto.
          by rewrite /Sym.sget OLD def_mem'.
        - apply get_upd_neq with (key' := p) in def_mem'; auto.
          rewrite /Sym.sget def_mem';
          case GET: (get mem p) => [[x L]|]; try by [].
          destruct (if      p == isolate_addr              then _
                    else if p == add_to_jump_targets_addr  then _
                    else if p == add_to_store_targets_addr then _
                    else None)
            as [[]|]; auto.
      }
      constructor; simpl; try done.
      * { unfold upd;
            rewrite /refine_memory /refine_mem_loc_b /pointwise in RMEMS *;
            intros p.
        destruct (p == w1) eqn:EQ_w1; move/eqP in EQ_w1; [subst p|].
        - erewrite get_set_eq, get_upd_eq by eauto using word_map_axioms.
          by specialize RMEMS with w1; rewrite GETM1 in RMEMS *.
        - erewrite get_set_neq, get_upd_neq with (m' := mem')
            by eauto using word_map_axioms.
          apply RMEMS. }
      * move=> c' Hc'.
        apply COMPSWD.
        move: def_mem' Hc'.
        rewrite !/Sym.sget /upd.
        case GET': (get mem w1) => [[x tg]|] // [<-].
        have [->|NE] := (c' =P w1); first by rewrite GET'.
        by rewrite get_set_neq.
      * move=> c' c'_in_AC.
        rewrite -(get_compartment_id_same _ SAME).
        by apply IDSWD.
      * move=> c1 c2 c1_in_AC c2_in_AC.
        rewrite -!(get_compartment_id_same _ SAME).
        by apply IDSU.
      * move=> c' c'_id c'_in_AC.
        rewrite -(get_compartment_id_same _ SAME) => Hc'_id.
        rewrite (JTWF _ _ c'_in_AC Hc'_id).
        apply/setP => p.
        rewrite !in_set.
        move: (SAME p).
        rewrite !/Sym.sget.
        case: (get mem p) => [[? ?]|]; case: (get mem' p) => [[? ?]|] //=;
        by [congruence | repeat case: (p =P _) => //= _; try congruence].
      * move=> c' c'_id c'_in_AC.
        rewrite -(get_compartment_id_same _ SAME) => Hc'_id.
        rewrite (STWF _ _ c'_in_AC Hc'_id).
        apply/setP => p.
        rewrite !in_set.
        move: (SAME p).
        rewrite !/Sym.sget.
        case: (get mem p) => [[? ?]|]; case: (get mem' p) => [[? ?]|] //=;
        by [congruence | repeat case: (p =P _) => //= _; try congruence].
      * rewrite /refine_previous_b; simpl.
        erewrite <-get_compartment_id_same; [|eassumption].
        (* eassumption picked the wrong thing first *)
        eapply prove_get_compartment_id; try apply def_cid; try eassumption;
          rewrite /Sym.sget /= PC; reflexivity.
      * have not_syscall : w1 \notin syscall_addrs.
        { apply/negP => contra.
          case/and3P: RSC => /eqP [].
          case/or4P: contra => [/eqP Hw1 | /eqP Hw1 | /eqP Hw1 | contra ] //;
          subst w1; by rewrite GETM1. }
        rewrite !in_cons !negb_or !(eq_sym w1) in not_syscall.
        case/and4P: not_syscall => /eqP N1 /eqP N2 /eqP N3 _.
        move: RSC.
        rewrite /refine_syscall_addrs_b !map_cons /=.
        do 3!rewrite (PartMaps.get_set_neq) //.
        by rewrite (PartMaps.get_upd_neq N1 def_mem')
                   (PartMaps.get_upd_neq N2 def_mem')
                   (PartMaps.get_upd_neq N3 def_mem').
      * rewrite /Sym.good_internal /= in RINT *.
        destruct extra as [next iT aJT aST].
        destruct iT,aJT,aST; auto.
        destruct RINT as [? [? [? RINT]]].
        repeat (split; [solve [auto]|]).
        intros p x c' I' W'; specialize (RINT p).
        { destruct (p == w1) eqn:EQ; move/eqP in EQ; subst.
          - apply get_upd_eq in def_mem'; auto; rewrite def_mem'.
            inversion 1; subst; eauto 2.
          - apply get_upd_neq with (key' := p) in def_mem'; auto.
            rewrite def_mem'; apply RINT. }
  - (* Jump *)
    undo1 NEXT rvec;
      destruct t1; try discriminate;
      undo1 def_rvec cid;
      unfold Sym.can_execute,Sym.compartmentalization_rvec in *;
      unoption; simpl in *.
    destruct tpc as [F cid']; try discriminate;
      destruct ti as [cid'' I W]; try discriminate.
    move/eqP in RPC; subst Apc.
    move: (COMPSWD pc).
    rewrite /Sym.sget PC => /(_ erefl).
    case COMP: (Abs.in_compartment_opt _ _) => [c|] // _.
    rewrite /refine_registers /pointwise in RREGS.
    destruct (get AR r) as [x|] eqn:GET;
      [| specialize RREGS with r; rewrite RW GET in RREGS; done].
    assert (EQ : x = w) by
      (by specialize RREGS with r;
          rewrite RW GET /refine_reg_b in RREGS; move/eqP in RREGS);
      subst x.
    evar (AR' : registers t);
      exists (AState w AR' AM AC JUMPED c); split;
      subst AR'.
    + eapply Abs.step_jump; try reflexivity.
      * unfold Abs.decode.
        unfold refine_memory,pointwise,refine_mem_loc_b in RMEMS;
          specialize RMEMS with pc; rewrite PC in RMEMS;
          destruct (get AM pc); [simpl|contradiction].
        move/eqP in RMEMS; subst; eassumption.
      * by apply (prove_permitted_now_in AGOOD SGOOD PC def_cid).
      * assumption.
    + constructor; simpl;
        try solve [done | eapply (prove_get_compartment_id SGOOD);
                          solve [ eassumption
                                | rewrite /Sym.sget /= PC; reflexivity ]].
  - (* Bnz *)
    undo1 NEXT rvec;
      destruct t1; try discriminate;
      undo1 def_rvec cid;
      unfold Sym.can_execute,Sym.compartmentalization_rvec in *;
      unoption; simpl in *.
    destruct tpc as [F cid']; try discriminate;
      destruct ti as [cid'' I W]; try discriminate.
    move/eqP in RPC; subst Apc.
    move: (COMPSWD pc).
    rewrite /Sym.sget PC => /(_ erefl).
    case COMP: (Abs.in_compartment_opt _ _) => [c|] // _.
    rewrite /refine_registers /pointwise in RREGS.
    destruct (get AR r) as [x|] eqn:GET;
      [| specialize RREGS with r; rewrite RW GET in RREGS; done].
    assert (EQ : x = w) by
      (by specialize RREGS with r;
          rewrite RW GET /refine_reg_b in RREGS; move/eqP in RREGS);
      subst x.
    evar (AR' : registers t);
      exists (AState (pc + (if w == 0 then 1 else Word.casts n))%w
                     AR' AM AC INTERNAL c); split;
      subst AR'.
    + eapply Abs.step_bnz; try reflexivity.
      * unfold Abs.decode.
        unfold refine_memory,pointwise,refine_mem_loc_b in RMEMS;
          specialize RMEMS with pc; rewrite PC in RMEMS;
          destruct (get AM pc); [simpl|contradiction].
        move/eqP in RMEMS; subst; eassumption.
      * eassumption.
      * by apply (prove_permitted_now_in AGOOD SGOOD PC def_cid).
    + constructor; simpl;
        try solve [done | eapply (prove_get_compartment_id SGOOD);
                          solve [ eassumption
                                | rewrite /Sym.sget /= PC; reflexivity ]].

  - (* Jal *)
    undo1 NEXT rvec;
      destruct t1; try discriminate;
      destruct told; try discriminate;
      undo1 def_rvec cid;
      undo1 NEXT regs';
      unfold Sym.can_execute,Sym.compartmentalization_rvec in *;
      unoption; simpl in *.
    destruct tpc as [F cid']; try discriminate;
      destruct ti as [cid'' I W]; try discriminate.
    move/eqP in RPC; subst Apc.
    move: (COMPSWD pc).
    rewrite /Sym.sget PC => /(_ erefl).
    case COMP: (Abs.in_compartment_opt _ _) => [c|] // _.
    rewrite /refine_registers /pointwise in RREGS.
    destruct (get AR r) as [x|] eqn:GET;
      [| specialize RREGS with r; rewrite RW GET in RREGS; done].
    assert (EQ : x = w) by
      (by specialize RREGS with r;
          rewrite RW GET /refine_reg_b in RREGS; move/eqP in RREGS);
      subst x.
    evar (AR' : registers t);
      exists (AState w AR' AM AC JUMPED c); split;
      subst AR'.
    + eapply Abs.step_jal; try reflexivity.
      * unfold Abs.decode.
        unfold refine_memory,pointwise,refine_mem_loc_b in RMEMS;
          specialize RMEMS with pc; rewrite PC in RMEMS;
          destruct (get AM pc); [simpl|contradiction].
        move/eqP in RMEMS; subst; eassumption.
      * by apply (prove_permitted_now_in AGOOD SGOOD PC def_cid).
      * assumption.
      * unfold upd; rewrite /refine_registers /pointwise in RREGS.
        match goal with |- context[get AR ?ra] =>
          (* This finds the type class instances *)
          case: (get AR ra) (RREGS ra) => {RREGS} RREGS;
            [reflexivity | rewrite OLD in RREGS; done]
        end.
    + constructor; simpl;
        try solve [done | eapply (prove_get_compartment_id SGOOD);
                          solve [ eassumption
                                | rewrite /Sym.sget /= PC; reflexivity ]].
      rewrite /refine_registers /pointwise in RREGS *; intros r'.
      destruct (ra == r') eqn:EQ_r'; move/eqP in EQ_r'; [subst r'|].
      * erewrite get_set_eq, get_upd_eq by eauto.
        by simpl.
      * erewrite get_set_neq, get_upd_neq with (m' := regs') by eauto.
        apply RREGS.
  - (* Syscall *)
    destruct (isolate_addr == pc) eqn:EQ;
      [ move/eqP in EQ; subst
      | clear EQ; destruct (add_to_jump_targets_addr == pc) eqn:EQ;
        [ move/eqP in EQ; subst
        | clear EQ; destruct (add_to_store_targets_addr == pc) eqn:EQ;
          [ move/eqP in EQ; subst
          | discriminate ]]];
      inversion GETCALL; subst;
      rewrite /Symbolic.run_syscall /Symbolic.transfer /sym_compartmentalization
              /Sym.compartmentalization_handler /Symbolic.sem
        in CALL;
      [ eapply isolate_refined              in CALL
      | eapply add_to_jump_targets_refined  in CALL
      | eapply add_to_store_targets_refined in CALL ];
      try constructor; try eassumption;
      try solve [by destruct tpc; try done; move/eqP in RPC; subst];
      destruct CALL as [ast' [STEP REFINE]];
      exists ast'; split; auto;
      [ eapply Abs.step_syscall with (sc := Abs.isolate              (t:=t))
      | eapply Abs.step_syscall with (sc := Abs.add_to_jump_targets  (t:=t))
      | eapply Abs.step_syscall with (sc := Abs.add_to_store_targets (t:=t)) ];
      try solve [reflexivity | eassumption];
      destruct tpc as []; try discriminate; move/eqP in RPC; subst;
      try match goal with |- context[get AM ?addr] =>
        rewrite /refine_memory /pointwise in RMEMS;
        specialize (RMEMS addr); rewrite PC in RMEMS;
        by destruct (get AM addr)
      end;
      rewrite /refine_syscall_addrs_b in RSC;
      case/and3P: RSC => /= RS1 RS2 /and3P [RS3 RS4 _];
      rewrite /Abs.get_syscall /= eq_refl;
      rewrite !in_cons /= in RS3 RS4.
      * done.
      * by destruct (isolate_addr == add_to_jump_targets_addr).
      * by destruct (isolate_addr == add_to_jump_targets_addr),
                    (isolate_addr == add_to_store_targets_addr),
                    (add_to_jump_targets_addr == add_to_store_targets_addr).
Qed.

End RefinementSA.
