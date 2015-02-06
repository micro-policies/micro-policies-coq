Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.ssrnat Ssreflect.seq Ssreflect.fintype MathComp.finset.
Require Import CoqUtils.ord CoqUtils.word CoqUtils.partmap.

Require Import lib.utils lib.partmap_utils common.types.
Require Import symbolic.symbolic.
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

Import Abs.Notations.
Import Abs.Hints.
Import Sym.EnhancedDo.

(* ssreflect exposes `succn' as a synonym for `S' *)
Local Notation II := Logic.I.

Context
  (mt           : machine_types)
  {ops          : machine_ops mt}
  {spec         : machine_ops_spec ops}
  {scr          : syscall_regs mt}
  {cmp_syscalls : compartmentalization_syscall_addrs mt}.

Notation word     := (mword mt).
Notation pc_tag   := (Sym.pc_tag mt).
Notation data_tag := (Sym.data_tag mt).
Notation sym_compartmentalization := (@Sym.sym_compartmentalization mt).

Notation spcatom := (atom word pc_tag).
Notation smatom  := (atom word data_tag).
Notation sratom  := (atom word unit).
Notation svalue  := (@vala word _).
Notation slabel  := (@taga word _).

Notation astate    := (@Abs.state mt).
Notation sstate    := (@Symbolic.state mt sym_compartmentalization).
Notation AState    := (@Abs.State mt).
Notation SState    := (@Symbolic.State mt sym_compartmentalization).
Notation SInternal := (@Sym.Internal mt).

Notation astep := Abs.step.
Notation sstep := Sym.step.

(* Avoiding some type class resolution problems *)

Arguments Sym.sget {_ _} s p : simpl never.
Arguments Sym.supd {_ _} s p tg : simpl never.

Canonical compartment_eqType :=
  Eval hnf in EqType (Abs.compartment mt) (Abs.compartment_eqMixin mt).

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

Definition refine_memory : memory mt -> Sym.memory mt -> Prop :=
  pointwise refine_mem_loc_b.

Definition refine_registers : registers mt -> Sym.registers mt -> Prop :=
  pointwise refine_reg_b.

Section WithSym.
Import Sym.

Definition get_compartment_id (sst : sstate)
                              (c   : Abs.compartment mt) : option word :=
  [pick cid |
    ((omap data_tag_compartment \o Sym.sget sst) @: Abs.address_space c) ==
    [set Some cid]].

Definition well_defined_compartments (sst : sstate)
                                     (C   : seq (Abs.compartment mt)) : Prop :=
  forall p, sget sst p -> Abs.in_compartment_opt C p.

Definition well_defined_ids (sst : sstate)
                            (C   : seq (Abs.compartment mt)) : Prop :=
  forall c, c \in C -> get_compartment_id sst c.

(* AAA: Does this imply disjointness? *)
Definition unique_ids (sst : sstate)
                      (C   : seq (Abs.compartment mt)) : Prop :=
  forall c1 c2,
    c1 \in C ->
    c2 \in C ->
    get_compartment_id sst c1 = get_compartment_id sst c2 ->
    c1 = c2.

Definition well_formed_targets (targets : Abs.compartment mt -> {set word})
                               (sources : data_tag _         -> {set word})
                               (sst     : sstate)
                               (C       : seq (Abs.compartment mt)) : Prop :=
  forall c cid,
    c \in C ->
    get_compartment_id sst c = Some cid ->
    targets c =
    [set p | oapp (fun s : {set word} => cid \in s) false
                  (omap sources (Sym.sget sst p)) ].

Definition well_formed_jump_targets : sstate -> seq (Abs.compartment mt) -> Prop :=
  well_formed_targets (fun c => Abs.jump_targets c) data_tag_incoming.

Definition well_formed_store_targets : sstate -> seq (Abs.compartment mt) -> Prop :=
  well_formed_targets (fun c => Abs.store_targets c) data_tag_writers.

End WithSym.

Definition refine_previous_b (sk : where_from) (prev : Abs.compartment mt)
                             (sst : sstate) : bool :=
  match Symbolic.pc sst with
    | _ @ (Sym.PC F cid) => (sk == F) &&
                            (get_compartment_id sst prev == Some cid)
  end.

Definition refine_syscall_addrs_b (AM : memory mt) (SM : Sym.memory mt) : bool :=
  [&& all (fun x => x \notin AM) syscall_addrs ,
      all (fun x => x \notin SM) syscall_addrs &
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
  split.
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

Lemma get_compartment_id_in_compartment_eq (C : seq (Abs.compartment mt)) sst c p :
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

Lemma get_compartment_id_in_compartment (C : seq (Abs.compartment mt)) sst c p :
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

Lemma in_compartment_get_compartment_id (C : seq (Abs.compartment mt)) sst c p :
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
  forall r, getm AR r = (svalue <$> getm SR r).
Proof.
  move=> AR SR REFINE r;
    rewrite /refine_registers /refine_reg_b /pointwise in REFINE.
  specialize REFINE with r.
  set oax := getm AR r in REFINE *; set osv := getm SR r in REFINE *;
    destruct oax as [|], osv as [[? []]|]; simpl in *; try done.
  by move/eqP in REFINE; subst.
Qed.

Lemma refined_mem_value : forall AM SM,
  refine_memory AM SM ->
  forall p, getm AM p = (svalue <$> getm SM p).
Proof.
  move=> AM SM REFINE p;
    rewrite /refine_memory /refine_mem_loc_b /pointwise in REFINE.
  specialize REFINE with p.
  set oax := getm AM p in REFINE *; set osv := getm SM p in REFINE *;
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
  set G := getm SM p; destruct G as [[wpairs ?]|]; subst; simpl; try done.

  move: (_ (ord_of_word wpairs)) (p + 1)%w => pairs.

  induction pairs as [|pairs]; simpl; [reflexivity | intros start].
  rewrite IHpairs; f_equal.
  rewrite /isolate_get_range.

  repeat (erewrite refined_mem_value; [|eassumption]).
  set G := getm SM start; destruct G as [[low ?]|]; subst; simpl; try done.
  by set G := getm SM (start + 1)%w; destruct G as [[high ?]|]; subst; simpl.
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
    destruct (getm AM a) as [w|],
             (getm (Symbolic.mem sst) a) as [[w' []]|] eqn:GET';
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
  by apply/Abs.in_compartment_opt_present; eassumption.
Qed.

Lemma supd_refine_memory AM sst sst' p c i w :
  Sym.supd sst p (Sym.DATA c i w) ?= sst' ->
  refine_memory AM (Symbolic.mem sst) ->
  refine_memory AM (Symbolic.mem sst').
Proof.
  case: sst => m r pc [? ? ? ?]; case: sst' => m' r' pc' [? ? ? ?].
  rewrite /Sym.supd /=.
  move=> UPD REF p'.
  case REP: (repm m p _) UPD => [m''|].
  - generalize (getm_rep REP p') => {REP} REP [<- _ _ _ _ _ _].
    rewrite REP.
    have [->|NE] := (p' =P p); last exact: REF.
    move: {REF} (REF p).
    case: (getm AM p) => [v1|];
    by case: (getm m p) => [[v2 [? ? ?]]|].
  - repeat case: (p =P _) => _ //=; move=> [<- _ _ _ _ _ _]; by apply REF.
Qed.

Lemma supd_refine_syscall_addrs_b AM sst sst' p l :
  Sym.supd sst p l ?= sst' ->
  refine_syscall_addrs_b AM (Symbolic.mem sst) ->
  refine_syscall_addrs_b AM (Symbolic.mem sst').
Proof.
  move=> UPD /and3P [Ha Hs Hu].
  apply/and3P; split=> // {Ha Hu}; apply/allP=> x /(allP Hs).
  rewrite !inE; case E: (getm _ _) => [//|] _.
  by rewrite (Sym.get_supd_none E UPD).
Qed.

Lemma sget_supd_good_internal (sst sst' : sstate) p c I1 W1 I2 W2 :
  (forall c', c' \in I2 :|: W2 -> (c' < Sym.next_id (Symbolic.internal sst))%ord) ->
  Sym.sget sst p ?= Sym.DATA c I1 W1 ->
  Sym.supd sst p (Sym.DATA c I2 W2) ?= sst' ->
  Sym.good_internal sst ->
  Sym.good_internal sst'.
Proof.
  move=> Hbounded_new Hsget Hsupd [Hbounded Hisolate].
  split.
  - move=> p' cid I W.
    rewrite (Sym.sget_supd Hsupd)
           -(Sym.supd_preserves_next_id Hsupd).
    have [_ {p'} [<- <- <- {cid I W}]|_] := p' =P p; last by apply Hbounded.
    move=> cid.
    rewrite -setUA in_setU1.
    case/orP => [/eqP -> {cid}|]; last by eauto.
    apply: (Hbounded _ _ _ _ Hsget).
    by rewrite in_setU in_setU1 eqxx.
  - move=> p' sc.
    rewrite !(Sym.sget_supd Hsupd).
    have [-> {p'}|_] := p' =P p;
    have [-> {sc}|_] := sc =P p => //=.
    + move=> sc_is_sc E.
      apply: (Hisolate p sc sc_is_sc).
      by rewrite Hsget /=.
    + move=> sc_is_sc E.
      apply: (Hisolate p' p sc_is_sc).
      by rewrite E Hsget.
    + move=> sc_is_sc E.
      by apply: (Hisolate p' sc sc_is_sc).
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
  { by rewrite GET (Sym.sget_supd UPD) eqxx. }
  rewrite (Sym.sget_supd UPD) (negbTE NE).
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
  rewrite (Sym.sget_supd UPD).
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

Lemma get_compartment_id_irrelevancies_bump m r pc si :
  get_compartment_id (SState m r pc (Sym.bump_next_id si)) =
  get_compartment_id (SState m r pc si).
Proof. by case: si. Qed.

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

Lemma well_formed_targets_augment (targets : Abs.compartment mt -> {set word})
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
    + rewrite subUset sub1set in_set (Sym.sget_supd UPD)
              eqxx /= SOURCES2 /= in_setU1 eqxx /=.
      apply/subsetP => p'.
      rewrite !in_set (Sym.sget_supd UPD).
      have [{p'} -> /=|//] := (p' =P p).
      by rewrite SOURCES2 /= in_setU1 eqxx.
    + apply/subsetP => p'.
      rewrite !in_set (Sym.sget_supd UPD).
      by have [{p'} ->|] := (p' =P p).
  - rewrite (WF _ _ c''_in_C ID').
    apply/eqP. rewrite eqEsubset. apply/andP.
    split; apply/subsetP => p';
    rewrite !in_set
            (Sym.sget_supd UPD);
    have [{p'} ->|] //= := (p' =P p);
    rewrite SOURCES2 GET /= SOURCES1 /= in_setU1; first by rewrite orbC => ->.
    case/orP => [/eqP E|//].
    rewrite E -?ID{cid'' E} in ID' *.
    by rewrite (UNIQUE _ _ c''_in_C c_in_C ID') eqxx in Hneq.
Qed.

Lemma well_formed_targets_same (targets : Abs.compartment mt -> {set word})
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
      rewrite !in_set (Sym.sget_supd UPD).
      have [{p'} -> /=|//] := (p' =P p).
      by rewrite SOURCES2 GET /= SOURCES1 /=.
    + apply/subsetP => p'.
      rewrite !in_set (Sym.sget_supd UPD).
      have [{p'} ->/=|//] := (p' =P p).
      by rewrite SOURCES2 /= GET /= SOURCES1 /=.
  - rewrite (WF _ _ c''_in_C ID').
    apply/eqP. rewrite eqEsubset. apply/andP.
    by split; apply/subsetP => p';
    rewrite !in_set
            (Sym.sget_supd UPD);
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
    Abs.semantics (Abs.add_to_jump_targets (mt:=mt)) ast ?= ast' /\
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
            (Abs.in_compartment_opt_sound ANOL IN_c) /=.
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
  destruct (getm AR syscall_arg1) as [Ap|]; destruct Lp; try done;
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
  destruct (getm AR ra) as [Apc'|]; destruct Lpc'; try done;
    move/eqP => ?; subst Apc'; simpl.

  have IN_pc' : pc' \in Aprev.
  { apply/(get_compartment_id_in_compartment COMPSWD IDSWD IDSU AIN).
    have [E|NE] := (pc' =P p).
    - subst pc'.
      rewrite (Sym.sget_supd_eq def_s') in def_xcIW0.
      rewrite def_xcIW /=.
      congruence.
    - by rewrite -(Sym.sget_supd_neq NE def_s') def_xcIW0 /=. }

  rewrite -(lock _) /= IN_pc' /= eq_refl.

  have IN_Jsys : pc' \in Abs.jump_targets c_sys. {
    rewrite eq_sym (negbTE NEQ_cid_sys) /= in COND.
    case/andP: IN_c => IC_c _.
    rewrite (JTWF _ _ IC_c R_c_sys) in_set.
    have [E|NE] := (pc' =P p).
    - subst pc'.
      rewrite def_xcIW /=.
      rewrite (Sym.sget_supd def_s') eqxx in def_xcIW0.
      move: def_xcIW0 => [? ? ?]; subst cid'' I_next W_next.
      by rewrite (in_setU1 cid_sys) eq_sym (negbTE NEQ_cid_sys) /= in NEXT.
    - by rewrite -(Sym.sget_supd_neq NE def_s') def_xcIW0 /=.
  }

  rewrite IN_Jsys. eexists; split; [reflexivity|].
  have /= E := Sym.supd_preserves_regs def_s'.
  subst R_next.

  constructor => //=.
  - exact: (supd_refine_memory def_s' RMEMS).
  - move=> p''.
    rewrite (sget_irrelevancies SR not_pc).
    move=> /(Sym.sget_supd_inv def_s')/COMPSWD.
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
  - have in_range : forall c' : [ordType of mword mt],
                      c' \in (cid' |: I'') :|: W'' ->
                      (c' < Sym.next_id
                              (Symbolic.internal
                                 (SState SM SR
                                         pc@(Sym.PC F cid')
                                         (SInternal Snext SiT SaJT SaST))))%ord.
    { move=> c'.
      case: SGINT => Hbounded Hisolate.
      rewrite -setUA in_setU1=> /orP [/eqP->{c'}|IN_IW].
      - apply: Hbounded; try eapply def_cid'.
        by rewrite in_setU in_setU1 eqxx.
      - apply: Hbounded; try apply def_xcIW.
        by rewrite -setUA in_setU1 IN_IW orbT.
    }
    exact: (sget_supd_good_internal in_range def_xcIW def_s').
Qed.

Theorem add_to_store_targets_refined : forall ast sst sst',
  Abs.good_state ast ->
  refine ast sst ->
  Sym.add_to_store_targets sst ?= sst' ->
  exists ast',
    Abs.semantics (Abs.add_to_store_targets (mt:=mt)) ast ?= ast' /\
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
            (Abs.in_compartment_opt_sound ANOL IN_c) /=.
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
  destruct (getm AR syscall_arg1) as [Ap|]; destruct Lp; try done;
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
  destruct (getm AR ra) as [Apc'|]; destruct Lpc'; try done;
    move/eqP=> ?; subst Apc'; simpl.

  have IN_pc' : pc' \in Aprev.
  { apply/(get_compartment_id_in_compartment COMPSWD IDSWD IDSU AIN).
    have [E|NE] := (pc' =P p).
    - subst pc'.
      rewrite (Sym.sget_supd_eq def_s') in def_xcIW0.
      rewrite def_xcIW /=.
      congruence.
    - by rewrite -(Sym.sget_supd_neq NE def_s') def_xcIW0 /=. }

  rewrite -(lock _) /= IN_pc' /= eq_refl.

  have IN_Jsys : pc' \in Abs.jump_targets c_sys. {
    rewrite eq_sym (negbTE NEQ_cid_sys) /= in COND.
    case/andP: IN_c => IC_c _.
    rewrite (JTWF _ _ IC_c R_c_sys) in_set.
    have [E|NE] := (pc' =P p).
    - subst pc'.
      rewrite def_xcIW /=.
      rewrite (Sym.sget_supd def_s') eqxx in def_xcIW0.
      by move: def_xcIW0 => [? ? ?]; subst cid'' I_next W_next.
    - by rewrite -(Sym.sget_supd_neq NE def_s') def_xcIW0 /=.
  }

  rewrite IN_Jsys. eexists; split; [reflexivity|].
  have /= E := Sym.supd_preserves_regs def_s'.
  subst R_next.

  constructor => //=.
  - exact: (supd_refine_memory def_s' RMEMS).
  - move=> p''.
    rewrite (sget_irrelevancies SR not_pc).
    move=> /(Sym.sget_supd_inv def_s')/COMPSWD.
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
  - have in_range : forall c',
                      c' \in I'' :|: (cid' |: W'') ->
                      (c' < Sym.next_id
                              (Symbolic.internal
                                 (SState SM SR
                                         pc@(Sym.PC F cid')
                                         (SInternal Snext SiT SaJT SaST))))%ord.
    { move=> c'.
      case: SGINT => Hbounded Hisolate.
      rewrite setUA (setUC I'') -setUA in_setU1=> /orP [/eqP->{c'}|IN_IW].
      - apply: Hbounded; try eapply def_cid'.
        by rewrite in_setU in_setU1 eqxx.
      - apply: Hbounded; try apply def_xcIW.
        by rewrite -setUA in_setU1 IN_IW orbT.
    }
    exact: (sget_supd_good_internal in_range def_xcIW def_s').
Qed.

Lemma retag_set_get_compartment_id_disjoint ok retag ps sst sst' c :
  Sym.retag_set ok retag ps sst = Some sst' ->
  [disjoint Abs.address_space c & ps] ->
  get_compartment_id sst' c = get_compartment_id sst c.
Proof.
  rewrite /Sym.retag_set /Sym.retag_one.
  move=> Hretag /pred0P Hdis.
  have {Hdis} Hdis: forall p, p \in Abs.address_space c -> p \notin ps.
  { move=> p Hin_c.
    apply/negP => Hin_ps.
    move: (Hdis p) => /=.
    by rewrite Hin_c Hin_ps. }
  elim: ps sst Hretag Hdis => [|p ps IH] sst /=; first congruence.
  case GET: (Sym.sget sst p) => [[cid' I' W']|] //=.
  case: (ok p cid' I' W') => //.
  case: (retag p cid' I' W') => [cid'' I'' W''] //.
  case UPD: (Sym.supd _ _ _) => [sst''|] //= Hretag Hdis.
  rewrite (IH sst'') //.
  - rewrite /get_compartment_id.
    apply eq_pick => cid //=.
    apply f_equal2 => // {cid}.
    apply eq_in_imset => p' /= p'_in_c.
    rewrite (Sym.sget_supd_neq _ UPD) // => ?. subst p'.
    move: (Hdis _ p'_in_c).
    by rewrite in_cons eqxx.
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

Lemma retag_set_get_compartment_id_same_ids ok retag ps sst sst' c :
  Sym.retag_set ok retag ps sst = Some sst' ->
  (forall p cid I W, p \in Abs.address_space c -> Sym.data_tag_compartment (retag p cid I W) = cid) ->
  get_compartment_id sst' c = get_compartment_id sst c.
Proof.
  rewrite /Sym.retag_set /Sym.retag_one.
  move=> Hretag_set Hretag.
  elim: ps sst Hretag_set => [|p ps IH] sst //=; first congruence.
  case GET: (Sym.sget _ _) => [[cid I W]|] //=.
  case: (ok _ _ _ _) => //.
  have [p_in_c|p_nin_c] := boolP (p \in Abs.address_space c).
  - move: Hretag => /(_ p cid I W p_in_c).
    case RETAG: (retag _ _ _ _) => [cid' I' W'] //= ->.
    case UPD: (Sym.supd _ _ _) => [sst''|] //= Hretag_set.
    rewrite (IH sst'' Hretag_set).
    apply eq_pick=> cid''.
    apply f_equal2=> // {cid''}.
    apply eq_imset=> p' //=.
    rewrite (Sym.sget_supd UPD).
    have [{p'} ->|//] := p' =P p.
    by rewrite GET.
  - case RETAG: (retag _ _ _ _) => [cid' I' W'] //=.
    case UPD: (Sym.supd _ _ _) => [sst''|] //= Hretag_set.
    rewrite (IH sst'' Hretag_set).
    apply eq_pick=> cid''.
    apply f_equal2=> // {cid''}.
    apply eq_in_imset=> p' p'_in_c //=.
    rewrite (Sym.sget_supd_neq _ UPD) // => ?.
    subst p'.
    by rewrite (negbTE p_nin_c) in p'_in_c.
Qed.

Lemma get_compartment_idP sst c cid :
  get_compartment_id sst c = Some cid <->
  [set (omap Sym.data_tag_compartment \o @Sym.sget _ cmp_syscalls sst) p | p in Abs.address_space c] =
  [set Some cid].
Proof.
  rewrite /get_compartment_id.
  split.
  - by case: pickP => [cid' /eqP Hcid' [<-] //|].
  - move=> ->.
    case: pickP => [cid' /eqP/set1_inj [->] //|/(_ cid)].
    by rewrite eqxx.
Qed.

Lemma get_compartment_id_set0 sst J S :
  get_compartment_id sst <<set0,J,S>> = None.
Proof.
  case H: (get_compartment_id _ _) => [cid|//].
  move/get_compartment_idP: H => /=.
  rewrite imset0=> /setP/(_ (Some cid)).
  by rewrite in_set0 in_set1 eqxx.
Qed.

Lemma get_compartment_id_setU1 sst (A J S : {set word}) p :
  get_compartment_id sst <<p |: A,J,S>> =
  if A == set0 then
    omap Sym.data_tag_compartment (Sym.sget sst p)
  else
    match omap Sym.data_tag_compartment (Sym.sget sst p), get_compartment_id sst <<A,J,S>> with
    | Some cid1, Some cid2 => if cid2 == cid1 then Some cid1 else None
    | _, _ => None
    end.
Proof.
  have [{A} ->|/set0Pn [p' p'_in_A]] := altP (A =P set0).
  { rewrite setU0 /get_compartment_id /= imset_set1.
    case: pickP => [cid /eqP/set1_inj <- //|] /=.
    case: (Sym.sget _ _) => [[cid ? ?]|] //= /(_ cid).
    by rewrite eqxx. }
  rewrite /get_compartment_id /= imsetU1 /=.
  case: (Sym.sget _ _) => [[cid I W]|] //=; last first.
  { case: pickP => [cid' /eqP/setP/(_ None)|//].
    by rewrite in_setU1 eqxx /= in_set1. }
  case: pickP => [cid' /eqP Hcid'|/(_ cid)].
  { move/setP/(_ (Some cid)): (Hcid').
    rewrite in_setU1 eqxx /= in_set1 => /esym/eqP [E]. subst cid'.
    case: pickP => [cid' /eqP Hcid''|/(_ cid) contra].
    - rewrite Hcid'' in Hcid'.
      by rewrite -[cid' == cid]/(Some cid' == Some cid) -in_set1 -Hcid' set22.
    - have: [set (omap Sym.data_tag_compartment ∘ Sym.sget sst) x | x in A] \subset [set Some cid]
        by rewrite -Hcid' subsetUr.
      rewrite subset1 contra {contra} /= imset_eq0 => /eqP/setP/(_ p').
      by rewrite p'_in_A in_set0. }
  case: pickP => [cid' /eqP ->|//].
  have [{cid'} ->|//] := cid' =P cid.
  by rewrite setUid eqxx.
Qed.

Lemma retag_one_get_compartment_id_new_id b ok retag p sst sst' (A J S : {set word}) cid' :
  Sym.retag_one ok retag sst p = Some sst' ->
  p \notin A ->
  (if b then
     forall cid I W, Sym.data_tag_compartment (retag p cid I W) = cid'
   else true) ->
  get_compartment_id sst' <<if b then p |: A else A,J,S>> =
  if b then
    match get_compartment_id sst <<A,J,S>> with
    | Some cid => if cid == cid' then Some cid'
                  else None
    | None => if A == set0 then Some cid' else None
    end
  else get_compartment_id sst <<A,J,S>>.
Proof.
  rewrite /Sym.retag_one.
  case Hsget: (Sym.sget _ _) => [[cid I W]|] //=.
  case: (ok p cid I W) => //=.
  case Hretag: (retag _ _ _ _) => [cid'' I' W'] /= Hsupd p_notin_A.
  case: b => [Hnew|_]; last first.
  { rewrite /get_compartment_id /=.
    apply eq_pick => p'.
    apply f_equal2 => // {p'}.
    apply eq_in_imset => p' /=.
    rewrite (Sym.sget_supd Hsupd).
    have [->|//] := altP (p' =P p).
    by rewrite (negbTE p_notin_A). }
  have := Hnew cid I W. rewrite Hretag /= => ?. subst cid''.
  rewrite get_compartment_id_setU1 (Sym.sget_supd Hsupd) eqxx /=.
  have [->|NE] := altP (A =P set0).
  { rewrite /get_compartment_id imset0.
    case: pickP => [cid'' /eqP/setP/(_ (Some cid''))|//].
    by rewrite in_set0 in_set1 eqxx. }
  suff ->: get_compartment_id sst' <<A,J,S>> = get_compartment_id sst <<A,J,S>> by [].
  rewrite /get_compartment_id /=.
  apply eq_pick=> cid''.
  apply f_equal2 => // {cid''}.
  apply eq_in_imset=> p' /=.
  rewrite (Sym.sget_supd Hsupd).
  have [->|//] := p' =P p.
  by rewrite (negbTE p_notin_A).
Qed.

Lemma retag_set_get_compartment_id_new_id ok retag (ps : seq word) sst sst' c cid' :
  uniq ps ->
  Sym.retag_set ok retag ps sst = Some sst' ->
  Abs.address_space c \subset ps ->
  Abs.address_space c != set0 ->
  (forall p cid I W,
     p \in Abs.address_space c ->
     Sym.data_tag_compartment (retag p cid I W) = cid') ->
  get_compartment_id sst' c = Some cid'.
Proof.
  case: c => [A J S] /= Huniq Hretag Hsubset Hnot0 Hnew.
  suff /(_ set0 A Hsubset _ Hnew):
    forall (A A' : {set word}),
      A' \subset ps ->
      [disjoint A & ps] ->
      (forall p cid I W,
         p \in A' ->
         Sym.data_tag_compartment (retag p cid I W) = cid') ->
      get_compartment_id sst' <<A' :|: A,J,S>> =
      if A' == set0 then get_compartment_id sst <<A,J,S>>
      else if A == set0 then Some cid'
      else match get_compartment_id sst <<A,J,S>> with
           | Some cid0 => if cid0 == cid' then Some cid' else None
           | None => None
           end.
  { rewrite setU0 eqxx (negbTE Hnot0) => -> //.
    rewrite disjoint_subset.
    apply/subsetP => ?.
    by rewrite in_set0. }
  move=> {A Hsubset Hnot0 Hnew} A A' Hsubset Hdis Hnew.
  elim: ps Huniq sst Hretag A A' Hsubset Hdis Hnew
        => [_ sst [<-] {sst'} A A'|
            p ps IH /= /andP [p_notin_ps Huniq] sst Hretag_set A A' /subsetP Hsubset Hdis Hnew].
  { have [{A'} ->|/set0Pn [p p_in_A'] /subsetP/(_ _ p_in_A') //] := altP (A' =P set0).
    by rewrite set0U. }
  move: (Hretag_set).
  rewrite /Sym.retag_set /=.
  case Hretag_one: (Sym.retag_one _ _ _ _) => [sst''|] //= Hretag_set'.
  have [->|A'_not_0] := altP (A' =P set0).
  { rewrite set0U. by eapply retag_set_get_compartment_id_disjoint; eauto. }
  have [p_in_A'|p_nin_A'] := boolP (p \in A').
  - rewrite -(setD1K p_in_A') (setUC [set p : word]) -setUA (IH _ sst'') {IH} //.
    + have ->: (p |: A == set0) = false.
      { apply/negbTE/eqP=> /setP/(_ p).
        by rewrite in_setU1 eqxx in_set0. }
      have:= (@retag_one_get_compartment_id_new_id (p \in A') ok retag p sst sst'' A J S cid' Hretag_one).
      move: (Hdis).
      rewrite p_in_A' disjoint_sym disjoint_subset => /subsetP/(_ p).
      rewrite in_cons eqxx=> /(_ erefl) p_notin_A /(_ p_notin_A) {p_notin_A} ->; last by eauto.
      have [->|_] := A =P set0.
      { rewrite get_compartment_id_set0 eqxx.
        by case: (A' :\ p == set0). }
      case: (A' :\ p == set0); case: (get_compartment_id _ _) => [cid|] //.
      have [/= _ {cid}|//] := cid =P cid'.
      by rewrite eqxx.
    + apply/subsetP=> p'.
      rewrite in_setD1 => /andP [p'_neq_p /Hsubset].
      by rewrite in_cons (negbTE p'_neq_p).
    + move: Hdis.
      rewrite !disjoint_subset=> /subsetP Hdis.
      apply/subsetP => p'.
      rewrite in_setU1=> /orP [/eqP -> {p'}//|/Hdis //].
      by rewrite /predC /in_mem /= => /norP [].
    + move=> p' cid I W.
      rewrite in_setD1=> /andP []. by auto.
  - rewrite (IH _ sst'') {IH} ?(negbTE A'_not_0) //.
    + have:= (@retag_one_get_compartment_id_new_id (p \in A') ok retag p sst sst'' A J S cid' Hretag_one).
      move: (Hdis).
      rewrite (negbTE p_nin_A') disjoint_sym disjoint_subset => /subsetP/(_ p).
      rewrite in_cons eqxx=> /(_ erefl) p_notin_A /(_ p_notin_A) {p_notin_A} ->; last by eauto.
      by have [|] := A =P set0.
    + apply/subsetP => p'.
      have [-> {p'}|p'_nin_p /Hsubset] := altP (p' =P p); first by rewrite (negbTE p_nin_A').
      by rewrite in_cons (negbTE p'_nin_p).
    + move: Hdis.
      rewrite !disjoint_subset=> /subsetP Hdis.
      apply/subsetP => p' /Hdis.
      by rewrite /predC /in_mem /= => /norP [].
Qed.

(* XXX: Not really needed anymore. *)
Lemma bounded_tags sst p c c' II WW :
  Sym.good_internal sst ->
  Sym.sget sst p = Some (Sym.DATA c II WW) ->
  c' \in II :|: WW ->
  (c' < (Sym.next_id (Symbolic.internal sst)))%ord.
Proof.
  move=> [Hbounded _] Hsget Hin.
  apply: Hbounded; try eapply Hsget.
  by rewrite -setUA in_setU1 Hin orbT.
Qed.

Theorem isolate_refined : forall ast sst sst',
  Abs.pc ast = isolate_addr ->
  Abs.good_state ast ->
  refine ast sst ->
  Sym.isolate sst = Some sst' ->
  exists ast',
    Abs.isolate_fn ast = Some ast' /\
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
    undo1 ISOLATE c';
    undo2 ISOLATE pA LpA; undo2 ISOLATE pJ LpJ; undo2 ISOLATE pS LpS;
    undo1 ISOLATE A'; undo1 ISOLATE NE_A';
    undo1 ISOLATE J';
    undo1 ISOLATE S';
    undo1 ISOLATE s';
    undo2 ISOLATE pc' Lpc';
    undoDATA ISOLATE i' cid_next I_next W_next;
    undo1 ISOLATE NEXT_EQ; move/eqP in NEXT_EQ; subst cid_next;
    undo1 ISOLATE NEXT;
    destruct s' as [SM' SR' pc'' si'];
    unoption.

  have /= ? := Sym.retag_set_preserves_pc def_s'.
  have /= ? := Sym.retag_set_preserves_regs def_s'.
  move: def_c'.
  rewrite /Sym.fresh' /=.
  have [//|NEQ [?]] := Snext =P monew.
  subst pc'' SR' c'.

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

  rewrite /Sym.good_pc_tag in SGPC; move: SGPC => [p [I [W def_cid]]].

  have SUBSET_A' : A' \subset Aprev. {
    apply/subsetP; intros a IN.
    have /(_ a) := (Sym.retag_set_forall (enum_uniq (mem (A' :|: J' :|: S'))) def_s').
    rewrite /Sym.do_ok (mem_enum (mem (A' :|: J' :|: S'))) !in_setU IN /= => /(_ erefl).
    move=> /= [c' [I' [W' [SGET /and3P [/eqP OK _ _]]]]]. subst c'.
    apply/(get_compartment_id_in_compartment COMPSWD IDSWD IDSU AIN).
    by rewrite SGET.
  }
  rewrite SUBSET_A'.

  have SUBSET_J' : J' \subset Aprev :|: Jprev. {
    apply/subsetP; move=> a IN.
    rewrite in_setU. apply/orP.
    have /(_ a) := Sym.retag_set_forall (enum_uniq (mem (A' :|: J' :|: S'))) def_s'.
    rewrite /Sym.do_retag /Sym.do_ok
            (mem_enum (mem (A' :|: J' :|: S'))) !in_setU IN orbT /=
            => /(_ erefl) [cid' [I' [W' [EQ /and3P [_ /orP [/eqP ? | cid'_in_I'] _]]]]].
    - subst cid'. left.
      apply/(get_compartment_id_in_compartment COMPSWD IDSWD IDSU AIN).
      by rewrite EQ.
    - right.
      have /= -> := JTWF _ _ AIN RPREV.
      by rewrite in_set EQ.
  }
  rewrite SUBSET_J'.

  have SUBSET_S' : S' \subset Aprev :|: Sprev. {
    apply/subsetP; move=> a IN.
    rewrite in_setU. apply/orP.
    have /(_ a) := Sym.retag_set_forall (enum_uniq (mem (A' :|: J' :|: S'))) def_s'.
    rewrite /Sym.do_retag /Sym.do_ok
            (mem_enum (mem (A' :|: J' :|: S'))) !in_setU IN orbT /=
            => /(_ erefl) [cid' [I' [W' [EQ /and3P [_ _ /orP [/eqP ? | cid'_in_S']]]]]].
    - subst cid'. left.
      apply/(get_compartment_id_in_compartment COMPSWD IDSWD IDSU AIN).
      by rewrite EQ.
    - right.
      have /= -> := STWF _ _ AIN RPREV.
      by rewrite in_set EQ.
  }
  rewrite SUBSET_S'.

  have IN_pc' : pc' \in Aprev.
  { apply/(get_compartment_id_in_compartment COMPSWD IDSWD IDSU AIN).
    have [OLD | [cid' [I' [W' [OLD []]]]]] :=
      Sym.retag_set_or_ok (enum_uniq (mem (A' :|: J' :|: S'))) def_s' pc';
      first by rewrite OLD def_xcIW.
    rewrite OLD RPREV {RPREV} /= def_xcIW /Sym.do_ok /Sym.do_retag.
    by have [IN /= /and3P [/eqP -> _ _] _|_ _ [-> _ _]] := boolP (pc' \in A'). }

  have DIFF : cid <> Snext. {
    intros ?; subst.
    eapply Sym.sget_lt_next in RINT; [simpl in RINT | eassumption].
    by rewrite Ord.leqxx in RINT.
  }

  have DIFF_sys : cid_sys <> Snext. {
    intros ?; subst.
    eapply Sym.sget_lt_next in RINT; [simpl in RINT | eassumption].
    by rewrite Ord.leqxx in RINT.
  }

  have NIN : pc' \notin A'. {
    apply/negP => IN.
    have /(_ pc') := Sym.retag_set_in_ok (enum_uniq (mem (A' :|: J' :|: S'))) def_s'.
    rewrite /Sym.do_ok /Sym.do_retag (mem_enum (mem (A' :|: J' :|: S'))) !in_setU IN /=
            => /(_ erefl) [cpc' [Ipc' [Wpc' [THEN [/and3P [/eqP ? _ _] NOW]]]]].
    subst cpc'.
    abstract congruence.
  }

  rewrite -(lock _) /= in_setD IN_pc' NIN /= eqxx.

  have c_sys_id : get_compartment_id (SState SM SR pc@(Sym.PC F cid)
                                             (SInternal Snext SiT SaJT SaST)) c_sys = Some cid_sys.
  { by rewrite (in_compartment_get_compartment_id COMPSWD IDSWD IDSU c_sys_in_AC pc_in_c_sys)
               def_LI. }

  have IN_Jsys : pc' \in Abs.jump_targets c_sys.
  { have /= -> := JTWF _ cid_sys c_sys_in_AC c_sys_id.
    rewrite in_set.
    have [->|[c' [I' [W' [-> /=]]]]] :=
      @Sym.retag_set_or_ok _ _ _ _ _ _ _ (enum_uniq (mem (A' :|: J' :|: S'))) def_s' pc';
      first by rewrite def_xcIW /=.
    rewrite def_xcIW /Sym.do_retag.
    case=> _ [_ E _].
    move: NEXT.
    rewrite E {E}.
    case: (pc' \in J') => //.
    by rewrite in_setU1 (introF (cid_sys =P Snext) DIFF_sys) /=. }

  rewrite IN_Jsys.

  eexists; split; [reflexivity|].

  (* Some useful lemmas *)

  move: (RSC) => /and3P; rewrite {1 2}/syscall_addrs => - [ANGET SNGET RSCU].
  move: (RSCU);
    rewrite /= !inE negb_or -!andbA => /and4P[] NEQiaJ NEQiaS NEQaJaS _.

  have NIN_sc : forall sc : word, sc \in syscall_addrs -> sc \notin A'.
  { move=> sc sc_is_sc.
    have {ANGET} ANGET := allP ANGET _ sc_is_sc.
    apply/negP; move=> IN.
    move: ASS => /allP/(_ _ AIN)/orP [UAS | SAS].
    - have IN' : sc \in Aprev by move/subsetP in SUBSET_A'; apply SUBSET_A'.
      move/forall_inP/(_ _ IN') in UAS.
      by rewrite inE UAS in ANGET.
    - rewrite /Abs.syscall_address_space /Abs.address_space /= in SAS.
      move: SAS => /existsP [sc' /and3P [NONE ELEM /eqP?]]; subst Aprev.
      move: SUBSET_A'; rewrite subset1; move => /orP [] /eqP?; subst A'.
      + move: IN_pc' IN NIN; rewrite !in_set1; move=> /eqP->.
        by rewrite eq_refl.
      + by rewrite in_set0 in IN. }

  have TSAI_s_s' : forall X : {set word},
                      [disjoint A' & X] ->
                      tags_subsets_add_1_in
                        X
                        Snext
                        (SState SM SR pc@(Sym.PC F cid)
                                (SInternal Snext SiT SaJT SaST))
                        (SState SM' SR pc@(Sym.PC F cid) si').
  {
    move=> X DJX a.
    have [a_in_sets|a_nin_sets] := boolP (a \in A' :|: J' :|: S').
    - have /(_ a) := Sym.retag_set_in (enum_uniq (mem (A' :|: J' :|: S'))) def_s'.
      rewrite -(mem_enum (mem (A' :|: J' :|: S')) a) in a_in_sets
        => /(_ a_in_sets) [cid' [I' [W' [Hold Hnew]]]].
      rewrite Hold Hnew /Sym.do_retag.
      split3.
      + move=> a_in_X.
        move/pred0P: DJX=> /(_ a) /=.
        by rewrite a_in_X andbT=> ->.
      + by case: (a \in J'); auto.
      + by case: (a \in S'); auto.
    - have /(_ a) := Sym.retag_set_not_in def_s'.
      rewrite -(mem_enum (mem (A' :|: J' :|: S')) a) in a_nin_sets
        => /(_ a_nin_sets) <-.
      by case: (Sym.sget _ _) => [[*]|]; auto. }

  have TSAI_s_s'' : forall X : {set word},
                       [disjoint A' & X] ->
                       tags_subsets_add_1_in
                         X
                         Snext
                         (SState SM SR pc@(Sym.PC F cid)
                                 (SInternal Snext SiT SaJT SaST))
                         (SState SM' SR pc'@(Sym.PC JUMPED cid_sys) (Sym.bump_next_id si'))
  by exact: TSAI_s_s'.

  have TSAI_rest : forall c,
                     c \in rem_all <<Aprev,Jprev,Sprev>> AC ->
                     tags_subsets_add_1_in
                       (Abs.address_space c)
                       Snext
                       (SState SM SR pc@(Sym.PC F cid)
                               (SInternal Snext SiT SaJT SaST))
                       (SState SM' SR pc'@(Sym.PC JUMPED cid_sys) (Sym.bump_next_id si')).
  {
    move=> c; rewrite in_rem_all => /andP [NEQ' IN] a.
    apply/TSAI_s_s''/pred0P=> p' /=.
    apply/negbTE/negP=> /andP [p'_in_A' p'_in_c].
    suff contra: c = <<Aprev,Jprev,Sprev>> by rewrite contra eqxx in NEQ'.
    move/Abs.non_overlappingP: ANOL.
    apply=> //.
    apply/negP=> /pred0P/(_ p') /=.
    rewrite p'_in_c /=.
    by move/subsetP: SUBSET_A' => /(_ _ p'_in_A') ->. }

  have RC_rest : forall c,
                   c \in rem_all <<Aprev,Jprev,Sprev>> AC ->
                   get_compartment_id
                     (SState SM' SR pc'@(Sym.PC JUMPED cid_sys) (Sym.bump_next_id si')) c =
                   get_compartment_id
                     (SState SM SR pc@(Sym.PC F cid) (SInternal Snext SiT SaJT SaST)) c.
  {
    move=> c.
    rewrite in_rem_all=> /andP [c_neq_prev c_in_AC].
    apply (retag_set_get_compartment_id_same_ids def_s')=> p' cid' I' W' p'_in_c.
    rewrite /Sym.do_retag.
    have [p'_in_A'|//] := boolP (p' \in A').
    suff E : c = <<Aprev,Jprev,Sprev>> by rewrite E eqxx in c_neq_prev.
    move/Abs.non_overlappingP: ANOL.
    apply=> //.
    apply/pred0P => /(_ p').
    rewrite /predI /= p'_in_c /=.
    by move/subsetP/(_ _ p'_in_A'): SUBSET_A'=> ->.
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
    move/allP in ASS.
    by move: (ASS _ AIN) => /orP [UAS | SAS].
  }

  have NOT_USER_c_sys : ~ Abs.user_address_space AM c_sys. {
    move=> /forall_inP UAS.
    specialize (UAS _ pc_in_c_sys); simpl in UAS.
    rewrite -(lock eq) in IS_ISOLATE; subst.

    by rewrite /= inE UAS in ANGET.
  }

  have SYSCALL_c_sys : Abs.syscall_address_space AM c_sys. {
    move/allP in ASS.
    by move: (ASS _ c_sys_in_AC) => /orP [UAS | SAS].
  }

  have DIFF_prev_c_sys : <<Aprev,Jprev,Sprev>> <> c_sys
    by move=> ?; subst.

  have R_c_sys' : get_compartment_id
                    (SState SM' SR pc'@(Sym.PC JUMPED cid_sys) (Sym.bump_next_id si'))
                    c_sys
                    ?= cid_sys.
  {
    rewrite -RC_rest in c_sys_id => //.
    rewrite in_rem_all; apply/andP; split=> //.
    by rewrite eq_sym; apply/eqP.
  }

  have Hres: get_compartment_id (SState SM' SR pc'@(Sym.PC JUMPED cid_sys) (Sym.bump_next_id si'))
                                <<Aprev :\: A',Jprev,Sprev>> = Some cid.
  { rewrite (get_compartment_id_irrelevancies SR pc@(Sym.PC F cid))
            get_compartment_id_irrelevancies_bump.
    rewrite (retag_set_get_compartment_id_same_ids def_s') //; last first.
    { rewrite /= => p' cid' _ _.
      by rewrite in_setD => /andP [/negbTE -> ?]. }
    have := (@get_compartment_id_subset _ _ _ _ pc' _ _ RPREV).
    apply.
    - by rewrite in_setD IN_pc' NIN.
    - by rewrite subDset subsetUr. }

  have Hnew: get_compartment_id (SState SM' SR pc'@(Sym.PC JUMPED cid_sys) (Sym.bump_next_id si'))
                                <<A',J',S'>> = Some Snext.
  { rewrite (get_compartment_id_irrelevancies SR pc@(Sym.PC F cid))
            get_compartment_id_irrelevancies_bump.
    have := (@retag_set_get_compartment_id_new_id _ _ _ _ _ <<A',J',S'>>
                                                  Snext (enum_uniq (mem (A' :|: J' :|: S'))) def_s' _ NE_A').
    apply.
    - apply/subsetP => p'.
      by rewrite (mem_enum (mem (A' :|: _ :|: _))) !in_setU=> ->.
    - by rewrite /Sym.do_retag=> ? ? ? ? /= ->. }

(* REFINEMENT *)

  constructor=> //=.
  - move/id in def_s'.
    eapply retag_set_preserves_memory_refinement in def_s'; last eassumption.
    assumption.
  - move=> p' Hp'.
    move: (COMPSWD p').
    rewrite (Sym.retag_set_preserves_definedness def_s' p') => /(_ Hp') {Hp'}.
    case Hp': (Abs.in_compartment_opt AC p') => [cp'|] // _.
    case/Abs.in_compartment_opt_correct/andP: Hp'.
    have [{cp'} ->|NE] := altP (cp' =P <<Aprev,Jprev,Sprev>>) => cp'_in_AC p'_in_cp'.
    { rewrite /= in_setD p'_in_cp' andbT.
      by case: (p' \in A'). }
    apply (@Abs.in_compartment_opt_is_some _ _ _ cp').
    by rewrite /Abs.in_compartment !in_cons in_rem_all NE cp'_in_AC !orbT /=.
  - move=> c'.
    rewrite !in_cons => /or3P [/eqP -> {c'}|/eqP -> {c'}|c'_in].
    + by rewrite Hres.
    + by rewrite Hnew.
    + rewrite RC_rest //.
      apply IDSWD.
      rewrite in_rem_all in c'_in.
      by case/andP: c'_in.
  - move=> c1 c2.
    rewrite !in_cons /=
            => /or3P [/eqP -> {c1}|/eqP -> {c1}|c1_in_AC]
               /or3P [/eqP -> {c2}|/eqP -> {c2}|c2_in_AC] //=;
    rewrite ?Hres ?Hnew; try congruence.
    + rewrite -RPREV RC_rest // => NEW.
      rewrite in_rem_all in c2_in_AC.
      case/andP: c2_in_AC => [/eqP ? ?].
      by apply IDSU in NEW; try congruence.
    + rewrite RC_rest // /get_compartment_id.
      case: pickP => [cid'' /eqP Hcid''|]//= [E].
      subst cid''.
      move: (set11 (Some Snext)).
      rewrite -Hcid'' => /imsetP /= [p' _].
      case GETp': (Sym.sget _ _) => [[cp' Ip' Wp']|] //= [E].
      subst cp'.
      move: (Sym.sget_lt_next RINT GETp') => /=.
      by rewrite Ord.leqxx.
    + rewrite -RPREV RC_rest // => NEW.
      rewrite in_rem_all in c1_in_AC.
      case/andP: c1_in_AC => [/eqP ? ?].
      by apply IDSU in NEW; try congruence.
    + rewrite RC_rest // /get_compartment_id.
      case: pickP => [cid'' /eqP Hcid''|]//= [E].
      subst cid''.
      move: (set11 (Some Snext)).
      rewrite -Hcid'' => /imsetP /= [p' _].
      case GETp': (Sym.sget _ _) => [[cp' Ip' Wp']|] //= [E].
      subst cp'.
      move: (Sym.sget_lt_next RINT GETp') => /=.
      by rewrite Ord.leqxx.
    + rewrite !RC_rest //.
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
      move: TSAI_s_s'' => /(_ (Aprev :\: A') DJ a).
      case: (Sym.sget _ a) => [[cid1 I1 W1]|] //=;
        [|by case: (Sym.sget _ a) => [[]|] //].
      case: (Sym.sget _ a) => [[cid2 I2 W2]|] //=.
      move=> [cid_eq [OR_Is OR_Ws]].
      case: OR_Is => [-> // | <-{I2}].
      rewrite inE in_set1.
      suff: cid != Snext by move=> /negbTE-> //.
      suff: (cid < Snext)%ord by apply: contra => /eqP ->; rewrite Ord.leqxx.
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
      have [p'_in_sets|p'_nin_sets] := boolP (p' \in (A' :|: J' :|: S')).
      * have /(_ p') := Sym.retag_set_in (enum_uniq (mem (A' :|: J' :|: S'))) def_s'.
        move: p'_in_sets.
        rewrite -(mem_enum (mem (A' :|: J' :|: S')))
                => H /(_ H) {H} [cid' [I' [W' [Hold']]]].
        rewrite /Sym.sget /= /Sym.do_retag => -> /=.
        case: (p' \in J'); first by rewrite in_setU1 eqxx.
        apply/esym/negbTE/negP=> Snext_in_I'.
        have /(_ Snext)/= := bounded_tags RINT Hold'.
        by rewrite in_setU Snext_in_I' Ord.leqxx => /(_ erefl).
      * have /(_ p') := Sym.retag_set_not_in def_s'.
        move: (p'_nin_sets).
        rewrite -(mem_enum (mem (A' :|: J' :|: S'))) {2 3}/Sym.sget /= => H /(_ H) {H} <-.
        rewrite !in_setU !negb_or -andbA in p'_nin_sets.
        case/and3P: p'_nin_sets => _ /negbTE -> _.
        case Hold': (Sym.sget _ _)=> [[cid' I' W']|//] /=.
        apply/esym/negbTE/negP=> Snext_in_I'.
        have /(_ Snext)/= := bounded_tags RINT Hold'.
        by rewrite in_setU Snext_in_I' Ord.leqxx => /(_ erefl).
    + move/(_ c' c'_in_AC') in RC_rest.
      rewrite RC_rest => GCI_cid'.
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
      suff: (cid' < Snext)%ord by apply: contra => /eqP ->; rewrite Ord.leqxx.
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
      move: TSAI_s_s'' => /(_ (Aprev :\: A') DJ a).
      case: (Sym.sget _ a) => [[cid1 I1 W1]|] //=;
        [|by case: (Sym.sget _ a) => [[]|] //].
      case: (Sym.sget _ a) => [[cid2 I2 W2]|] //=.
      move=> [cid_eq [OR_Is OR_Ws]].
      case: OR_Ws => [-> // | <-{W2}].
      rewrite inE in_set1.
      suff: cid != Snext by move=> /negbTE-> //.
      suff: (cid < Snext)%ord by apply: contra => /eqP ->; rewrite Ord.leqxx.
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
      have [p'_in_sets|p'_nin_sets] := boolP (p' \in (A' :|: J' :|: S')).
      * have /(_ p') := Sym.retag_set_in (enum_uniq (mem (A' :|: J' :|: S'))) def_s'.
        move: p'_in_sets.
        rewrite -(mem_enum (mem (A' :|: J' :|: S')))
                => H /(_ H) {H} [cid' [I' [W' [Hold']]]].
        rewrite /Sym.sget /= /Sym.do_retag => -> /=.
        case: (p' \in S'); first by rewrite in_setU1 eqxx.
        apply/esym/negbTE/negP=> Snext_in_W'.
        have /(_ Snext)/= := bounded_tags RINT Hold'.
        by rewrite in_setU Snext_in_W' orbT Ord.leqxx => /(_ erefl).
      * have /(_ p') := Sym.retag_set_not_in def_s'.
        move: (p'_nin_sets).
        rewrite -(mem_enum (mem (A' :|: J' :|: S'))) {2 3}/Sym.sget /= => H /(_ H) {H} <-.
        rewrite !in_setU !negb_or -andbA in p'_nin_sets.
        case/and3P: p'_nin_sets => _ _ /negbTE ->.
        case Hold': (Sym.sget _ _)=> [[cid' I' W']|//] /=.
        apply/esym/negbTE/negP=> Snext_in_W'.
        have /(_ Snext)/= := bounded_tags RINT Hold'.
        by rewrite in_setU Snext_in_W' orbT Ord.leqxx => /(_ erefl).
    + move/(_ c' c'_in_AC') in RC_rest.
      rewrite RC_rest => GCI_cid'.
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
      suff: (cid' < Snext)%ord by apply: contra => /eqP ->; rewrite Ord.leqxx.
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
    case/and3P: RSC => ? Hs ?.
    apply/and3P.
    split=> //; apply/allP=> x /(allP Hs); rewrite inE.
    by rewrite -(Sym.retag_set_preserves_get_definedness def_s') /= inE.
  - have := (Sym.retag_set_preserves_good_internal _ RINT def_s').
    apply => //.
    + move=> sc cid' I' W' sc_is_sc.
      rewrite /Sym.do_retag.
      by rewrite (negbTE (NIN_sc _ sc_is_sc)).
    + move=> p' cid' I' W'.
      rewrite /Sym.do_retag /= !inE.
      by case: (p' \in A'); rewrite eqxx ?orbT.
    + move=> p' cid' I' W'.
      rewrite /Sym.do_retag /= -{3}(setUid [set Snext])
             -[[set Snext] :|: _ :|: _]setUA [_ :|: (_ :|: _)]setUC -setUA.
      apply setUSS.
      * by case: (p' \in J'); rewrite ?subxx ?subsetUr.
      * by case: (p' \in S'); rewrite ?subxx ?subsetUr.
Qed.

Lemma prove_permitted_now_in AR AM AC Ask Aprev mem reg pc extra c i cid cid' cid'' II WW F :
  let ast := AState pc AR AM AC Ask Aprev in
  let sst := SState mem reg pc@(Sym.PC F cid') extra in
  Abs.good_state ast ->
  Sym.good_state sst ->
  getm (Symbolic.mem sst) (vala (Symbolic.pc sst)) ?= i@(Sym.DATA cid'' II WW) ->
  (do! guard (cid'' == cid') || (F == JUMPED) && (cid' \in II);
   Some cid'') ?= cid ->
  refine_previous_b (Abs.step_kind ast) (Abs.previous ast) sst ->
  well_defined_compartments sst AC ->
  well_defined_ids sst AC ->
  unique_ids sst AC ->
  well_formed_jump_targets sst AC ->
  Abs.in_compartment_opt (Abs.compartments ast) (vala (Symbolic.pc sst)) ?= c ->
  Abs.permitted_now_in (Abs.compartments ast) (Abs.step_kind ast) (Abs.previous ast) (vala (Symbolic.pc sst)) ?= c.
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
  getm mem pc ?= i@(Sym.DATA cid'' II WW) ->
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
          destruct (getm AM pc); [simpl|contradiction].
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
    evar (AR' : registers mt);
      exists (AState (pc+1)%w AR' AM AC INTERNAL c); split;
      subst AR'.
    + eapply Abs.step_const; try reflexivity.
      * unfold Abs.decode.
        unfold refine_memory,pointwise,refine_mem_loc_b in RMEMS;
          specialize RMEMS with pc; rewrite PC in RMEMS;
          destruct (getm AM pc); [simpl|contradiction].
        move/eqP in RMEMS; subst; eassumption.
      * by apply (prove_permitted_now_in AGOOD SGOOD PC def_cid).
      * unfold updm; rewrite /refine_registers /pointwise in RREGS;
          specialize RREGS with r.
        case: (getm AR r) RREGS => [a|] RREGS;
          [reflexivity | rewrite OLD in RREGS; done].
    + constructor; simpl;
        try solve [done | eapply (prove_get_compartment_id SGOOD);
                          solve [ eassumption
                                | rewrite /Sym.sget /= PC; reflexivity ]].
      rewrite /refine_registers /pointwise in RREGS *; intros r'.
      rewrite getm_set.
      destruct (r' == r) eqn:EQ_r; move/eqP in EQ_r; [subst r'|].
      * erewrite getm_upd_eq by eauto.
        by unfold refine_reg_b.
      * erewrite getm_upd_neq with (m' := regs') by eauto.
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
    destruct (getm AR r1) as [x1|] eqn:GET1;
      [| specialize RREGS with r1; rewrite R1W GET1 in RREGS; done].
    destruct (getm AR r2) as [x2|] eqn:GET2;
      [| specialize RREGS with r2; rewrite OLD GET2 in RREGS; done].
    evar (AR' : registers mt);
      exists (AState (pc+1)%w AR' AM AC INTERNAL c); split;
      subst AR'.
    + eapply Abs.step_mov; try reflexivity.
      * unfold Abs.decode.
        unfold refine_memory,pointwise,refine_mem_loc_b in RMEMS;
          specialize RMEMS with pc; rewrite PC in RMEMS;
          destruct (getm AM pc); [simpl|contradiction].
        move/eqP in RMEMS; subst; eassumption.
      * by apply (prove_permitted_now_in AGOOD SGOOD PC def_cid).
      * eassumption.
      * unfold updm; rewrite GET2; reflexivity.
    + constructor; simpl;
        try solve [done | eapply (prove_get_compartment_id SGOOD);
                          solve [ eassumption
                                | rewrite /Sym.sget /= PC; reflexivity ]].
      rewrite /refine_registers /pointwise in RREGS *; intros r2'.
      rewrite getm_set.
      destruct (r2' == r2) eqn:EQ_r2; move/eqP in EQ_r2; [subst r2'|].
      * erewrite getm_upd_eq by eauto.
        by specialize RREGS with r1; rewrite GET1 R1W /refine_reg_b in RREGS *.
      * erewrite getm_upd_neq with (m' := regs') by eauto.
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
    destruct (getm AR r1) as [x1|] eqn:GET1;
      [| specialize RREGS with r1; rewrite R1W GET1 in RREGS; done].
    destruct (getm AR r2) as [x2|] eqn:GET2;
      [| specialize RREGS with r2; rewrite R2W GET2 in RREGS; done].
    destruct (getm AR r3) as [x3|] eqn:GET3;
      [| specialize RREGS with r3; rewrite OLD GET3 in RREGS; done].
    evar (AR' : registers mt);
      exists (AState (pc+1)%w AR' AM AC INTERNAL c); split;
      subst AR'.
    + eapply Abs.step_binop; try reflexivity.
      * unfold Abs.decode.
        unfold refine_memory,pointwise,refine_mem_loc_b in RMEMS;
          specialize RMEMS with pc; rewrite PC in RMEMS;
          destruct (getm AM pc); [simpl|contradiction].
        move/eqP in RMEMS; subst; eassumption.
      * by apply (prove_permitted_now_in AGOOD SGOOD PC def_cid).
      * eassumption.
      * eassumption.
      * unfold updm; rewrite GET3; reflexivity.
    + constructor; simpl;
        try solve [done | eapply (prove_get_compartment_id SGOOD);
                          solve [ eassumption
                                | rewrite /Sym.sget /= PC; reflexivity ]].
      unfold updm; rewrite /refine_registers /pointwise in RREGS *; intros r3'.
      rewrite getm_set.
      destruct (r3' == r3) eqn:EQ_r3; move/eqP in EQ_r3; [subst r3'|].
      * erewrite getm_upd_eq by eauto.
        { unfold refine_reg_b. apply/eqP; f_equal.
          - by specialize RREGS with r1;
               rewrite GET1 R1W /refine_reg_b in RREGS *; apply/eqP.
          - by specialize RREGS with r2;
               rewrite GET2 R2W /refine_reg_b in RREGS *; apply/eqP. }
      * erewrite getm_upd_neq with (m' := regs') by eauto.
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
    destruct (getm AR r1) as [x1|] eqn:GET1;
      [| specialize RREGS with r1; rewrite R1W GET1 in RREGS; done].
    destruct (getm AR r2) as [xold|] eqn:GET2;
      [| specialize RREGS with r2; rewrite OLD GET2 in RREGS; done].
    assert (EQ1 : x1 = w1) by
      (by specialize RREGS with r1;
          rewrite R1W GET1 /refine_reg_b in RREGS; move/eqP in RREGS);
      subst x1.
    destruct (getm AM w1) as [x2|] eqn:GETM1;
      [|specialize RMEMS with w1; rewrite MEM1 GETM1 in RMEMS; done].
    evar (AR' : registers mt);
      exists (AState (pc+1)%w AR' AM AC INTERNAL ac); split;
      subst AR'.
    + eapply Abs.step_load; try reflexivity.
      * unfold Abs.decode.
        unfold refine_memory,pointwise,refine_mem_loc_b in RMEMS;
          specialize RMEMS with pc; rewrite PC in RMEMS;
          destruct (getm AM pc); [simpl|contradiction].
        move/eqP in RMEMS; subst; eassumption.
      * by apply (prove_permitted_now_in AGOOD SGOOD PC def_cid).
      * eassumption.
      * eassumption.
      * unfold updm; rewrite GET2; reflexivity.
    + constructor; simpl;
        try solve [done | eapply (prove_get_compartment_id SGOOD);
                          (* eassumption picked the wrong thing first *)
                          solve [ apply def_cid
                                | eassumption
                                | rewrite /Sym.sget /= PC; reflexivity ]].
      unfold updm; rewrite /refine_registers /pointwise in RREGS *; intros r2'.
      rewrite getm_set.
      destruct (r2' == r2) eqn:EQ_r2; move/eqP in EQ_r2; [subst r2'|].
      * erewrite getm_upd_eq by eauto.
        by specialize RMEMS with w1;
           rewrite GETM1 MEM1 /refine_mem_loc_b /refine_reg_b in RMEMS *.
      * erewrite getm_upd_neq with (m' := regs') by eauto.
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
    destruct (getm AR r1) as [x1|] eqn:GET1;
      [| specialize RREGS with r1; rewrite R1W GET1 in RREGS; done].
    destruct (getm AR r2) as [x2|] eqn:GET2;
      [| specialize RREGS with r2; rewrite R2W GET2 in RREGS; done].
    assert (EQ1 : x1 = w1) by
      (by specialize RREGS with r1;
          rewrite R1W GET1 /refine_reg_b in RREGS; move/eqP in RREGS);
      subst x1.
    assert (EQ1 : x2 = w2) by
      (by specialize RREGS with r2;
          rewrite R2W GET2 /refine_reg_b in RREGS; move/eqP in RREGS);
      subst x2.
    destruct (getm AM w1) as [xold|] eqn:GETM1;
      [|specialize RMEMS with w1; rewrite OLD GETM1 in RMEMS; done].
    evar (AM' : memory mt);
      exists (AState (pc+1)%w AR AM' AC INTERNAL ac); split;
      subst AM'.
    + eapply Abs.step_store; try reflexivity.
      * unfold Abs.decode.
        unfold refine_memory,pointwise,refine_mem_loc_b in RMEMS;
          specialize RMEMS with pc; rewrite PC in RMEMS;
          destruct (getm AM pc); [simpl|contradiction].
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
      * unfold updm; rewrite GETM1; reflexivity.
    + assert (SAME :
                equilabeled
                  (SState mem  reg pc@(Sym.PC F cid')             extra)
                  (SState mem' reg (pc+1)%w@(Sym.PC INTERNAL cid) extra)). {
        rewrite /equilabeled; intros p.
        destruct (p == w1) eqn:EQ_w1; move/eqP in EQ_w1; [subst p|].
        - apply getm_upd_eq in def_mem'; auto.
          by rewrite /Sym.sget OLD def_mem'.
        - apply getm_upd_neq with (key' := p) in def_mem'; auto.
          rewrite /Sym.sget def_mem';
          case GET: (getm mem p) => [[x L]|]; try by [].
          destruct (if      p == isolate_addr              then _
                    else if p == add_to_jump_targets_addr  then _
                    else if p == add_to_store_targets_addr then _
                    else None)
            as [[]|]; auto.
      }
      constructor; simpl; try done.
      * { unfold updm;
            rewrite /refine_memory /refine_mem_loc_b /pointwise in RMEMS *;
            intros p.
        rewrite getm_set.
        destruct (p == w1) eqn:EQ_w1; move/eqP in EQ_w1; [subst p|].
        - erewrite getm_upd_eq by eauto.
          by specialize RMEMS with w1; rewrite GETM1 in RMEMS *.
        - erewrite getm_upd_neq with (m' := mem') by eauto.
          apply RMEMS. }
      * move=> c' Hc'.
        apply COMPSWD.
        move: def_mem' Hc'.
        rewrite !/Sym.sget /updm.
        case GET': (getm mem w1) => [[x tg]|] // [<-].
        rewrite getm_set.
        by have [->|NE //] := (c' =P w1); rewrite GET'.
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
        case: (getm mem p) => [[? ?]|]; case: (getm mem' p) => [[? ?]|] //=;
        by [congruence | repeat case: (p =P _) => //= _; try congruence].
      * move=> c' c'_id c'_in_AC.
        rewrite -(get_compartment_id_same _ SAME) => Hc'_id.
        rewrite (STWF _ _ c'_in_AC Hc'_id).
        apply/setP => p.
        rewrite !in_set.
        move: (SAME p).
        rewrite !/Sym.sget.
        case: (getm mem p) => [[? ?]|]; case: (getm mem' p) => [[? ?]|] //=;
        by [congruence | repeat case: (p =P _) => //= _; try congruence].
      * rewrite /refine_previous_b; simpl.
        erewrite <-get_compartment_id_same; [|eassumption].
        (* eassumption picked the wrong thing first *)
        eapply prove_get_compartment_id; try apply def_cid; try eassumption;
          rewrite /Sym.sget /= PC; reflexivity.
      * have not_syscall : w1 \notin syscall_addrs.
        { apply/negP => contra; case/and3P: RSC => /allP /(_ _ contra).
          by rewrite inE GETM1. }
        case/and3P: RSC => [Ha Hs Hu]; apply/and3P; split=> //.
          apply/allP=> x x_in_sc; rewrite inE getm_set; move: x_in_sc not_syscall.
          by have [{x}-> ->|_ /(allP Ha _)] := altP (x =P _).
        apply/allP=> x x_in_sc; rewrite inE.
        move: def_mem'; rewrite /updm OLD /= => - [<-].
        rewrite getm_set; move: x_in_sc not_syscall.
        by have [{x}-> ->|_ /(allP Hs _)] := altP (x =P _).
      * rewrite /Sym.good_internal /= in RINT *.
        case: RINT=> /= Hbounded Hisolate.
        { split.
          - move=> p cid''' I''' W'''.
            rewrite /Sym.sget.
            have [{p} -> | NEQ] := (p =P w1).
            + rewrite (getm_upd_eq def_mem'); move => [<- <- <-].
              apply (Hbounded w1 c I W).
              by rewrite /Sym.sget OLD.
            + rewrite (getm_upd_neq NEQ def_mem').
              by apply (Hbounded p cid''' I''' W''').
          - move=> p sc.
            have [{p} ->|NEQp] := p =P w1;
            have [{sc} ->|NEQsc] := sc =P w1 => //.
            + rewrite /Sym.sget
                      (getm_upd_eq def_mem')
                      (getm_upd_neq NEQsc def_mem') => sc_is_sc E.
              by rewrite (Hisolate w1 sc sc_is_sc) // -E /Sym.sget OLD.
            + rewrite /Sym.sget
                      (getm_upd_eq def_mem')
                      (getm_upd_neq NEQp def_mem') => sc_is_sc E.
              by rewrite (Hisolate p w1 sc_is_sc) // E /Sym.sget OLD.
            + rewrite /Sym.sget
                      (getm_upd_neq NEQp def_mem')
                      (getm_upd_neq NEQsc def_mem').
              by apply (Hisolate p sc). }
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
    destruct (getm AR r) as [x|] eqn:GET;
      [| specialize RREGS with r; rewrite RW GET in RREGS; done].
    assert (EQ : x = w) by
      (by specialize RREGS with r;
          rewrite RW GET /refine_reg_b in RREGS; move/eqP in RREGS);
      subst x.
    evar (AR' : registers mt);
      exists (AState w AR' AM AC JUMPED c); split;
      subst AR'.
    + eapply Abs.step_jump; try reflexivity.
      * unfold Abs.decode.
        unfold refine_memory,pointwise,refine_mem_loc_b in RMEMS;
          specialize RMEMS with pc; rewrite PC in RMEMS;
          destruct (getm AM pc); [simpl|contradiction].
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
    destruct (getm AR r) as [x|] eqn:GET;
      [| specialize RREGS with r; rewrite RW GET in RREGS; done].
    assert (EQ : x = w) by
      (by specialize RREGS with r;
          rewrite RW GET /refine_reg_b in RREGS; move/eqP in RREGS);
      subst x.
    evar (AR' : registers mt);
      exists (AState (pc + (if w == 0 then 1 else swcast n))%w
                     AR' AM AC INTERNAL c); split;
      subst AR'.
    + eapply Abs.step_bnz; try reflexivity.
      * unfold Abs.decode.
        unfold refine_memory,pointwise,refine_mem_loc_b in RMEMS;
          specialize RMEMS with pc; rewrite PC in RMEMS;
          destruct (getm AM pc); [simpl|contradiction].
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
    destruct (getm AR r) as [x|] eqn:GET;
      [| specialize RREGS with r; rewrite RW GET in RREGS; done].
    assert (EQ : x = w) by
      (by specialize RREGS with r;
          rewrite RW GET /refine_reg_b in RREGS; move/eqP in RREGS);
      subst x.
    evar (AR' : registers mt);
      exists (AState w AR' AM AC JUMPED c); split;
      subst AR'.
    + eapply Abs.step_jal; try reflexivity.
      * unfold Abs.decode.
        unfold refine_memory,pointwise,refine_mem_loc_b in RMEMS;
          specialize RMEMS with pc; rewrite PC in RMEMS;
          destruct (getm AM pc); [simpl|contradiction].
        move/eqP in RMEMS; subst; eassumption.
      * by apply (prove_permitted_now_in AGOOD SGOOD PC def_cid).
      * assumption.
      * unfold updm; rewrite /refine_registers /pointwise in RREGS.
        match goal with |- context[getm AR ?ra] =>
          (* This finds the type class instances *)
          case: (getm AR ra) (RREGS ra) => {RREGS} RREGS;
            [reflexivity | rewrite OLD in RREGS; done]
        end.
    + constructor; simpl;
        try solve [done | eapply (prove_get_compartment_id SGOOD);
                          solve [ eassumption
                                | rewrite /Sym.sget /= PC; reflexivity ]].
      rewrite /refine_registers /pointwise in RREGS *; intros r'.
      rewrite getm_set.
      destruct (r' == ra) eqn:EQ_r'; move/eqP in EQ_r'; [subst r'|].
      * erewrite getm_upd_eq by eauto.
        by simpl.
      * erewrite getm_upd_neq with (m' := regs') by eauto.
        apply RREGS.
  - (* Syscall *)
    rewrite getm_mkpartmap /= !(eq_sym pc) in GETCALL.
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
      [ eapply Abs.step_syscall with (sc := Abs.isolate              (mt:=mt))
      | eapply Abs.step_syscall with (sc := Abs.add_to_jump_targets  (mt:=mt))
      | eapply Abs.step_syscall with (sc := Abs.add_to_store_targets (mt:=mt)) ];
      try solve [reflexivity | eassumption];
      destruct tpc as []; try discriminate; move/eqP in RPC; subst;
      try match goal with |- context[getm AM ?addr] =>
        rewrite /refine_memory /pointwise in RMEMS;
        specialize (RMEMS addr); rewrite PC in RMEMS;
        by destruct (getm AM addr)
      end;
      rewrite /refine_syscall_addrs_b in RSC;
      case/and3P: RSC => /= RS1 RS2 /and3P [RS3 RS4 _];
      rewrite getm_mkpartmap /= -!(eq_sym isolate_addr) eq_refl;
      rewrite !in_cons /= in RS3 RS4.
      * done.
      * by destruct (isolate_addr == add_to_jump_targets_addr).
      * by rewrite (eq_sym add_to_store_targets_addr);
           destruct (isolate_addr == add_to_jump_targets_addr),
                    (isolate_addr == add_to_store_targets_addr),
                    (add_to_jump_targets_addr == add_to_store_targets_addr).
Qed.

End RefinementSA.
