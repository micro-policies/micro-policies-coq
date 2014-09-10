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

(* I want to use S and I as variables. *)
Let S := Datatypes.S.
Let I := Logic.I.
(* ssreflect exposes `succn' as a synonym for `S' *)
Local Notation II := Logic.I.

Context
  (t            : machine_types)
  {ops          : machine_ops t}
  {spec         : machine_ops_spec ops}
  {scr          : @syscall_regs t}
  {cmp_syscalls : compartmentalization_syscall_addrs t}.

Notation word := (word t).
Notation stag := (@Sym.stag t).
Notation sym_compartmentalization := (@Sym.sym_compartmentalization t).

Notation satom  := (atom word stag).
Notation svalue := (@val word stag).
Notation slabel := (@common.tag word stag).

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
Definition refine_pc_b (apc : word) (spc : satom) :=
  match spc with
    | spc' @ (Sym.PC _ _) => apc == spc'
    | _                   => false
  end.

(* We check the compartment stuff later *)
Definition refine_mem_loc_b (ax : word) (sx : satom) : bool :=
  match sx with
    | sx' @ (Sym.DATA _ _ _) => ax == sx'
    | _                      => false
  end.

Definition refine_reg_b (ar : word) (sr : satom) : bool :=
  match sr with
    | sr' @ Sym.REG => ar == sr'
    | _             => false
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
    (stag_compartment <=< Sym.sget sst) @: Abs.address_space c ==
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
                               (sources : stag -> option {set word})
                               (sst     : sstate)
                               (C       : seq (Abs.compartment t)) : Prop :=
  forall c cid,
    c \in C ->
    get_compartment_id sst c = Some cid ->
    targets c =
    [set p | oapp (fun s : {set word} => cid \in s) false
                  (sources =<< Sym.sget sst p) ].

Definition well_formed_jump_targets : sstate -> seq (Abs.compartment t) -> Prop :=
  well_formed_targets (fun c => Abs.jump_targets c) stag_incoming.

Definition well_formed_store_targets : sstate -> seq (Abs.compartment t) -> Prop :=
  well_formed_targets (fun c => Abs.store_targets c) stag_writers.

End WithSym.

Definition refine_previous_b (sk : where_from) (prev : Abs.compartment t)
                             (sst : sstate) : bool :=
  match Symbolic.pc sst with
    | _ @ (Sym.PC F cid) => (sk == F) &&
                            (get_compartment_id sst prev == Some cid)
    | _ @ _ => false
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

(*
(* MOVE *)
Lemma map_options_in (X Y : eqType) (f : X -> option Y) xs ys :
  map_options f xs = Some ys ->
  forall y, reflect (exists2 x, f x = Some y & x \in xs) (y \in ys).
Proof.
  elim: xs ys => [|x xs IH] //= ys.
  - move=> [<-] y.
    by apply/(iffP idP) => [|[? ? ?]] //=.
  - case Ex: (f x) => [y|] //=.
    case Em: (map_options _ _) => [ys' |] //=.
    move/(IH _): Em => Em [<-] y'.
    rewrite in_cons.
    have [E|?] := (y' =P y) => /=.
    + constructor.
      eexists x => //; first by rewrite -E in Ex.
      by rewrite in_cons eqxx.
    + apply/(iffP (Em y')); move=> [x' H1 H2].
      * exists x' => //.
        by rewrite in_cons H2 orbT.
      * exists x' => //.
        rewrite in_cons in H2.
        case/orP: H2 => [/eqP E | //].
        congruence.
Qed.
*)

(*
Ltac explode_refined_compartment' RC :=
  let sxs      := fresh "sxs"      in
  let def_sxs  := fresh "def_sxs"  in
  let sc       := fresh "sc"       in
  let def_sc   := fresh "def_sc"   in
  let ALL_J    := fresh "ALL_J"    in
  let ALL_S    := fresh "ALL_S"    in
  let mJ       := fresh "mJ"       in
  let MAP_J    := fresh "MAP_J"    in
  let mS       := fresh "mS"       in
  let MAP_S    := fresh "MAP_S"    in
  let SAME_cid := fresh "SAME_cid" in
  match type of RC with refined_compartment <<?A,?J,?S>> _ ?= _ =>
  rewrite /refined_compartment /= in RC;
     undo1 RC sxs; undo1 RC sc;
     undo1 RC ALL_J; undo1 RC ALL_S;
     inversion RC; subst sc; clear RC;
  let unfmap hyp name eqn :=
      match type of hyp with
        | (_ <$> ?opt) = Some _ =>
          destruct opt as [name|] eqn:eqn;
            [simpl in hyp | discriminate];
            let H := fresh hyp in
            inversion hyp as [H]; clear hyp; rename H into hyp
      end
  in unfmap ALL_J mJ MAP_J; unfmap ALL_S mS MAP_S;
     move/map_options_in in MAP_J; move/map_options_in in MAP_S;
     move/allP in ALL_J; move/allP in ALL_S; simpl in *;
  move/map_options_in in def_sxs;
  destruct (map_options _ sxs) as [cids|] eqn:MAP_sxs; simpl in *;
    [|discriminate];
  move/map_options_in in MAP_sxs; idtac
  (*move: def_sc => /theP/andP [NE_cids /allP SAME_cid]*)
  end.

Ltac explode_refined_compartment RC A J S :=
  match type of RC with
    | refined_compartment ?c _ ?= _ => destruct c as [A J S]
  end;
  explode_refined_compartment' RC.
*)

(*
(* Could be reused more than it is *)
Lemma refined_sget_in_compartment : forall C c cid sst I W p,
  Abs.good_compartments C ->
  c \in C ->
  (forall p, refine_compartment_tag C sst p) ->
  refined_compartment c sst ?= cid ->
  Sym.sget sst p ?= Sym.DATA cid I W ->
  C ⊢ p ∈ c.
Proof.
  clear S I.
  move=> C [A J S] cid sst I W p GOODS IN_c_C RCTAGS /= REFINED SGET.
  move: (RCTAGS p) => RCTAGS'; rewrite /refine_compartment_tag SGET in RCTAGS';
    move: RCTAGS' => [c' [IC' RTAG]].
  case: pickP REFINED => //= cid' /andP [? /forallP ?].
  admit. (*
  have IC_p'_c : C ⊢ p' ∈ <<A,J,S>>.  rewrite /Abs.in_compartment /=.
  move: (mem_enum A).


  Set Printing All.
  rewrite mem_enum in IN'.

IN'. by apply Abs.in_compartment_spec.
  specialize RTAG with p'; rewrite SGET' in RTAG.
  destruct Lw; try done; simpl in *.
  inversion TAG; subst.
  move: RTAG => [SAME _]; assert (IC_p'_c' : C ⊢ p' ∈ c') by by apply SAME.
  replace c' with <<A,J,S>> in * by eauto 3.
  assumption.*)
Qed.
*)

Theorem refine_good : forall `(REFINE : refine ast sst),
  Abs.good_state ast ->
  Sym.good_state sst.
Proof.
  clear S I.
  move=> [Apc AR AM AC Ask Aprev]
         [SM SR [Spc Lpc] [Snext SiT SaJT SaST]]
         [RPC RREGS RMEMS WDCOMPS WDIDS UIDS WFJTS WFSTS RPREV RSCS RINT]
         /and4P [ELEM GOODS SS SP];
    simpl in *.
  repeat split.
  - intros p; unfold Sym.good_memory_tag.
    unfold refine_memory, pointwise in RMEMS; specialize RMEMS with p.
    unfold Sym.sget in *.
    case SGET: (get SM p) RMEMS => [[Sx SL]|] RMEMS.
    + case AGET: (get AM p) RMEMS => [Ax|] RMEMS; [simpl in RMEMS | elim RMEMS].
      destruct SL as [|c I W|]; solve [apply/andP; tauto | done].
    + destruct (p == isolate_addr);
        [|destruct (p == add_to_jump_targets_addr);
          [|destruct (p == add_to_store_targets_addr)]];
        unfold Sym.sget in *; simpl in *;
        try done; by destruct SiT,SaJT,SaST.
  - intros r; unfold Sym.good_register_tag.
    unfold refine_registers, pointwise in RREGS; specialize RREGS with r.
    case SGET: (get SR r) RREGS => [[Sx SL]|] RREGS; last by [].
    case AGET: (get AR r) RREGS => [Ax|] RREGS; last by elim RREGS.
    unfold refine_reg_b in RREGS.
    by destruct SL.
  - destruct Lpc; try discriminate.
    move: RPREV => /andP [/eqP? /eqP RPREV]; subst.
    rewrite /get_compartment_id in RPREV.
    case: pickP RPREV => //= => x /eqP RPREV.
    have: Some x == Some x by apply eq_refl.
    rewrite -(in_set1 (Some x)) -RPREV => /imsetP [y IN_y ->] SGET.
      clear x RPREV.
      exists y; move: SGET.
    case SGET: (Sym.sget _ y) => [L|//].
    case: L SGET => //= [F' c' | c' I W] SGET []?; subst.
    + move/(_ y) in RMEMS.
      rewrite /Sym.sget in SGET.
      move: RMEMS SGET.
      case: (get SM y) => [[]|] /=.
      * case: (get AM y) => //.
        by move=> a x L MEM []?; subst; simpl in *.
      * move=> _.
        rewrite /Sym.good_internal /= in RINT.
        destruct SiT,SaJT,SaST; try done.
        case: (y == isolate_addr) => //.
        case: (y == add_to_jump_targets_addr) => //.
        case: (y == add_to_store_targets_addr) => //.
    + by exists I,W.
  - assumption.
Qed.

Ltac unoption :=
  repeat match goal with
    | EQ  : Some _ = Some _ |- _ => inversion EQ; subst; clear EQ
    | NEQ : Some _ = None   |- _ => discriminate
    | NEQ : None   = Some   |- _ => discriminate
    | EQ  : None   = None   |- _ => clear EQ
  end.

(*
Lemma prove_refined_compartment : forall pc cid I W
                                         AC c sst,
  Sym.sget sst pc ?= Sym.DATA cid I W ->
  Abs.good_compartments AC ->
  all (is_some ∘ refined_compartment^~ sst) AC ->
  (forall p, refine_compartment_tag AC sst p) ->
  AC ⊢ pc ∈ c ->
  (forall p' : word,
     match Sym.sget sst p' with
       | Some (Sym.PC _ _) => False
       | Some (Sym.DATA cid' I' W') =>
         (cid = cid' <-> AC ⊢ p' ∈ c) /\
         (cid \in I' -> p' \in Abs.jump_targets c) /\
         (cid \in W' -> p' \in Abs.store_targets c)
       | Some Sym.REG => False
       | None => True
     end) ->
  refined_compartment c sst ?= cid.
Proof. admit. Qed. (*
  clear S I; intros until 0; simpl in *;
    intros PC AGOOD RCOMPS RCTAGS IN_c SET_I RTAG;
    rewrite /refine_compartment_tag in RCTAGS; simpl in *.
  assert (OK : is_some (refined_compartment c sst)). {
    move/forallb_forall in RCOMPS. apply RCOMPS.
    apply Abs.in_compartment_spec in IN_c; tauto.
  }
  destruct (refined_compartment c sst) as [cid'''|] eqn:OK';
    [clear OK; rename OK' into OK; f_equal | discriminate].
  destruct sst as [mem reg pc' si]; simpl in *.
  let S := fresh "S" in explode_refined_compartment OK A J S.
  - move: NE_cids => /nonempty_iff_in [cid' IN_cid].
    specialize (SAME_cid cid' IN_cid); subst.
    apply MAP_sxs in IN_cid.
    move: IN_cid => [[v [F' cid'|cid' I' W'|]] [EQ_cid IN_sxs]];
                   simpl in *; try discriminate;
                   inversion EQ_cid; subst; clear EQ_cid;
                   apply def_sxs in IN_sxs; destruct IN_sxs as [p [GET IN_p]];
                   [by specialize RTAG with p; rewrite GET in RTAG|].
    move: (RCTAGS p) => RCTAGS'; rewrite GET in RCTAGS';
                        move: RCTAGS' => [SET_I' [SET_W' [c [IC_p_c RTAG']]]].
    assert (IC_p_AJS : AC ⊢ p ∈ <<A,J,S>>) by
        (apply Abs.in_compartment_spec; apply Abs.in_compartment_spec in IN_c;
         tauto).
    assert (c = <<A,J,S>>) by eauto 3; subst.
    specialize RTAG with p; rewrite GET in RTAG;
    destruct RTAG as [SAME _].
    symmetry; apply SAME; assumption.
Qed.
*)

Lemma prove_refined_compartment' : forall pc cid cid' cid'' I W F
                                          AR AM AC Ask Aprev c sst,
  Sym.sget sst pc ?= Sym.DATA cid'' I W ->
  (do! guard (cid'' == cid') || ((F == JUMPED) && (cid' \in I));
   Some cid'') ?= cid ->
  Abs.good_state (AState pc AR AM AC Ask Aprev) ->
  all (is_some ∘ refined_compartment^~ sst) AC ->
  (forall p, refine_compartment_tag AC sst p) ->
  AC ⊢ pc ∈ c ->
  (forall p' : word,
     match Sym.sget sst p' with
       | Some (Sym.PC _ _) => False
       | Some (Sym.DATA cid''' I' W') =>
         (cid'' = cid''' <-> AC ⊢ p' ∈ c) /\
         (cid'' \in I' -> p' \in Abs.jump_targets c) /\
         (cid'' \in W' -> p' \in Abs.store_targets c)
       | Some Sym.REG => False
       | None => True
     end) ->
  refined_compartment c sst == Some cid.
Proof.
  intros until 0; intros SGET GUARD.
  undo1 GUARD COND; inversion GUARD; subst.
  intros; apply/eqP; eapply prove_refined_compartment; eauto.
Qed.
*)

Lemma get_compartment_id_in_compartment_eq (C : seq (Abs.compartment t)) sst c p :
  (forall p, Sym.good_memory_tag sst p) ->
  well_defined_compartments sst C ->
  well_defined_ids sst C ->
  unique_ids sst C ->
  c \in C ->
  (get_compartment_id sst c == (Sym.stag_compartment =<< Sym.sget sst p)) =
  (p \in Abs.address_space c).
Proof.
  move=> /(_ p) GOODp /(_ p) WDC WDID UNIQUE IN.
  move: (WDID c IN).
  case ID: (get_compartment_id sst c) => [cid|] // _.
  rewrite /Sym.good_memory_tag in GOODp.
  apply/(sameP idP)/(iffP idP).

  - move: ID.
    rewrite /get_compartment_id.
    case: pickP => // cid' /eqP Hcid' [E]. subst cid'.
    move/(mem_imset (Sym.stag_compartment <=< Sym.sget sst)) => /=.
    rewrite Hcid' in_set1.
    case GET: (Sym.sget sst p) GOODp {WDC} => [[|? Ia Sa|]|] //= _.
    by rewrite eq_sym.

  - case GET: (Sym.sget sst p) GOODp WDC => [[|? Ia Sa|]|] //= _ /(_ erefl).
    case E: (Abs.in_compartment_opt C p) => [c'|] // _ /eqP [E'].
    rewrite -E' in GET => {E'}.
    case/Abs.in_compartment_opt_correct/andP: E => IN' INp.
    suff {UNIQUE} ID' : get_compartment_id sst c' = Some cid.
    { rewrite -ID' in ID.
      by rewrite (UNIQUE _ _ IN IN' ID). }
    move: (WDID c' IN').
    rewrite /get_compartment_id.
    case: pickP => // cid' /eqP Hcid' _.
    move/(mem_imset (Sym.stag_compartment <=< Sym.sget sst)): INp.
    rewrite Hcid' in_set1 /= GET /=.
    by move/eqP=> ->.
Qed.

Lemma get_compartment_id_in_compartment (C : seq (Abs.compartment t)) sst c p :
  (forall p, Sym.good_memory_tag sst p) ->
  well_defined_compartments sst C ->
  well_defined_ids sst C ->
  unique_ids sst C ->
  c \in C ->
  (get_compartment_id sst c = (Sym.stag_compartment =<< Sym.sget sst p)) ->
  (p \in Abs.address_space c).
Proof.
  move=> GOOD WDC WDID UNIQUE IN H.
  by rewrite -(get_compartment_id_in_compartment_eq _ GOOD WDC WDID UNIQUE IN) H.
Qed.

Lemma in_compartment_get_compartment_id (C : seq (Abs.compartment t)) sst c p :
  (forall p, Sym.good_memory_tag sst p) ->
  well_defined_compartments sst C ->
  well_defined_ids sst C ->
  unique_ids sst C ->
  c \in C ->
  (p \in Abs.address_space c) ->
  get_compartment_id sst c = (Sym.stag_compartment =<< Sym.sget sst p).
Proof.
  move=> GOOD WDC WDID UNIQUE IN H.
  apply/eqP.
  by rewrite (get_compartment_id_in_compartment_eq _ GOOD WDC WDID UNIQUE IN) H.
Qed.

(*
Lemma prove_permitted_now_in : forall pc cid cid' cid'' I W F
                                      AR AM AC Ask Aprev
                                      mem reg int
                                      c,
  let sst := (SState mem reg pc@(Sym.PC F cid') int) in
  Sym.sget sst pc ?= Sym.DATA cid'' I W ->
  (Ask == F) && (refined_compartment Aprev sst == Some cid') ->
  (do! guard (cid'' == cid') || ((F == JUMPED) && (cid' \in I));
   Some cid'') ?= cid ->
  Abs.good_state (AState pc AR AM AC Ask Aprev) ->
  Sym.good_state sst ->
  (forall p, refine_compartment_tag AC sst p) ->
  AC ⊢ pc ∈ c ->
  (forall p' : word,
     match Sym.sget sst p' with
      | Some (Sym.PC _ _) => False
      | Some (Sym.DATA cid''' I' W') =>
          (cid'' = cid''' <-> AC ⊢ p' ∈ c) /\
          (cid'' \in I' -> p' \in Abs.jump_targets c) /\
          (cid'' \in W' -> p' \in Abs.store_targets c)
      | Some Sym.REG => False
      | None => True
     end) ->
  Abs.permitted_now_in AC Ask Aprev pc ?= c.
Proof. admit. Qed. (*
  clear S I; intros until 0; subst sst;
    intros PC RPREV def_cid AGOOD SGOOD RCTAGS IN_c SET_I RTAG;
    rewrite /refine_compartment_tag in RCTAGS; simpl in *.
  eapply Abs.permitted_now_in_spec; eauto 3.
  split; auto.
  move: RPREV => /andP [/eqP ? /eqP RPREV]; subst Ask.
  assert (IN_prev : In Aprev AC). {
    apply Abs.good_state_decomposed__previous_is_compartment in AGOOD;
      auto.
    set (ELT := elem Aprev AC) in *; by destruct ELT.
  }
  explode_refined_compartment RPREV Aprev Jprev Sprev.
  undo1 def_cid COND;
    move: COND => /orP [/eqP? | /andP [/eqP? /set_elem_true IN]];
    subst; inversion def_cid; subst; clear def_cid;
    [ left
    | right; split; auto; lapply IN; [clear IN; intros IN | auto]].
  - move: NE_cids => /nonempty_iff_in [cid' IN_cid].
    specialize (SAME_cid cid' IN_cid); subst.
    apply MAP_sxs in IN_cid.
    move: IN_cid => [[v [F' cid'|cid' I' W'|]] [EQ_cid IN_sxs]];
      simpl in *; try discriminate;
      inversion EQ_cid; subst; clear EQ_cid;
      apply def_sxs in IN_sxs; destruct IN_sxs as [p [GET IN_p]];
      specialize RTAG with p; rewrite GET in RTAG; try done.
    destruct RTAG as [[SAME _] _].
    assert (IC_p_c    : AC ⊢ p ∈ c) by auto.
    assert (IC_p_prev : AC ⊢ p ∈ <<Aprev,Jprev,Sprev>>) by
      by apply Abs.in_compartment_spec.
    eauto 3.
  - rewrite /Sym.good_state /= in SGOOD.
    move: SGOOD => [[_ [_ [p' [x' [I' [W' GET']]]]]] _].
    assert (IC'' : AC ⊢ p' ∈ <<Aprev,Jprev,Sprev>>). {
      move/id in def_sxs; move/id in MAP_sxs;
        move/id in SAME_cid; move/id in NE_cids.
      destruct cids as [|cid'' cids];
        [discriminate | clear NE_cids; simpl in *].
      move: (SAME_cid cid'' (or_introl Logic.eq_refl)) => ?; subst.
      move: (MAP_sxs cid') => [MAP_sxs' _];
        specialize (MAP_sxs' (or_introl Logic.eq_refl)).
      move: MAP_sxs' => [[v Lv] [TAG IN_sxs]]; simpl in *.
      apply def_sxs in IN_sxs.
      destruct IN_sxs as [p [GET_p IN_p]].
      move: (RCTAGS p) => RTAG'; rewrite GET_p in RTAG'.
      destruct Lv as [|cid'' I'' W''|]; try done.
      simpl in TAG; inversion TAG; subst.
      move: RTAG' => [_ [_ [c'' [IC'' RTAG']]]].
      specialize RTAG' with p'; rewrite GET' in RTAG';
        move: RTAG' => [[SAME _] _].
      specialize (SAME Logic.eq_refl).
      assert (IC_p_prev : AC ⊢ p ∈ <<Aprev,Jprev,Sprev>>) by
        by apply Abs.in_compartment_spec.
      assert (c'' = <<Aprev,Jprev,Sprev>>) by eauto 3; subst.
      assumption.
    }
    move: (RCTAGS p') => RCTAGS'; rewrite GET' in RCTAGS';
      move: RCTAGS' => [_ [_ [c' [IC' RTAG']]]].
    specialize RTAG' with pc; rewrite PC in RTAG'.
    move: RTAG' => [_ [IN_I _]].
    apply IN_I in IN.
    by assert (c' = <<Aprev,Jprev,Sprev>>) by eauto 3; subst.
Qed.
*)
*)

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

(*
Ltac solve_permitted_now_in :=
  match goal with
    | RPREV : context[refine_previous_b],
      PC    : get _ ?pc ?= _
      |- Abs.permitted_now_in _ _ _ ?pc ?= _ =>
      rewrite /refine_previous_b /= in RPREV;
      eapply prove_permitted_now_in; try eassumption;
      rewrite /Sym.sget PC; reflexivity
  end.
*)

(*
Definition equivalued (sst1 sst2 : sstate) : Prop :=
  forall p,
    match Sym.sget sst1 p , Sym.sget sst2 p with
      | Some (x1@_) , Some (x2@_) => x1 = x2
      | None        , None        => True
      | _           , _           => False
    end.
*)

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
      | Some L1 , Some L2 => Sym.stag_compartment L1 =
                             Sym.stag_compartment L2
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

Lemma tags_subsets_in_tail : forall p ps sst sst',
  tags_subsets_in (p |: ps) sst sst' ->
  tags_subsets_in ps sst sst'.
Proof.
  rewrite /tags_subsets_in /=; move=> p ps sst sst' TSI a.
  specialize TSI with a.
  destruct (Sym.sget sst  a) as [[| |]|],
           (Sym.sget sst' a) as [[| |]|];
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
  destruct (Sym.sget sst   p) as [[| |]|],
           (Sym.sget sst'  p) as [[| |]|],
           (Sym.sget sst'' p) as [[| |]|];
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
  destruct (Sym.sget sst   p) as [[| |]|],
           (Sym.sget sst'  p) as [[| |]|],
           (Sym.sget sst'' p) as [[| |]|];
    try done.
  move: TSI TSI' => [H1 [H2 H3]] [H1' [H2' H3']].
  repeat split; solve [intuition congruence|eauto using subset_trans].
Qed.

Lemma tags_subsets_any_in : forall ps sst sst',
  tags_subsets       sst sst' ->
  tags_subsets_in ps sst sst'.
Proof.
  move=> ps sst sst' TSI p; specialize (TSI p).
  destruct (Sym.sget sst  p) as [[| |]|],
           (Sym.sget sst' p) as [[| |]|];
    try done.
  repeat invh and; subst; auto.
Qed.

(*
Lemma refined_compartment_untouched_preserved : forall sst sst' c cid,
  (forall p, Sym.good_memory_tag sst  p) ->
  (forall p, Sym.good_memory_tag sst' p) ->
  tags_subsets_in (Abs.address_space c) sst sst' ->
  refined_compartment c sst  ?= cid ->
  refined_compartment c sst' ?= cid.
Proof.
  clear S I; intros sst sst' [A J S] cid GOOD GOOD' TSI.
  rewrite /refined_compartment /=.
  case: pickP => [sc|] //; case/andP=> H1 /forall_inP H2 [<-].
  rewrite -(@eq_pick _ (fun sc' => (sc' == sc) &&
                                   [forall os in (Sym.stag_incoming <=< Sym.sget sst') @: J :|:
                                                 (Sym.stag_writers  <=< Sym.sget sst') @: S,
                                     oapp (fun s : {set word} => sc' \in s) false os])).
  admit.

  admit. (*
  assert (INIT :
    (do! sxs <- map_options (Sym.sget sst) A;
     the =<< map_options (Sym.stag_compartment ∘ slabel) sxs)
    =
    (do! sxs' <- map_options (Sym.sget sst') A;
     the =<< map_options (Sym.stag_compartment ∘ slabel) sxs')).
  {
    rewrite (lock the) 2!bind_assoc -(lock the) 2!map_options_bind; f_equal.
    induction A as [|a A]; simpl in *; [reflexivity|].
    move: (TSI a) => COMPAT.
    destruct (Sym.sget sst  a) as [[x  [|c  I  W|]]|],
             (Sym.sget sst' a) as [[x' [|c' I' W'|]]|];
      try done; destruct COMPAT as [EQ _]; simpl.
    specialize (EQ (or_introl erefl)); subst c'.
    rewrite IHA; try reflexivity.
    eapply tags_subsets_in_tail; eassumption.
  }

  set MAP_J := map_options _ J; set MAP_J' := map_options _ J.
  assert (EQ_ALL_J : forall sc,
            (forallb (set_elem sc) <$> MAP_J)  ?= true ->
            (forallb (set_elem sc) <$> MAP_J') ?= true). {
    subst MAP_J MAP_J'; intros sc; simpl.
    induction J as [|a J]; [reflexivity|simpl].
    move: (TSI a) => COMPAT; specialize GOOD with a; specialize GOOD' with a.
    rewrite /Sym.good_memory_tag in GOOD GOOD'.
    destruct (Sym.sget sst  a) as [[x  [|c  I  W|]]|],
             (Sym.sget sst' a) as [[x' [|c' I' W'|]]|];
      try done; simpl.
    move: GOOD GOOD' => /andP [SET_I SET_W] /andP [SET_I' SET_W'].
    destruct COMPAT as [EQ [SUB_I SUB_W]]; subst.
    let unMO ys MO := match goal with
                        |- context[map_options ?f J] =>
                        destruct (map_options f J) as [ys|] eqn:MO
                      end
    in unMO ys MO; unMO ys' MO'; try done; simpl in *.
    - specialize SUB_I with sc.
      move=> [/andP [ELEM ALL]]; f_equal; apply/andP; split; auto.
      + apply/set_elem_true; [|apply set_elem_true in ELEM]; auto.
      + destruct (forallb _ ys); try done.
        destruct (forallb _ ys'); try done.
        lapply IHJ; [move=> H; specialize (H erefl); discriminate | auto].
    - destruct (forallb _ ys).
      + lapply IHJ; [move=> H; specialize (H erefl); discriminate | auto].
      + rewrite Bool.andb_false_r; inversion 1.
  }

  set MAP_S := map_options _ S; set MAP_S' := map_options _ S.
  assert (EQ_ALL_S : forall sc,
            (forallb (set_elem sc) <$> MAP_S)  ?= true ->
            (forallb (set_elem sc) <$> MAP_S') ?= true). {
    subst MAP_S MAP_S'; intros sc; simpl.
    induction S as [|a S' IHS];
      [reflexivity | simpl; clear S; rename S' into S].
    move: (TSI a) => COMPAT; specialize GOOD with a; specialize GOOD' with a.
    rewrite /Sym.good_memory_tag in GOOD GOOD'.
    destruct (Sym.sget sst  a) as [[x  [|c  I  W|]]|],
             (Sym.sget sst' a) as [[x' [|c' I' W'|]]|];
      try done; simpl.
    move: GOOD GOOD' => /andP [SET_I SET_W] /andP [SET_I' SET_W'].
    destruct COMPAT as [EQ [SUB_I SUB_W]]; subst.
    let unMO ys MO := match goal with
                        |- context[map_options ?f S] =>
                        destruct (map_options f S) as [ys|] eqn:MO
                      end
    in unMO ys MO; unMO ys' MO'; try done; simpl in *.
    - specialize SUB_W with sc.
      move=> [/andP [ELEM ALL]]; f_equal; apply/andP; split; auto.
      + apply/set_elem_true; [|apply set_elem_true in ELEM]; auto.
      + destruct (forallb _ ys); try done.
        destruct (forallb _ ys'); try done.
        lapply IHS; [move=> H; specialize (H erefl); discriminate | auto].
    - destruct (forallb _ ys).
      + lapply IHS; [move=> H; specialize (H erefl); discriminate | auto].
      + rewrite Bool.andb_false_r; inversion 1.
  }

  intros REFINED; rewrite bind_assoc in REFINED.
  match type of REFINED with
    | (do! _ <- ?X; _) ?= _ =>
      destruct X as [sc|] eqn:def_sc; simpl in REFINED; [|done]
  end.
  rewrite bind_assoc -INIT def_sc; simpl.
  specialize EQ_ALL_J with sc; specialize EQ_ALL_S with sc.
  destruct (forallb _ <$> MAP_J) as [[]|] eqn:ALL_J; simpl in REFINED; try done.
  destruct (forallb _ <$> MAP_S) as [[]|] eqn:ALL_S; simpl in REFINED; try done.
  lapply EQ_ALL_J; [clear EQ_ALL_J; intro ALL_J' | done].
  lapply EQ_ALL_S; [clear EQ_ALL_S; intro ALL_S' | done].
  destruct (forallb _ <$> MAP_J') as [[]|]; try done.
  destruct (forallb _ <$> MAP_S') as [[]|]; done. *)
Qed.
*)

(*
Lemma refined_compartment_all_untouched_preserved : forall sst sst' c cid,
  (forall p, Sym.good_memory_tag sst  p) ->
  (forall p, Sym.good_memory_tag sst' p) ->
  tags_subsets sst sst' ->
  refined_compartment c sst  ?= cid ->
  refined_compartment c sst' ?= cid.
Proof.
  move=> sst sst' c cid GOOD GOOD' TS;
    apply refined_compartment_untouched_preserved;
    try apply tags_subsets_any_in; assumption.
Qed.
*)

(*
Lemma refined_compartment_all_untouched_isSome_preserved : forall sst sst' c,
  (forall p, Sym.good_memory_tag sst  p) ->
  (forall p, Sym.good_memory_tag sst' p) ->
  tags_subsets sst sst' ->
  refined_compartment c sst ->
  refined_compartment c sst'.
Proof.
  intros sst sst' c cid GOOD GOOD' COMPAT.
  destruct (refined_compartment c sst) eqn:RC; [|done].
  eapply refined_compartment_all_untouched_preserved in RC; try eassumption.
  by rewrite RC.
Qed.
*)

(*
Lemma refined_compartment_augment cid sst Aprev Jprev Sprev p:
  get_compartment_id sst <<Aprev,Jprev,Sprev>> ?= cid ->
  is_some (get_compartment_id sst <<Aprev,p |: Jprev,Sprev>>) =
  oapp (fun s : {set word} => cid \in s) false
       ((Sym.stag_incoming <=< Sym.sget sst) p).
Proof.
  rewrite /get_compartment_id.
  case: pickP cid => [cid /eqP Hcid1|] //. _ [<-].
  rewrite -(@eq_pick _ (fun sc => (sc == cid) &&
                                  oapp (fun s : {set word} => cid \in s) false
                                  ((Sym.stag_incoming <=< Sym.sget sst) p))).
  { case: pickP {Hcid1 Hcid2} => [cid' /andP [_ ->] //|/(_ cid)].
    by rewrite eqxx /=. }
  move => cid' /=.
  rewrite -Hcid1.
  apply/(sameP idP)/(iffP idP)=> /andP [/eqP Hcid'].
  - move/set1_inj: Hcid' => [->].
    rewrite eqxx /=.
    move/forallP=> /(_ ((Sym.stag_incoming <=< Sym.sget sst) p))/implyP H.
    rewrite imsetU1 in_setU in_setU1 eqxx /= in H.
    by apply H.
  - rewrite {cid'} Hcid' eqxx /=.
    move=> Hp.
    apply/forallP=> os.
    rewrite imsetU1 in_setU in_setU1 -orbA.
    by apply/implyP=> /or3P [/eqP -> //| Hos | Hos];
    move: Hcid2 => /(_ os)/implyP Hcid2; apply/Hcid2; rewrite in_setU Hos ?orbT.
Qed.
*)

Lemma get_compartment_id_same : forall sst sst' c,
  equilabeled sst sst' ->
  get_compartment_id sst c = get_compartment_id sst' c.
Proof.
  clear S I; intros sst sst' [A J S] SAME.
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
  clear S I; intros ok retag ps; induction ps as [|p ps]; simpl;
    intros sst sst'' AM RETAG REFINE.
  - by inversion RETAG; subst.
  - let I := fresh "I"
    in undoDATA RETAG x c I W; undo1 RETAG OK;
       destruct (retag c I W) as [|c' I' W'|] eqn:TAG; try discriminate;
       undo1 RETAG sst'.
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

(***** START MOVEMENT FOR EFFICIENCY *****)

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
    by case: (get m p) => [[v2 [|? ? ?|]]|].
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

Lemma sget_supd_good_internal sst sst' p c I1 W1 I2 W2 :
  Sym.sget sst p ?= Sym.DATA c I1 W1 ->
  Sym.supd sst p (Sym.DATA c I2 W2) ?= sst' ->
  Sym.good_internal sst ->
  Sym.good_internal sst'.
Proof.
  case: sst => m r pc [? [? ?|? ? ?|] [? ?|? ? ?|] [? ?|? ? ?|]];
  rewrite /Sym.sget /Sym.supd /Sym.good_internal /rep //=.
  case: sst' => m' r' pc' [? ? ? ?] /=.
  case GET: (get m p) => [[? tg]|].
  - move=> [Ht] /= [<- _ _ <- <- <- <-] [H1 [H2 H3]].
    subst tg.
    do 2?split; trivial.
    move=> p' x c' I' W'.
    have [->|NE] := (p' =P p).
    + rewrite get_set_eq.
      move=> [_ <- _ _].
      by apply (H3 _ _ _ _ _ GET).
    + rewrite (get_set_neq _ _ NE).
      by apply H3.
  - by repeat case: (p =P _) => _ //; move=> [<- _ _] [<- _ _ <- <- <- <-].
Qed.

Lemma sget_irrelevancies r' pc' m int r pc :
  Sym.sget (SState m r pc int) =
  Sym.sget (SState m r' pc' int).
Proof. reflexivity. Qed.

Lemma sget_next_irrelevant next' next m r pc iT aJT aST :
  Sym.sget (SState m r pc (SInternal next  iT aJT aST)) =
  Sym.sget (SState m r pc (SInternal next' iT aJT aST)).
Proof. reflexivity. Qed.

Lemma supd_good_memory_tag sst sst' p c I' W' :
  Sym.supd sst p (Sym.DATA c I' W') ?= sst' ->
  (forall p', Sym.good_memory_tag sst  p') ->
  (forall p', Sym.good_memory_tag sst' p').
Proof.
  move=> UPD GOOD p'.
  rewrite /Sym.good_memory_tag (Sym.sget_supd _ _ _ _ UPD).
  have [_ //|_] := (p' =P p).
  by apply/GOOD.
Qed.

Lemma supd_tags_subsets sst sst' p c I1 W1 I2 W2 :
  Sym.sget sst p ?= Sym.DATA c I1 W1 ->
  Sym.supd sst p (Sym.DATA c I2 W2) ?= sst' ->
  (forall p', Sym.good_memory_tag sst p') ->
  I1 \subset I2 -> W1 \subset W2 ->
  tags_subsets sst sst'.
Proof.
  clear I S.
  move=> GET UPD SGMEM HI HW p'.
  have [{p'} -> //|NE] := altP (p' =P p).
  { by rewrite GET (Sym.sget_supd _ _ _ _ UPD) eqxx. }
  rewrite (Sym.sget_supd _ _ _ _ UPD) (negbTE NE).
  by case/Sym.good_memory_tagP: (SGMEM p') => [c' I' W'|].
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
                                  (sources : stag -> option {set word})
                                  sst sst' p pcid I1 I2 W1 W2 Ss C c cid c' :
  well_formed_targets targets sources sst C ->
  unique_ids sst C ->
  Sym.sget sst p = Some (Sym.DATA pcid I1 W1) ->
  Sym.supd sst p (Sym.DATA pcid I2 W2) = Some sst' ->
  get_compartment_id sst c = Some cid ->
  c \in C ->
  Abs.address_space c = Abs.address_space c' ->
  targets c' = p |: targets c ->
  sources (Sym.DATA pcid I2 W2) = Some (cid |: Ss) ->
  sources (Sym.DATA pcid I1 W1) = Some Ss ->
  well_formed_targets targets sources sst' (c' :: rem_all c C).
Proof.
  clear S I.
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
                               (sources : stag -> option {set word})
                               sst sst' p pcid I1 I2 W1 W2 Ss C c cid c' :
  well_formed_targets targets sources sst C ->
  unique_ids sst C ->
  Sym.sget sst p = Some (Sym.DATA pcid I1 W1) ->
  Sym.supd sst p (Sym.DATA pcid I2 W2) = Some sst' ->
  get_compartment_id sst c = Some cid ->
  c \in C ->
  Abs.address_space c = Abs.address_space c' ->
  targets c' = targets c ->
  sources (Sym.DATA pcid I2 W2) = Some Ss ->
  sources (Sym.DATA pcid I1 W1) = Some Ss ->
  well_formed_targets targets sources sst' (c' :: rem_all c C).
Proof.
  clear S I.
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
  clear S I; move=> ast sst sst' AGOOD REFINE ADD.
  assert (SGOOD : Sym.good_state sst) by (eapply refine_good; eassumption).
  destruct REFINE as [RPC RREGS RMEMS COMPSWD IDSWD IDSU JTWF STWF RPREV RSC RINT],
           ast    as [Apc AR    AM    AC    Ask Aprev],
           sst    as [SM SR Spc [Snext SiT SaJT SaST]].
  generalize SGOOD; move=> [[SGMEM [SGREG SGPC]] SGINT].
  case/and4P: (AGOOD) => AIN /andP [ANOL ACC] ASS ASP.
  rewrite /Abs.semantics /Abs.add_to_jump_targets
          /Abs.add_to_compartment_component
          (lock Abs.in_compartment_opt);
    simpl in *.
  rewrite /refine_pc_b in RPC.
  destruct Spc as [pc [F cid'| |]]; try done; move/eqP in RPC; subst.

  move/id in ADD;
    undo1 ADD LI;
    undo1 ADD cid_sys;
    destruct LI as [|cid I W|]; try discriminate;
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
    by rewrite (in_compartment_get_compartment_id SGMEM COMPSWD IDSWD IDSU IN1 IN2) def_LI. }

  rewrite /Sym.good_pc_tag in SGPC; move: SGPC => [p' [I' [W' def_cid']]].

  assert (SYS_SEP : Aprev != c_sys). {
    apply/eqP; intro; subst.
    replace cid_sys with cid' in * by congruence.
    rewrite eq_refl in NEQ_cid_sys; discriminate.
  }
  rewrite SYS_SEP; simpl.

  generalize RREGS => RREGS';
    rewrite /refine_registers /pointwise /refine_reg_b in RREGS';
    specialize (RREGS' syscall_arg1); rewrite def_p_Lp in RREGS'.
  destruct (get AR syscall_arg1) as [Ap|]; destruct Lp; try done;
    move/eqP in RREGS'; subst; simpl.

  destruct Aprev as [Aprev Jprev Sprev]; simpl.

  have IC_p': p' \in Aprev.
  { apply/(get_compartment_id_in_compartment SGMEM COMPSWD IDSWD IDSU AIN).
    by rewrite def_cid'. }

  have ->: p \in Aprev :|: Jprev. {
    rewrite in_setU. apply/orP.
    case/orP: OK => [/eqP E|OK].
    - subst cid''. left.
      apply/(get_compartment_id_in_compartment SGMEM COMPSWD IDSWD IDSU AIN).
      by rewrite RPREV def_xcIW.
    - right.
      have /= -> := JTWF _ _ AIN RPREV.
      by rewrite in_set def_xcIW.
  }

  generalize RREGS => RREGS';
    rewrite /refine_registers /pointwise /refine_reg_b in RREGS';
    specialize (RREGS' ra); rewrite def_pc'_Lpc' in RREGS'.
  destruct (get AR ra) as [Apc'|]; destruct Lpc'; try done;
    move/eqP in RREGS'; subst; simpl.

  have IN_pc' : pc' \in Aprev.
  { apply/(get_compartment_id_in_compartment SGMEM COMPSWD IDSWD IDSU AIN).
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
  - exact: (sget_supd_good_internal def_xcIW def_s').
Qed.

Theorem add_to_store_targets_refined : forall ast sst sst',
  Abs.good_state ast ->
  refine ast sst ->
  Sym.add_to_store_targets sst ?= sst' ->
  exists ast',
    Abs.semantics (Abs.add_to_store_targets (t:=t)) ast ?= ast' /\
    refine ast' sst'.
Proof.
  clear S I; move=> ast sst sst' AGOOD REFINE ADD.
  assert (SGOOD : Sym.good_state sst) by (eapply refine_good; eassumption).
  destruct REFINE as [RPC RREGS RMEMS COMPSWD IDSWD IDSU JTWF STWF RPREV RSC RINT],
           ast    as [Apc AR    AM    AC    Ask Aprev],
           sst    as [SM SR Spc [Snext SiT SaJT SaST]].
  generalize SGOOD; move=> [[SGMEM [SGREG SGPC]] SGINT].
  case/and4P: (AGOOD) => AIN /andP [ANOL ACC] ASS ASP.
  rewrite /Abs.semantics /Abs.add_to_store_targets
          /Abs.add_to_compartment_component
          (lock Abs.in_compartment_opt);
    simpl in *.
  rewrite /refine_pc_b in RPC.
  destruct Spc as [pc [F cid'| |]]; try done; move/eqP in RPC; subst.

  move/id in ADD;
    undo1 ADD LI;
    undo1 ADD cid_sys;
    destruct LI as [|cid I W|]; try discriminate;
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
    by rewrite (in_compartment_get_compartment_id SGMEM COMPSWD IDSWD IDSU IN1 IN2) def_LI. }

  rewrite /Sym.good_pc_tag in SGPC; move: SGPC => [p' [I' [W' def_cid']]].

  assert (SYS_SEP : Aprev != c_sys). {
    apply/eqP; intro; subst.
    replace cid_sys with cid' in * by congruence.
    rewrite eq_refl in NEQ_cid_sys; discriminate.
  }
  rewrite SYS_SEP; simpl.

  generalize RREGS => RREGS';
    rewrite /refine_registers /pointwise /refine_reg_b in RREGS';
    specialize (RREGS' syscall_arg1); rewrite def_p_Lp in RREGS'.
  destruct (get AR syscall_arg1) as [Ap|]; destruct Lp; try done;
    move/eqP in RREGS'; subst; simpl.

  destruct Aprev as [Aprev Jprev Sprev]; simpl.

  have IC_p': p' \in Aprev.
  { apply/(get_compartment_id_in_compartment SGMEM COMPSWD IDSWD IDSU AIN).
    by rewrite def_cid'. }

  have ->: p \in Aprev :|: Sprev. {
    rewrite in_setU. apply/orP.
    case/orP: OK => [/eqP E|OK].
    - subst cid''. left.
      apply/(get_compartment_id_in_compartment SGMEM COMPSWD IDSWD IDSU AIN).
      by rewrite RPREV def_xcIW.
    - right.
      have /= -> := STWF _ _ AIN RPREV.
      by rewrite in_set def_xcIW.
  }

  generalize RREGS => RREGS';
    rewrite /refine_registers /pointwise /refine_reg_b in RREGS';
    specialize (RREGS' ra); rewrite def_pc'_Lpc' in RREGS'.
  destruct (get AR ra) as [Apc'|]; destruct Lpc'; try done;
    move/eqP in RREGS'; subst; simpl.

  have IN_pc' : pc' \in Aprev.
  { apply/(get_compartment_id_in_compartment SGMEM COMPSWD IDSWD IDSU AIN).
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
  - exact: (sget_supd_good_internal def_xcIW def_s').
Qed.

(***** END MOVEMENT *****)

(*
*)


Lemma retag_set_get_compartment_id_disjoint ok retag (ps : {set word}) sst sst' c cid :
  Sym.retag_set ok retag (enum ps) sst = Some sst' ->
  [disjoint Abs.address_space c & ps] ->
  get_compartment_id sst c = Some cid ->
  get_compartment_id sst' c = Some cid.
Proof.
  move=> Hretag /pred0P Hdis Hid.
  have {Hdis} Hdis: forall p, p \in Abs.address_space c -> p \notin enum ps.
  { move=> p Hin_c.
    apply/negP => Hin_ps.
    move: (Hdis p) => /=.
    by rewrite Hin_c -(mem_enum (mem ps)) Hin_ps. }
  elim: {ps} (enum ps) sst Hid Hretag Hdis => [|p ps IH] sst Hid /=; first congruence.
  case GET: (Sym.sget sst p) => [[|cid' I' W'|]|] //=.
  case: (ok cid' I' W') => //.
  case: (retag cid' I' W') => [|cid'' I'' W''|] //.
  case UPD: (Sym.supd _ _ _) => [sst''|] //= Hretag Hdis.
  apply (IH sst'') => //.
  - move: Hid.
    rewrite /get_compartment_id.
    case: pickP => [cid''' /eqP Hcid'''|] // [E].
    subst cid'''.
    move: (set11 (Some cid)).
    rewrite -Hcid''' => /imsetP [p' H1 H2].
    suff ->: [set (Sym.stag_compartment <=< @Sym.sget _ cmp_syscalls sst'') x | x in Abs.address_space c] =
             [set (Sym.stag_compartment <=< @Sym.sget _ cmp_syscalls sst) x | x in Abs.address_space c].
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
  suff ->: [set (Sym.stag_compartment <=< @Sym.sget _ cmp_syscalls sst) x | x in Abs.address_space c'] =
           [set (Sym.stag_compartment <=< @Sym.sget _ cmp_syscalls sst) x | x in Abs.address_space c].
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
  (forall c I1 W1, Sym.stag_compartment (retag c I1 W1) = Some c) ->
  get_compartment_id sst c = Some cid ->
  get_compartment_id sst' c = Some cid.
Proof.
  move=> Hretag_set Hretag.
  elim: ps sst Hretag_set => [|p ps IH] sst //=; first congruence.
  case GET: (Sym.sget _ _) => [[|cid1 I1 W1|]|] //=.
  case: (ok _ _ _) => //.
  move: Hretag => /(_ cid1 I1 W1).
  case RETAG: (retag _ _ _) => [|cid2 I2 W2|] //= [E].
  subst cid2.
  case UPD: (Sym.supd _ _ _) => [sst''|] //= Hretag_set Hcid.
  suff : get_compartment_id sst'' c = Some cid by apply IH.
  move: (Hcid).
  rewrite /get_compartment_id.
  case: pickP => [cid' /eqP Hcid1|]//= [E].
  subst cid'.
  suff -> : [set (Sym.stag_compartment <=< @Sym.sget _ cmp_syscalls sst'') x | x in Abs.address_space c] =
            [set (Sym.stag_compartment <=< @Sym.sget _ cmp_syscalls sst) x | x in Abs.address_space c].
  { apply Hcid. }
  apply/eq_in_imset => p' /= p'_in.
  rewrite (Sym.sget_supd _ _ _ _ UPD).
  have [-> //=|//] := (p' =P p).
  by rewrite GET.
Qed.

Lemma retag_set_get_compartment_id_new_id ok retag sst sst' c cid :
  Sym.retag_set ok retag (enum (Abs.address_space c)) sst = Some sst' ->
  (forall c I1 W1, Sym.stag_compartment (retag c I1 W1) = Some cid) ->
  get_compartment_id sst' c = Some cid.
Proof.
  case: c => [Aprev Jprev Sprev] /= Hretag_set Hretag.
  suff H: forall (ps : seq word) (Aprev : {set word}) sst,
            @Sym.retag_set _ cmp_syscalls ok retag ps sst = Some sst' ->
            get_compartment_id sst <<Aprev,Jprev,Sprev>> = Some cid ->
            get_compartment_id sst' <<Aprev :|: [set p : word in ps],Jprev,Sprev>> = Some cid.
  { admit. }
  elim {sst Aprev Hretag_set} => [|p ps IH] Aprev sst /=.
  { have -> : [set p : word in [::]] = set0 by [].
    rewrite setU0.
    congruence. }
  case GET: (Sym.sget sst p) => [[|cid' I' W'|]|] //=.
  case: (ok cid' I' W') => //.
  move: (Hretag cid' I' W').
  case: (retag _ _ _) => [|cid'' I'' W''|] //= [E].
  subst cid''.
  case UPD: (Sym.supd _ _ _) => [sst''|] //= Hretag_set Hcid.
  rewrite set_cons setUA.
  apply (IH _ sst'') => //.
  move: Hcid.
  rewrite /get_compartment_id.
  case: pickP => /= [cid'' /eqP E|] //= [?].
  subst cid''.
  rewrite setUC imsetU1 (Sym.sget_supd _ _ _ _ UPD) eqxx /=.
  suff -> : [set (do!X <- @Sym.sget _ cmp_syscalls sst'' x; Sym.stag_compartment X) | x in Aprev] =
            [set (do!X <- @Sym.sget _ cmp_syscalls sst x; Sym.stag_compartment X) | x in Aprev].
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

Theorem isolate_refined : forall ast sst sst',
  Abs.pc ast = isolate_addr ->
  Abs.good_state ast ->
  refine ast sst ->
  Sym.isolate sst ?= sst' ->
  exists ast',
    Abs.isolate_fn ast ?= ast' /\
    refine ast' sst'.
Proof.
  clear S I; move=> ast sst sst' IS_ISOLATE AGOOD REFINE ISOLATE;
    rewrite (lock eq) in IS_ISOLATE.
  assert (SGOOD : Sym.good_state sst) by (eapply refine_good; eassumption).
  destruct REFINE as [RPC RREGS RMEMS COMPSWD IDSWD IDSU JTWF STWF RPREV RSC RINT],
           ast    as [Apc AR    AM    AC    Ask Aprev],
           sst    as [SM SR Spc [Snext SiT SaJT SaST]].
  generalize SGOOD; move=> [[SGMEM [SGREG SGPC]] SGINT].
  case/and4P: (AGOOD) => AIN /andP [ANOL ACC] ASS ASP.
  rewrite /Abs.semantics /Abs.isolate /Abs.isolate_fn
          (lock Abs.in_compartment_opt);
    simpl in *.

  rewrite /refine_pc_b in RPC.
  destruct Spc as [pc [F cid| |]]; try done; move/eqP in RPC; subst.

  move/id in ISOLATE;
    undo1 ISOLATE LI;
    undo1 ISOLATE cid_sys;
    destruct LI as [|cid' I_sys W_sys|]; try discriminate;
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
  case/Abs.in_compartment_opt_correct/andP: (IN_c) => c_sys_in_AC pc_in_c_sys.

  move=> {COND_sys}.
  undo1 def_cid_sys COND; unoption.

  repeat (erewrite refined_reg_value; [|eassumption]).
  rewrite def_pA_LpA def_pJ_LpJ def_pS_LpS def_pc'_Lpc' /=.

  move: RPREV => /andP [/eqP ? /eqP RPREV]; subst.
  have -> /=: Abs.permitted_now_in AC F Aprev pc ?= c_sys.
  { rewrite /Abs.permitted_now_in IN_c /=.
    case/orP: COND => [/eqP E| /andP [/eqP E cid_in_I_sys]].
    - subst cid_sys.
      suff ->: c_sys = Aprev by rewrite eqxx.
      apply/(IDSU _ _ c_sys_in_AC AIN).
      by rewrite RPREV
                 (in_compartment_get_compartment_id SGMEM COMPSWD IDSWD IDSU c_sys_in_AC pc_in_c_sys)
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

  assert (SGOOD_sA : forall p, Sym.good_memory_tag sA p). {
    by eapply Sym.retag_set_preserves_good_memory_tag; try eassumption.
  }

  assert (SGOOD_sJ : forall p, Sym.good_memory_tag sJ p). {
    by eapply Sym.retag_set_preserves_good_memory_tag; try eassumption.
  }

  assert (SGOOD_sS : forall p, Sym.good_memory_tag (SState MS RS pcS siS) p). {
    by eapply Sym.retag_set_preserves_good_memory_tag; try eassumption.
  }

  assert (SUBSET_A' : A' \subset Aprev). {
    apply/subsetP; intros a IN.
    have := (Sym.retag_set_forall _ _ _ _ _ (enum_uniq (mem A')) def_sA a).
    rewrite (mem_enum (mem A')) IN => /(_ erefl).
    move=> /= [c' [I' [W' [SGET /eqP OK]]]]; subst c'.
    apply/(get_compartment_id_in_compartment SGMEM COMPSWD IDSWD IDSU AIN).
    rewrite /Sym.sget /= in SGET *.
    by rewrite SGET.
  }
  rewrite SUBSET_A'.

  assert (IN_A' : forall a I' W',
                    Sym.sget sA a ?= Sym.DATA Snext I' W' ->
                    a \in A'). {
    intros until 0; intros SGET.
    have [// | NIN] := boolP (a \in A').
    have := (Sym.retag_set_not_in _ _ _ _ _ def_sA a).
    rewrite (mem_enum (mem A')) NIN => /(_ erefl) SGET'.
    rewrite -SGET' in SGET.
    eapply Sym.sget_lt_next in RINT; [simpl in RINT | exact: SGET].
    by rewrite ltb_irrefl in RINT.
  }

  assert (SUBSET_J' : J' \subset Aprev :|: Jprev). {
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
     + apply/(get_compartment_id_in_compartment SGMEM COMPSWD IDSWD IDSU AIN).
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

  assert (IN_A'_sJ : forall a I' W',
                       Sym.sget sJ a ?= Sym.DATA Snext I' W' ->
                       a \in A'). {
    intros until 0; intros SGET.
    apply @Sym.retag_set_or with (p := a) in def_sJ; try assumption.
    rewrite SGET in def_sJ.
    destruct def_sJ as [OLD | NEW].
    - by apply IN_A' in OLD.
    - move: NEW => [cnew [Inew [Wnew [SGET' /esym[]]]]] *; subst.
      by apply IN_A' in SGET'.
    - by apply (enum_uniq (mem J')).
  }

  assert (SUBSET_S' : S' \subset Aprev :|: Sprev). {
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
     apply/(get_compartment_id_in_compartment SGMEM COMPSWD IDSWD IDSU AIN).
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

  assert (COMPARTMENTS :
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
              end). {
    intros a.
    replace (Sym.sget (SState SM SR pc@(Sym.PC F cid)
                              (SInternal Snext SiT SaJT SaST))
                      a)
       with (Sym.sget (SState SM SR pc@(Sym.PC F cid)
                              (SInternal (Snext + 1)%w SiT SaJT SaST))
                      a)
         by reflexivity.
    replace (Sym.sget (SState MS RS pc'@(Sym.PC JUMPED cid_sys) siS) a)
       with (Sym.sget (SState MS RS pcS siS) a)
         by reflexivity.
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
      rewrite /Sym.good_memory_tag in SGOOD_sS.
      specialize SGOOD_sS with a.
      move: SGOOD_sS.
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
  { apply/(get_compartment_id_in_compartment SGMEM COMPSWD IDSWD IDSU AIN).
    move/(_ pc') in COMPARTMENTS.
    rewrite /Sym.sget /= in def_xcIW.
    rewrite {2 3}/Sym.sget /= def_xcIW in COMPARTMENTS.
    case SGET: (Sym.sget _ _) COMPARTMENTS => [[|cpc' Ipc' Wpc'|]|] //=.
    rewrite RPREV.
    by intuition congruence. }

  assert (DIFF : cid <> Snext). {
    intros ?; subst.
    eapply Sym.sget_lt_next in RINT; [simpl in RINT | eassumption].
    by rewrite ltb_irrefl in RINT.
  }

  assert (DIFF_sys : cid_sys <> Snext). {
    intros ?; subst.
    eapply Sym.sget_lt_next in RINT; [simpl in RINT | eassumption].
    by rewrite ltb_irrefl in RINT.
  }

  assert (NIN : pc' \notin A'). {
    apply/negP => IN.
    have := Sym.retag_set_in_ok _ _ _ _ _ (enum_uniq (mem A')) def_sA pc'.
    rewrite (mem_enum (mem A')) => /(_ IN) [cpc' [Ipc' [Wpc' [THEN [OK NOW]]]]].
    move/eqP in OK; subst cpc'.
    move/id in def_xcIW.
    have := Sym.retag_set_or _ _ _ _ _ (enum_uniq (mem S')) SGOOD_sJ def_sS pc'.
    have := Sym.retag_set_or _ _ _ _ _ (enum_uniq (mem J')) SGOOD_sA def_sJ pc'.
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
  { by rewrite (in_compartment_get_compartment_id SGMEM COMPSWD IDSWD IDSU c_sys_in_AC pc_in_c_sys)
               def_LI. }

  have IN_Jsys : pc' \in Abs.jump_targets c_sys. {
    have /= -> := JTWF _ cid_sys c_sys_in_AC c_sys_id.
    rewrite in_set.
    move/(_ pc'): COMPARTMENTS.
    rewrite (sget_irrelevancies RS pcS MS) def_xcIW.
    case SGET': (Sym.sget _ _) => [[|cpc' Ipc' Wpc'|]|] //= Hcpc'.
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

  have TSI_s'_sA : forall X : {set word},
                     [disjoint A' & X] ->
                     tags_subsets_in
                       X
                       (SState SM SR pc@(Sym.PC F cid)
                               (SInternal (Snext + 1)%w SiT SaJT SaST))
                       sA.
  {
    move=> X DJX a.
    assert (NIN_a : a \in X -> ~ a \in A'). {
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
        move: (SGOOD_sA a) => SGOOD'; rewrite /Sym.good_memory_tag in SGOOD'.
        by destruct (Sym.sget sA a) as [[]|].
      + by rewrite (mem_enum (mem A')) /=; apply/negP.
    - generalize def_sA => def_sA';
        apply @Sym.retag_set_or_ok with (p := a) in def_sA';
        try first [assumption | exact (enum_uniq (mem A'))].
      move: def_sA' => [OLD | [cnew [Inew [Wnew [THEN [OK NOW]]]]]].
      + rewrite OLD.
        move: (SGOOD_sA a) => SGOOD'; rewrite /Sym.good_memory_tag in SGOOD'.
        by destruct (Sym.sget sA a) as [[]|].
      + by rewrite THEN NOW; repeat split; auto.
  }
   
  have TS_sA_sJ : tags_subsets sA sJ. {
    move=> a.
    generalize def_sJ => def_sJ';
      apply @Sym.retag_set_or with (p := a) in def_sJ';
      try first [assumption | exact (enum_uniq (mem J'))].
    move: def_sJ' => [OLD | [cnew [Inew [Wnew [THEN NOW]]]]].
    - rewrite -OLD.
      move: (SGOOD_sA a) => SGOOD'; rewrite /Sym.good_memory_tag in SGOOD'.
      by destruct (Sym.sget sA a) as [[]|].
    - by rewrite THEN NOW subsetU1.
  }
   
  have TS_sJ_sS : tags_subsets sJ (SState MS RS pcS siS). {
    move=> a.
    generalize def_sS => def_sS';
      apply @Sym.retag_set_or with (p := a) in def_sS';
      try first [assumption | exact (enum_uniq (mem S'))].
    move: def_sS' => [OLD | [cnew [Inew [Wnew [THEN NOW]]]]].
    - rewrite -OLD.
      move: (SGOOD_sJ a) => SGOOD'; rewrite /Sym.good_memory_tag in SGOOD'.
      by destruct (Sym.sget sJ a) as [[]|].
    - by rewrite THEN NOW subsetU1.
  }
   
  have TSI_s0_sS' : forall X : {set word},
                      [disjoint A' & X] ->
                      tags_subsets_in
                        X
                        (SState SM SR pc@(Sym.PC F cid)
                                (SInternal Snext SiT SaJT SaST))
                        (SState MS RS pc'@(Sym.PC JUMPED cid_sys) siS).
  {
    intros X DJX.
    eapply tags_subsets_in_trans.
    - rewrite /tags_subsets_in /Sym.sget.
      apply TSI_s'_sA; assumption.
    - eapply tags_subsets_in_trans.
      + apply tags_subsets_any_in; eassumption.
      + apply tags_subsets_any_in.
        rewrite /tags_subsets /Sym.sget.
        apply TS_sJ_sS; assumption.
  }
   
  have TSI_rest : forall c,
                    c \in rem_all <<Aprev,Jprev,Sprev>> AC ->
                    tags_subsets_in
                      (Abs.address_space c)
                      (SState SM SR pc@(Sym.PC F cid)
                              (SInternal Snext SiT SaJT SaST))
                      (SState MS RS pc'@(Sym.PC JUMPED cid_sys) siS).
  {
    move=> c; rewrite in_rem_all => /andP [NEQ IN] a.
    apply TSI_s0_sS'.
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
    move: TSI_rest => /(_ c c_in_AC' a).
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
    rewrite !in_cons in_rem_all => /or3P [/eqP -> {c'}|/eqP -> {c'}|/andP [c'_not_old c'_in_AC]].
    + suff ->: get_compartment_id (SState MS RS pc'@(Sym.PC JUMPED cid_sys) siS)
               <<Aprev :\: A',Jprev,Sprev>> = Some cid; first by [].
      rewrite (get_compartment_id_irrelevancies RS pcS).
      apply (retag_set_get_compartment_id_same_ids def_sS); first by [].
      apply (retag_set_get_compartment_id_same_ids def_sJ); first by [].
      apply (retag_set_get_compartment_id_disjoint def_sA).
      { rewrite disjoint_subset /=.
        apply/subsetP => p''.
        by rewrite in_setD => /andP []. }
      rewrite (get_compartment_id_irrelevancies' SR pc@(Sym.PC F cid) Snext).
      have := (get_compartment_id_subset _ _ RPREV).
      apply.
      * exact: pc'.
      * by rewrite in_setD IN_pc' NIN.
      * by rewrite subDset subsetUr.
    + suff ->: get_compartment_id (SState MS RS pc'@(Sym.PC JUMPED cid_sys) siS)
               <<A',J',S'>> = Some Snext; first by [].
      rewrite (get_compartment_id_irrelevancies RS pcS).
      apply (retag_set_get_compartment_id_same_ids def_sS); first by [].
      apply (retag_set_get_compartment_id_same_ids def_sJ); first by [].
      by apply (@retag_set_get_compartment_id_new_id _ _ _ _ <<A',J',S'>> Snext def_sA).
    + admit.
  - move=> c1 c2. admit.
    (*rewrite !in_cons !in_rem_all /=
            => /or3P [/eqP -> {c1}|/eqP -> {c1}|/andP [not_pred1 c1_in_AC]]
               /or3P [/eqP -> {c2}|/eqP -> {c2}|/andP [not_pred2 c2_in_AC]] //=.*)
  - move=> c' cid'. admit.
    (*rewrite !in_cons => /or3P [/eqP {c'} ->|/eqP {c'} ->|] /=.*)
  - move=> c' cid'. admit.
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
          specialize (SGOOD_sJ a); rewrite /Sym.good_memory_tag /= in SGOOD_sJ.
          by destruct (Sym.sget sJ a) as [[]|].
        + by rewrite THEN NOW.
        + exact (enum_uniq (pred_of_set J')).
      - eapply Sym.retag_set_preserves_next_id; eassumption.
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
          specialize (SGOOD_sS a); rewrite /Sym.good_memory_tag /= in SGOOD_sS.
          by destruct (Sym.sget (SState MS RS pcS siS) a) as [[]|].
        + by rewrite THEN NOW.
        + exact (enum_uniq (pred_of_set S')).
      - eapply Sym.retag_set_preserves_next_id; eassumption.
    }

    exact SGINT_sS.

(* END REFINEMENT *)

(*
  generalize RSC => /andP [/andP [/andP [/andP [/andP [/andP [/andP [/andP [
                    ANGET_i ANGET_aJ] ANGET_aS]
                    SNGET_i] SNGET_aJ] SNGET_aS]
                    /eqP NEQiaJ] /eqP NEQiaS] /eqP NEQaJaS].

  assert (NIN_i : ~ In isolate_addr A'). {
    intros IN.
    rewrite /Abs.syscalls_separated in ASS; move/forallb_forall in ASS.
    specialize (ASS _ IN_prev_AC); move: ASS => /orP [UAS | SAS].
    - rewrite /Abs.user_address_space /= in UAS; move/forallb_forall in UAS.
      assert (IN' : In isolate_addr Aprev)
        by by move/subset_spec in SUBSET_A'; apply SUBSET_A'.
      specialize (UAS _ IN').
      by move/negP in ANGET_i.
    - rewrite /Abs.syscall_address_space in SAS.
      cbv [Abs.address_space] in SAS.
      destruct Aprev as [|sc [|]]; try done.
      move: SAS => /andP [NONE ELEM].
      assert (A' = []). {
        destruct A' as [|a' A']; [reflexivity|].
        move/subset_spec in SUBSET_A'.
        apply SUBSET_A' in IN.
        inversion IN; subst; try done.
        specialize (SUBSET_A' a' (or_introl erefl)).
        inversion SUBSET_A'; subst; try done.
        inversion IN_pc'_Aprev; subst; try done.
        by elim NIN; left.
      }
      by subst A'.
  }

  assert (NIN_aJ : ~ In add_to_jump_targets_addr A'). {
    intros IN.
    rewrite /Abs.syscalls_separated in ASS; move/forallb_forall in ASS.
    specialize (ASS _ IN_prev_AC); move: ASS => /orP [UAS | SAS].
    - rewrite /Abs.user_address_space /= in UAS; move/forallb_forall in UAS.
      assert (IN' : In add_to_jump_targets_addr Aprev)
        by by move/subset_spec in SUBSET_A'; apply SUBSET_A'.
      specialize (UAS _ IN').
      by move/negP in ANGET_aJ.
    - rewrite /Abs.syscall_address_space in SAS.
      cbv [Abs.address_space] in SAS.
      destruct Aprev as [|sc [|]]; try done.
      move: SAS => /andP [NONE ELEM].
      assert (A' = []). {
        destruct A' as [|a' A']; [reflexivity|].
        move/subset_spec in SUBSET_A'.
        apply SUBSET_A' in IN.
        inversion IN; subst; try done.
        specialize (SUBSET_A' a' (or_introl erefl)).
        inversion SUBSET_A'; subst; try done.
        inversion IN_pc'_Aprev; subst; try done.
        by elim NIN; left.
      }
      by subst A'.
  }

  assert (NIN_aS : ~ In add_to_store_targets_addr A'). {
    intros IN.
    rewrite /Abs.syscalls_separated in ASS; move/forallb_forall in ASS.
    specialize (ASS _ IN_prev_AC); move: ASS => /orP [UAS | SAS].
    - rewrite /Abs.user_address_space /= in UAS; move/forallb_forall in UAS.
      assert (IN' : In add_to_store_targets_addr Aprev)
        by by move/subset_spec in SUBSET_A'; apply SUBSET_A'.
      specialize (UAS _ IN').
      by move/negP in ANGET_aS.
    - rewrite /Abs.syscall_address_space in SAS.
      cbv [Abs.address_space] in SAS.
      destruct Aprev as [|sc [|]]; try done.
      move: SAS => /andP [NONE ELEM].
      assert (A' = []). {
        destruct A' as [|a' A']; [reflexivity|].
        move/subset_spec in SUBSET_A'.
        apply SUBSET_A' in IN.
        inversion IN; subst; try done.
        specialize (SUBSET_A' a' (or_introl erefl)).
        inversion SUBSET_A'; subst; try done.
        inversion IN_pc'_Aprev; subst; try done.
        by elim NIN; left.
      }
      by subst A'.
  }

  generalize def_sA => GETS_sA;
    move/Sym.retag_set_preserves_get_definedness in GETS_sA.
  generalize def_sJ => GETS_sJ;
    move/Sym.retag_set_preserves_get_definedness in GETS_sJ.
  generalize def_sS => GETS_sS;
    move/Sym.retag_set_preserves_get_definedness in GETS_sS.
  simpl in *.

  assert (SNGET_sA_i : ~~ is_some (get (Symbolic.mem sA) isolate_addr))
    by by apply/negP; intros H; apply GETS_sA in H; move/negP in SNGET_i.
  assert (SNGET_sA_aJ : ~~ is_some (get (Symbolic.mem sA)
                                        add_to_jump_targets_addr))
    by by apply/negP; intros H; apply GETS_sA in H; move/negP in SNGET_aJ.
  assert (SNGET_sA_aS : ~~ is_some (get (Symbolic.mem sA)
                                        add_to_store_targets_addr))
    by by apply/negP; intros H; apply GETS_sA in H; move/negP in SNGET_aS.

  assert (SNGET_sJ_i : ~~ is_some (get (Symbolic.mem sJ) isolate_addr))
    by by apply/negP; intros H; apply GETS_sJ in H; move/negP in SNGET_sA_i.
  assert (SNGET_sJ_aJ : ~~ is_some (get (Symbolic.mem sJ)
                                        add_to_jump_targets_addr))
    by by apply/negP; intros H; apply GETS_sJ in H; move/negP in SNGET_sA_aJ.
  assert (SNGET_sJ_aS : ~~ is_some (get (Symbolic.mem sJ)
                                        add_to_store_targets_addr))
    by by apply/negP; intros H; apply GETS_sJ in H; move/negP in SNGET_sA_aS.

  assert (SNGET_sS_i : ~~ is_some (get MS isolate_addr))
    by by apply/negP; intros H; apply GETS_sS in H; move/negP in SNGET_sJ_i.
  assert (SNGET_sS_aJ : ~~ is_some (get MS add_to_jump_targets_addr))
    by by apply/negP; intros H; apply GETS_sS in H; move/negP in SNGET_sJ_aJ.
  assert (SNGET_sS_aS : ~~ is_some (get MS add_to_store_targets_addr))
    by by apply/negP; intros H; apply GETS_sS in H; move/negP in SNGET_sJ_aS.

  assert (SGINT_sA : Sym.good_internal sA). {
    eapply Sym.retag_set_updating_preserves_good_internal;
      try apply def_sA; try eauto 1; apply/eqP; assumption.
  }
  assert (SGINT_sJ : Sym.good_internal sJ). {
    generalize def_sJ => GETS;
      move/Sym.retag_set_preserves_get_definedness in GETS.
    eapply Sym.good_internal_equiv; try apply SGINT_sA; try (by apply/eqP);
      auto.
    - intros a.
      generalize def_sJ => def_sJ';
        apply @Sym.retag_set_or with (p := a) in def_sJ'; try assumption.
      move: def_sJ' => [OLD | [xnew [cnew [Inew [Wnew [THEN NOW]]]]]].
      + rewrite OLD.
        specialize (SGOOD_sJ a); rewrite /Sym.good_memory_tag /= in SGOOD_sJ.
        by destruct (Sym.sget sJ a) as [[? []]|].
      + by rewrite THEN NOW.
    - eapply Sym.retag_set_preserves_next_id; eassumption.
  }
  assert (SGINT_sS : Sym.good_internal (SState MS RS pcS siS)). {
    generalize def_sS => GETS;
      move/Sym.retag_set_preserves_get_definedness in GETS.
    eapply Sym.good_internal_equiv; try apply SGINT_sJ; try (by apply/eqP);
      auto.
    - intros a.
      generalize def_sS => def_sS';
        apply @Sym.retag_set_or with (p := a) in def_sS'; try assumption.
      move: def_sS' => [OLD | [xnew [cnew [Inew [Wnew [THEN NOW]]]]]].
      + rewrite OLD.
        specialize (SGOOD_sS a); rewrite /Sym.good_memory_tag /= in SGOOD_sS.
        by destruct (Sym.sget (SState MS RS pcS siS) a) as [[? []]|].
      + by rewrite THEN NOW.
    - eapply Sym.retag_set_preserves_next_id; eassumption.
  }

  assert (TSI_s'_sA : forall X,
                        is_set X ->
                        disjoint A' X ->
                        tags_subsets_in
                          X
                          (SState SM SR pc@(Sym.PC F cid)
                                  (SInternal (Snext + 1)%w SiT SaJT SaST))
                          sA). {
    move=> X SET_X DJX a.
    assert (NIN_a : In a X -> ~ In a A'). {
      move=> IN_a IN'_a.
      rewrite /disjoint in DJX.
      assert (IN' : In a (set_intersection A' X))
        by by apply set_intersection_spec.
      by destruct (set_intersection A' X) as [|z A'X].
    }
    destruct (elem a X) as [IN_X | NIN_X].
    - specialize (NIN_a IN_X).
      generalize def_sA => def_sA';
        apply @Sym.retag_set_not_in with (p := a) in def_sA'; try assumption.
      rewrite def_sA'.
      move: (SGOOD_sA a) => SGOOD'; rewrite /Sym.good_memory_tag in SGOOD'.
      by destruct (Sym.sget sA a) as [[? []]|].
    - generalize def_sA => def_sA';
        apply @Sym.retag_set_or_ok with (p := a) in def_sA'; try assumption.
      move: def_sA' => [OLD | [xnew [cnew [Inew [Wnew [THEN [OK NOW]]]]]]].
      + rewrite OLD.
        move: (SGOOD_sA a) => SGOOD'; rewrite /Sym.good_memory_tag in SGOOD'.
        by destruct (Sym.sget sA a) as [[? []]|].
      + rewrite THEN NOW; repeat split; auto.
        move=> ? //.
  }

  assert (TS_sA_sJ : tags_subsets sA sJ). {
    move=> a.
    generalize def_sJ => def_sJ';
      apply @Sym.retag_set_or with (p := a) in def_sJ'; try assumption.
    move: def_sJ' => [OLD | [xnew [cnew [Inew [Wnew [THEN NOW]]]]]].
    - rewrite -OLD.
      move: (SGOOD_sA a) => SGOOD'; rewrite /Sym.good_memory_tag in SGOOD'.
      by destruct (Sym.sget sA a) as [[? []]|].
    - rewrite THEN NOW; auto.
  }

  assert (TS_sJ_sS : tags_subsets sJ (SState MS RS pcS siS)). {
    move=> a.
    generalize def_sS => def_sS';
      apply @Sym.retag_set_or with (p := a) in def_sS'; try assumption.
    move: def_sS' => [OLD | [xnew [cnew [Inew [Wnew [THEN NOW]]]]]].
    - rewrite -OLD.
      move: (SGOOD_sJ a) => SGOOD'; rewrite /Sym.good_memory_tag in SGOOD'.
      by destruct (Sym.sget sJ a) as [[? []]|].
    - rewrite THEN NOW; auto.
  }

  assert (TSI_s0_sS' : forall X,
                         is_set X ->
                         disjoint A' X ->
                         tags_subsets_in
                           X
                           (SState SM SR pc@(Sym.PC F cid)
                                   (SInternal Snext SiT SaJT SaST))
                           (SState MS RS pc'@(Sym.PC JUMPED cid_sys) siS)). {
    intros X SET_X DJX.
    eapply tags_subsets_in_trans.
    - rewrite /tags_subsets_in /Sym.sget.
      apply TSI_s'_sA; assumption.
    - eapply tags_subsets_in_trans.
      + apply tags_subsets_any_in; eassumption.
      + apply tags_subsets_any_in.
        rewrite /tags_subsets /Sym.sget.
        apply TS_sJ_sS; assumption.
  }

  assert (TSI_rest : forall c,
                       In c (delete <<Aprev,Jprev,Sprev>> AC) ->
                       tags_subsets_in
                         (Abs.address_space c)
                         (SState SM SR pc@(Sym.PC F cid)
                                 (SInternal Snext SiT SaJT SaST))
                         (SState MS RS pc'@(Sym.PC JUMPED cid_sys) siS)).
  {
    move=> c /delete_in_iff [NEQ IN] a.
    apply TSI_s0_sS'.
    - move/forallb_forall in AGOODS; apply AGOODS in IN; auto.
    - assert (DJ' : disjoint Aprev (Abs.address_space c)). {
        replace Aprev with (Abs.address_space <<Aprev,Jprev,Sprev>>)
          by reflexivity.
        apply Abs.good_compartments__in2_disjoint with (ops := ops) (C := AC);
          try assumption.
        apply in_neq_in2; auto.
      }
      apply disjoint_subset with (ys := Aprev); try assumption.
      + move/forallb_forall in AGOODS; apply AGOODS in IN; auto.
      + apply subset_spec; assumption.
  }

  assert (RC_rest : forall c,
                      In c (delete <<Aprev,Jprev,Sprev>> AC) ->
                      refined_compartment
                        c (SState SM SR pc@(Sym.PC F cid)
                                  (SInternal Snext SiT SaJT SaST))
                      = refined_compartment
                          c (SState MS RS pc'@(Sym.PC JUMPED cid_sys) siS)). {
    intros c IN_c.
    move/forallb_forall in RCOMPS; lapply (RCOMPS c);
      [move=> RCSOME | apply delete_in_iff in IN_c; tauto].
    match type of RCSOME with
      | is_some ?rc = true =>
        destruct rc as [c_cid|] eqn:RC; [clear RCSOME | done]
    end.
    eapply TSI_rest, refined_compartment_untouched_preserved in IN_c; eauto 1.
  }

  assert (NOT_SYSCALL_prev : ~ Abs.syscall_address_space
                                 AM <<Aprev,Jprev,Sprev>>). {
    move=> SAS.
    rewrite /Abs.syscall_address_space (lock elem) /= in SAS.
    destruct Aprev as [|sc [|]]; auto.
    move: PNI => /(Abs.permitted_now_in_spec _) PNI.
    destruct IN_pc'_Aprev; [subst pc' | done].
    destruct A' as [|a' A']; [discriminate|].
    move/subset_spec in SUBSET_A'.
    move: (SUBSET_A' a' (or_introl erefl)) => [EQ | []]; subst a'.
    apply NIN; auto.
  }

  assert (USER_prev : Abs.user_address_space AM <<Aprev,Jprev,Sprev>>). {
    move/forallb_forall in ASS.
    move: (ASS _ IN_prev_AC) => /orP [UAS | SAS] //.
  }

  generalize IN_c_sys => /Abs.in_compartment_spec [IN_c_sys_AC IN_pc_c_sys].

  assert (NOT_USER_c_sys : ~ Abs.user_address_space AM c_sys). {
    move=> /forallb_forall UAS.
    specialize (UAS _ IN_pc_c_sys); simpl in UAS.
    rewrite -(lock eq) in IS_ISOLATE; subst.
    by move/negP in ANGET_i.
  }

  assert (SYSCALL_c_sys : Abs.syscall_address_space AM c_sys). {
    move/forallb_forall in ASS.
    move: (ASS _ IN_c_sys_AC) => /orP [UAS | SAS] //.
  }

  assert (DIFF_prev_c_sys : <<Aprev,Jprev,Sprev>> <> c_sys)
    by by move=> ?; subst.

  assert (R_c_sys' : refined_compartment
                       c_sys
                       (SState MS RS pc'@(Sym.PC JUMPED cid_sys) siS)
                       ?= cid_sys). {
    rewrite RC_rest in R_c_sys; auto.
    apply delete_in_iff; split.
    - auto.
    - apply Abs.in_compartment_spec in IN_c_sys; tauto.
  }

  assert (NEW_CIDS : forall p,
            match
              Sym.sget (SState SM SR pc@(Sym.PC F cid)
                               (SInternal Snext SiT SaJT SaST))
                       p,
              Sym.sget (SState MS RS pc'@(Sym.PC JUMPED cid_sys) siS) p
            with
              | Some _@(Sym.DATA cid1 I1 W1), Some _@(Sym.DATA cid2 I2 W2) =>
                (cid1 = cid2 /\ cid2 <> Snext /\ ~ In p A') \/
                (cid1 = cid  /\ cid2 =  Snext /\ In p A')
              | None , None =>
                True
              | _ , _ =>
                False
            end). {
    move=> a; destruct (elem a A') as [IN_a | NIN_a].
    - generalize def_sA => def_sA';
        apply @Sym.retag_set_in_ok with (p := a) in def_sA'; try assumption.
      move: def_sA' => [y [cidy [Iy [Wy [THEN [/eqP OK NOW]]]]]]; subst cidy.
      rewrite /Sym.sget /= in THEN; rewrite {1}/Sym.sget /= THEN.
      move/id in TS_sA_sJ; move/id in TS_sJ_sS.
      specialize (TS_sA_sJ a); specialize (TS_sJ_sS a).
      rewrite NOW in TS_sA_sJ.
      replace (Sym.sget (SState MS RS pc'@(Sym.PC JUMPED cid_sys) siS) a)
         with (Sym.sget (SState MS RS pcS                         siS) a)
           by reflexivity.
      destruct (Sym.sget sJ                     a) as [[xJ [|cidJ IJ WJ|]]|],
               (Sym.sget (SState MS RS pcS siS) a) as [[xS [|cidS IS WS|]]|];
        try done.
      by repeat invh and; subst; right.
    - assert (SET_a : is_set [a]) by auto.
      assert (DJ_a : disjoint A' [a]). {
        destruct A' as [|a' A']; [done|].
        rewrite /disjoint /=.
        destruct (a' <=> a) eqn:CMP.
        + apply compare_eq in CMP; subst; elim NIN_a; auto.
        + destruct (set_intersection A' [a]) as [|z zs] eqn:SI; [done|].
          assert (IN_z : In z (set_intersection A' [a])) by (rewrite SI; auto).
          apply set_intersection_spec in IN_z; eauto 2.
          move: IN_z => [IN_z [?|[]]]; subst.
          assert (z = a') by (simpl in NIN_a; tauto); subst.
          by apply lt_irrefl in CMP.
        + done.
      }
      specialize (TSI_s0_sS' [a] SET_a DJ_a a); move/id in TSI_s0_sS'.
      destruct (Sym.sget
                  (SState SM SR pc@(Sym.PC F cid)
                          (SInternal Snext SiT SaJT SaST))
                  a) as [[y [|cidy Iy Wy|]]|] eqn:ORIG,
               (Sym.sget
                  (SState MS RS pc'@(Sym.PC JUMPED cid_sys) siS)
                  a) as [[y' [|cidy' Iy' Wy'|]]|];
        try done.
      move: TSI_s0_sS' => [E _]; specialize (E (or_introl erefl)); subst cidy'.
      left; repeat split; auto.
      apply Sym.sget_lt_next in ORIG; [simpl in ORIG|assumption].
      by move=> ?; subst; apply lt_irrefl in ORIG.
  }

  assert (RC_prev : refined_compartment
                      <<set_difference Aprev A', Jprev, Sprev>>
                      (SState MS RS pc'@(Sym.PC JUMPED cid_sys) siS)
                      ?= cid). {
    admit.
  }

  assert (RC_new : refined_compartment
                     <<A',J',S'>>
                     (SState MS RS pc'@(Sym.PC JUMPED cid_sys) siS)
                     ?= cid). {
    admit.
  }

  constructor; simpl.
  - apply eq_refl.
  - move/id in def_sA; move/id in def_sJ; move/id in def_sS;
      apply Sym.retag_set_preserves_regs in def_sA;
      apply Sym.retag_set_preserves_regs in def_sJ;
      apply Sym.retag_set_preserves_regs in def_sS;
      simpl in *.
    replace RS with SR by congruence.
    assumption.
  - apply RMEMS'.
  - split.
    + rewrite (lock refined_compartment) /= -(lock refined_compartment)
              RC_prev RC_new
              (lock refined_compartment) /= -(lock refined_compartment).
      eapply forallb_impl_in; [|apply delete_preserves_forallb, RCOMPS].
      simpl; move=> c IN.
      by eapply RC_rest in IN; rewrite IN.
    + admit.
  - apply/andP; split; [apply eq_refl | apply/eqP; apply R_c_sys'].
  - rewrite /refine_memory /refine_mem_loc_b /pointwise in RMEMS'.
    rewrite /refine_syscall_addrs_b /= in RSC *.
    repeat move: RSC => /andP [RSC ?].
    andb_true_split; auto;
      match goal with
        | |- context[get MS ?addr] =>
          by specialize (RMEMS' addr);
             destruct (get AM addr), (get MS addr) as [[? []]|] eqn:GET';
             rewrite GET' in RMEMS' *
      end.
  - apply SGINT_sS.
*)
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
        { rewrite (in_compartment_get_compartment_id SGMEM COMPSWD IDSWD IDSU c_in_AC pc_in_c).
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
  rewrite (in_compartment_get_compartment_id SGMEM COMPSWD IDSWD IDSU c_in_AC pc_in_c)
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
  clear S I; move=> ast sst sst' AGOOD REFINE SSTEP.
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
    destruct tpc as [F cid'| |]; try discriminate;
      destruct ti as [|cid'' I W|]; try discriminate.
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
      destruct told as [| |]; try discriminate;
      undo1 def_rvec cid;
      undo1 NEXT regs';
      unfold Sym.can_execute,Sym.compartmentalization_rvec in *;
      unoption; simpl in *.
    destruct tpc as [F cid'| |]; try discriminate;
      destruct ti as [|cid'' I W|]; try discriminate.
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
    destruct tpc as [F cid'| |]; try discriminate;
      destruct ti as [|cid'' I W|]; try discriminate.
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
    destruct tpc as [F cid'| |]; try discriminate;
      destruct ti as [|cid'' I W|]; try discriminate.
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
    destruct tpc as [F cid'| |]; try discriminate;
      destruct ti as [|cid'' I'' W''|]; try discriminate.
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
    destruct tpc as [F cid'| |]; try discriminate;
      destruct ti as [|cid'' I'' W''|]; try discriminate.
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
            apply (get_compartment_id_in_compartment SGMEM COMPSWD IDSWD IDSU ac_in_AC).
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
        destruct RINT as [? [? RINT]].
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
    destruct tpc as [F cid'| |]; try discriminate;
      destruct ti as [|cid'' I W|]; try discriminate.
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
    destruct tpc as [F cid'| |]; try discriminate;
      destruct ti as [|cid'' I W|]; try discriminate.
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
    destruct tpc as [F cid'| |]; try discriminate;
      destruct ti as [|cid'' I W|]; try discriminate.
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
