Require Import List. Import ListNotations.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Require Import lib.utils lib.ordered lib.partial_maps common.common.
Require Import symbolic.symbolic symbolic.rules.
Require Import lib.haskell_notation.
Require Import sfi.common lib.list_utils lib.set_utils sfi.isolate_sets.
Require Import sfi.abstract sfi.symbolic.

Set Bullet Behavior "Strict Subproofs".
Import DoNotation.

Section RefinementSA.

Set Implicit Arguments.

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
  {sfi_syscalls : sfi_syscall_addrs t}.

Notation word    := (word t).
Notation stag    := (@Sym.stag t).
Notation sym_sfi := (@Sym.sym_sfi t ops).

Notation satom  := (atom word stag).
Notation svalue := (@val word stag).
Notation slabel := (@common.tag word stag).

Notation astate    := (@Abs.state t).
Notation sstate    := (@Symbolic.state t sym_sfi).
Notation AState    := (@Abs.State t).
Notation SState    := (@Symbolic.State t sym_sfi).
Notation SInternal := (@Sym.Internal t).

Notation astep := Abs.step.
Notation sstep := Sym.step.

Hint Immediate word_map_axioms.
Hint Immediate reg_map_axioms.

Arguments Sym.sget {_ _ _} s p : simpl never.
Arguments Sym.supd {_ _ _} s p v : simpl never.

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

Section With_EqType_refined_compartment.
Import Sym.
Definition refined_compartment (c   : Abs.compartment t)
                               (sst : sstate) : option word :=
  let: <<A,J,S>> := c in
  do! sxs <- map_options (Sym.sget sst) A;
  do! sc  <- the =<< map_options (stag_compartment ∘ slabel) sxs;
             (* modulo emptiness *)
  do! guard? forallb (set_elem sc) <$>
               map_options (stag_incoming ∘ slabel <=< Sym.sget sst) J;
  do! guard? forallb (set_elem sc) <$>
               map_options (stag_writers  ∘ slabel <=< Sym.sget sst) S;
  Some sc.
End With_EqType_refined_compartment.

Definition refine_compartment_tag (C   : list (Abs.compartment t))
                                  (sst : sstate)
                                  (p   : word) : Prop :=
  match Sym.sget sst p with
    | Some (_ @ (Sym.DATA cid I W)) =>
      is_set I /\ is_set W /\
      exists c,
        C ⊢ p ∈ c /\
        forall p',
          match Sym.sget sst p' with
            | Some (_ @ (Sym.DATA cid' I' W')) =>
              (cid = cid' <-> C ⊢ p' ∈ c) /\
              (In cid I'   -> In p' (Abs.jump_targets  c)) /\
              (In cid W'   -> In p' (Abs.shared_memory c))
            | Some (_ @ _) =>
              False
            | None =>
              True
          end
    | Some (_ @ _) =>
      False
    | None =>
      True
  end.

Definition refine_compartments (C : list (Abs.compartment t))
                               (sst : sstate) : Prop :=
  forallb (is_some ∘ refined_compartment ^~ sst) C /\
  forall p, refine_compartment_tag C sst p.

Definition refine_previous_b (sk : where_from) (prev : Abs.compartment t)
                             (sst : sstate) : bool :=
  match Symbolic.pc sst with
    | _ @ (Sym.PC F cid) => (sk == F) &&
                            (refined_compartment prev sst == Some cid)
    | _ @ _ => false
  end.

Definition refine_syscall_addrs_b (AM : memory t) (SM : Sym.memory t) : bool :=
  ~~ is_some (get AM isolate_addr)                        &&
  ~~ is_some (get AM add_to_jump_targets_addr)            &&
  ~~ is_some (get AM add_to_shared_memory_addr)           &&
  ~~ is_some (get SM isolate_addr)                        &&
  ~~ is_some (get SM add_to_jump_targets_addr)            &&
  ~~ is_some (get SM add_to_shared_memory_addr)           &&
  (isolate_addr             != add_to_jump_targets_addr)  &&
  (isolate_addr             != add_to_shared_memory_addr) &&
  (add_to_jump_targets_addr != add_to_shared_memory_addr).

Record refine (ast : astate) (sst : sstate) : Prop := RefineState
  { pc_refined           : refine_pc_b            (Abs.pc           ast)
                                                  (Symbolic.pc      sst)
  ; regs_refined         : refine_registers       (Abs.regs         ast)
                                                  (Symbolic.regs    sst)
  ; mems_refined         : refine_memory          (Abs.mem          ast)
                                                  (Symbolic.mem     sst)
  ; compartments_refined : refine_compartments    (Abs.compartments ast)
                                                  sst
  ; previous_refined     : refine_previous_b      (Abs.step_kind    ast)
                                                  (Abs.previous     ast)
                                                  sst
  ; syscalls_refined     : refine_syscall_addrs_b (Abs.mem          ast)
                                                  (Symbolic.mem     sst)
  ; internal_refined     : Sym.good_internal      sst }.

Generalizable All Variables.

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
     rewrite ->forallb_forall in *; simpl in *;
  move/map_options_in in def_sxs;
  destruct (map_options _ sxs) as [cids|] eqn:MAP_sxs; simpl in *;
    [|discriminate];
  move/map_options_in in MAP_sxs;
  move: def_sc => /the_spec [NE_cids SAME_cid];
  unfold SetoidClass.equiv,SetoidDec.eq_setoid in SAME_cid
  end.

Ltac explode_refined_compartment RC A J S :=
  match type of RC with
    | refined_compartment ?c _ ?= _ => destruct c as [A J S]
  end;
  explode_refined_compartment' RC.

(* Could be reused more than it is *)
Lemma refined_sget_in_compartment : forall C c cid sst x I W p,
  Abs.good_compartments C ->
  In c C ->
  (forall p, refine_compartment_tag C sst p) ->
  refined_compartment c sst ?= cid ->
  Sym.sget sst p ?= x@(Sym.DATA cid I W) ->
  C ⊢ p ∈ c.
Proof.
  clear S I; intros until 0; intros GOODS IN_c_C RCTAGS REFINED SGET.
  move: (RCTAGS p) => RCTAGS'; rewrite /refine_compartment_tag SGET in RCTAGS';
    move: RCTAGS' => [SET_I [SET_W [c' [IC' RTAG]]]].
  let S := fresh "S" in explode_refined_compartment REFINED A J S.
  move: NE_cids => /nonempty_iff_in [temp IN_temp];
    generalize IN_temp => IN_cid;
    apply SAME_cid in IN_temp; subst; clear SAME_cid.
  apply MAP_sxs in IN_cid.
  destruct IN_cid as [[w Lw] [TAG IN_sxs]].
  apply def_sxs in IN_sxs.
  destruct IN_sxs as [p' [SGET' IN']].
  assert (IC_p'_c : C ⊢ p' ∈ <<A,J,S>>) by by apply Abs.in_compartment_spec.
  specialize RTAG with p'; rewrite SGET' in RTAG.
  destruct Lw; try done; simpl in *.
  inversion TAG; subst.
  move: RTAG => [SAME _]; assert (IC_p'_c' : C ⊢ p' ∈ c') by by apply SAME.
  replace c' with <<A,J,S>> in * by eauto 3.
  assumption.
Qed.

Theorem refine_good : forall `(REFINE : refine ast sst),
  Abs.good_state ast ->
  Sym.good_state sst.
Proof.
  clear S I.
  move=> [Apc AR AM AC Ask Aprev]
         [SM SR [Spc Lpc] [Snext SiT SaJT SaST]]
         [RPC RREGS RMEMS RCOMPS RPREV RSC RINT]
         /andP [/andP [/andP [ELEM GOODS] SS] SP];
    simpl in *;
    unfold refine_compartments in RCOMPS; simpl in RCOMPS;
    destruct RCOMPS as [RCOMPS RTAGS];
  unfold Sym.good_state, Abs.good_state in *; simpl in *.
  repeat split.
  - intros p; unfold Sym.good_memory_tag.
    unfold refine_memory, pointwise in RMEMS; specialize RMEMS with p.
    specialize RTAGS with p; unfold refine_compartment_tag in RTAGS;
      simpl in RTAGS.
    unfold Sym.sget in *.
    destruct (get SM p) as [[Sx SL]|] eqn:SGET; rewrite SGET in RTAGS *.
    + destruct (get AM p) as [Ax|] eqn:AGET; [simpl in RMEMS | elim RMEMS].
      destruct SL as [|c I W|]; solve [apply/andP; tauto | done].
    + destruct (p == isolate_addr);
        [|destruct (p == add_to_jump_targets_addr);
          [|destruct (p == add_to_shared_memory_addr)]];
        unfold Sym.sget in *; simpl in *.
      * destruct SiT; try done.
        by repeat invh and; apply/andP.
      * destruct SaJT; try done.
        by repeat invh and; apply/andP.
      * destruct SaST; try done.
        by repeat invh and; apply/andP.
      * done.
  - intros r; unfold Sym.good_register_tag.
    unfold refine_registers, pointwise in RREGS; specialize RREGS with r.
    destruct (get SR r) as [[Sx SL]|] eqn:SGET; rewrite SGET; [|trivial].
    destruct (get AR r) as [Ax|] eqn:AGET; [|elim RREGS].
    unfold refine_reg_b in RREGS.
    by destruct SL.
  - destruct Lpc; try discriminate.
    move: RPREV => /andP [/eqP? /eqP RPREV]; subst.
    let S := fresh "S" in explode_refined_compartment RPREV A J S.
    destruct cids as [|c' cids]; [discriminate | clear NE_cids].
    specialize (SAME_cid c' (or_introl Logic.eq_refl)); subst.
    specialize MAP_sxs with c;
      move: MAP_sxs => [MAP_sxs _];
      specialize (MAP_sxs (or_introl Logic.eq_refl)).
    move: MAP_sxs => [[x Lx] [TAG IN]].
    apply def_sxs in IN.
    destruct IN as [p [GET IN]].
    rewrite /refine_memory /pointwise /refine_mem_loc_b in RMEMS.
    specialize RMEMS with p; exists p;
      specialize RTAGS with p;
      rewrite /refine_compartment_tag in RTAGS.
    unfold Sym.sget in *.
    destruct (get SM p) eqn:SGET; rewrite SGET in RTAGS GET *; simpl in *.
    + inversion GET; subst; simpl in *.
      destruct (get AM p); [|done].
      destruct Lx as [|c' I W|]; try done.
      simpl in TAG; inversion TAG; subst; eauto.
    + destruct (p == isolate_addr);
        [ destruct SiT; try done
        | destruct (p == add_to_jump_targets_addr);
          [ destruct SaJT; try done
          | destruct (p == add_to_shared_memory_addr);
            [ destruct SaST; try done
            | discriminate ]]];
        inversion GET; subst;
        simpl in TAG; inversion TAG; subst;
        eauto.
  - assumption.
Qed.

Ltac unoption :=
  repeat match goal with
    | EQ  : Some _ = Some _ |- _ => inversion EQ; subst; clear EQ
    | NEQ : Some _ = None   |- _ => discriminate
    | NEQ : None   = Some   |- _ => discriminate
    | EQ  : None   = None   |- _ => clear EQ
  end.

Lemma prove_refined_compartment : forall pc instr cid I W
                                         AC c sst,
  Sym.sget sst pc ?= instr@(Sym.DATA cid I W) ->
  Abs.good_compartments AC ->
  forallb (is_some ∘ refined_compartment^~ sst) AC ->
  (forall p, refine_compartment_tag AC sst p) ->
  AC ⊢ pc ∈ c ->
  is_set I ->
  (forall p' : word,
     match Sym.sget sst p' with
       | Some _@(Sym.PC _ _) => False
       | Some _@(Sym.DATA cid' I' W') =>
         (cid = cid' <-> AC ⊢ p' ∈ c) /\
         (In cid I' -> In p' (Abs.jump_targets c)) /\
         (In cid W' -> In p' (Abs.shared_memory c))
       | Some _@Sym.REG => False
       | None => True
     end) ->
  refined_compartment c sst ?= cid.
Proof.
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

Lemma prove_refined_compartment' : forall pc instr cid cid' cid'' I W F
                                          AR AM AC Ask Aprev c sst,
  Sym.sget sst pc ?= instr@(Sym.DATA cid'' I W) ->
  (do! guard (cid'' == cid') || ((F == JUMPED) && set_elem cid' I);
   Some cid'') ?= cid ->
  Abs.good_state (AState pc AR AM AC Ask Aprev) ->
  forallb (is_some ∘ refined_compartment^~ sst) AC ->
  (forall p, refine_compartment_tag AC sst p) ->
  AC ⊢ pc ∈ c ->
  is_set I ->
  (forall p' : word,
     match Sym.sget sst p' with
       | Some _@(Sym.PC _ _) => False
       | Some _@(Sym.DATA cid''' I' W') =>
         (cid'' = cid''' <-> AC ⊢ p' ∈ c) /\
         (In cid'' I' -> In p' (Abs.jump_targets c)) /\
         (In cid'' W' -> In p' (Abs.shared_memory c))
       | Some _@Sym.REG => False
       | None => True
     end) ->
  refined_compartment c sst == Some cid.
Proof.
  intros until 0; intros SGET GUARD.
  undo1 GUARD COND; inversion GUARD; subst.
  intros; apply/eqP; eapply prove_refined_compartment; eauto.
Qed.

Lemma prove_permitted_now_in : forall pc instr cid cid' cid'' I W F
                                      AR AM AC Ask Aprev
                                      mem reg int
                                      c,
  let sst := (SState mem reg pc@(Sym.PC F cid') int) in
  Sym.sget sst pc ?= instr@(Sym.DATA cid'' I W) ->
  (Ask == F) && (refined_compartment Aprev sst == Some cid') ->
  (do! guard (cid'' == cid') || ((F == JUMPED) && set_elem cid' I);
   Some cid'') ?= cid ->
  Abs.good_state (AState pc AR AM AC Ask Aprev) ->
  Sym.good_state sst ->
  (forall p, refine_compartment_tag AC sst p) ->
  AC ⊢ pc ∈ c ->
  is_set I ->
  (forall p' : word,
     match Sym.sget sst p' with
      | Some _@(Sym.PC _ _) => False
      | Some _@(Sym.DATA cid''' I' W') =>
          (cid'' = cid''' <-> AC ⊢ p' ∈ c) /\
          (In cid'' I' -> In p' (Abs.jump_targets c)) /\
          (In cid'' W' -> In p' (Abs.shared_memory c))
      | Some _@Sym.REG => False
      | None => True
     end) ->
  Abs.permitted_now_in AC Ask Aprev pc ?= c.
Proof.
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

Ltac solve_permitted_now_in :=
  match goal with
    | RPREV : context[refine_previous_b],
      PC    : get _ ?pc ?= _
      |- Abs.permitted_now_in _ _ _ ?pc ?= _ =>
      rewrite /refine_previous_b /= in RPREV;
      eapply prove_permitted_now_in; try eassumption;
      rewrite /Sym.sget PC; reflexivity
  end.

Definition equivalued (sst1 sst2 : sstate) : Prop :=
  forall p,
    match Sym.sget sst1 p , Sym.sget sst2 p with
      | Some (x1@_) , Some (x2@_) => x1 = x2
      | None        , None        => True
      | _           , _           => False
    end.

Definition equilabeled (sst1 sst2 : sstate) : Prop :=
  forall p,
    match Sym.sget sst1 p , Sym.sget sst2 p with
      | Some (_@L1) , Some (_@L2) => L1 = L2
      | None        , None        => True
      | _           , _           => False
    end.

Definition equicompartmental (sst1 sst2 : sstate) : Prop :=
  forall p,
    match Sym.sget sst1 p , Sym.sget sst2 p with
      | Some (_@L1) , Some (_@L2) => Sym.stag_compartment L1 =
                                     Sym.stag_compartment L2
      | None        , None        => True
      | _           , _           => False
    end.

Definition tags_subsets (sst1 sst2 : sstate) : Prop :=
  forall p,
    match Sym.sget sst1 p , Sym.sget sst2 p with
      | Some _@(Sym.DATA c1 I1 W1) , Some _@(Sym.DATA c2 I2 W2) =>
        c1 = c2 /\
        (forall a, In a I1 -> In a I2) /\
        (forall a, In a W1 -> In a W2)
      | None , None =>
        True
      | _ , _ =>
        False
    end.

Lemma refined_compartment_preserved : forall sst sst' c,
  (forall p, Sym.good_memory_tag sst  p) ->
  (forall p, Sym.good_memory_tag sst' p) ->
  tags_subsets sst sst' ->
  refined_compartment c sst ->
  refined_compartment c sst'.
Proof.
  clear S I; intros sst sst' [A J S] GOOD GOOD' COMPAT.
  rewrite /tags_subsets in COMPAT.
  rewrite /refined_compartment /=.

  assert (INIT :
    (do! sxs <- map_options (Sym.sget sst) A;
     the =<< map_options (Sym.stag_compartment ∘ slabel) sxs)
    =
    (do! sxs' <- map_options (Sym.sget sst') A;
     the =<< map_options (Sym.stag_compartment ∘ slabel) sxs')).
  {
    rewrite (lock the) 2!bind_assoc -(lock the) 2!map_options_bind; f_equal.
    induction A as [|a A]; simpl in *; [reflexivity|].
    specialize COMPAT with a.
    destruct (Sym.sget sst  a) as [[x  [|c  I  W|]]|],
             (Sym.sget sst' a) as [[x' [|c' I' W'|]]|];
      try done; destruct COMPAT as [EQ _]; subst; simpl.
    rewrite IHA; reflexivity.
  }
  
  set MAP_J := map_options _ J; set MAP_J' := map_options _ J.
  assert (EQ_ALL_J : forall sc,
            (forallb (set_elem sc) <$> MAP_J)  ?= true ->
            (forallb (set_elem sc) <$> MAP_J') ?= true). {
    subst MAP_J MAP_J'; intros sc; simpl.
    induction J as [|a J]; [reflexivity|simpl].
    specialize COMPAT with a; specialize GOOD with a; specialize GOOD' with a.
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
        lapply IHJ; [inversion 1 | auto].
    - destruct (forallb _ ys).
      + lapply IHJ; [inversion 1 | auto].
      + rewrite Bool.andb_false_r; inversion 1.
  }
  
  set MAP_S := map_options _ S; set MAP_S' := map_options _ S.
  assert (EQ_ALL_S : forall sc,
            (forallb (set_elem sc) <$> MAP_S)  ?= true ->
            (forallb (set_elem sc) <$> MAP_S') ?= true). {
    subst MAP_S MAP_S'; intros sc; simpl.
    induction S as [|a S' IHS];
      [reflexivity | simpl; clear S; rename S' into S].
    specialize COMPAT with a; specialize GOOD with a; specialize GOOD' with a.
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
        lapply IHS; [inversion 1 | auto].
    - destruct (forallb _ ys).
      + lapply IHS; [inversion 1 | auto].
      + rewrite Bool.andb_false_r; inversion 1.
  }
  
  intros REFINED; rewrite bind_assoc in REFINED.
  match type of REFINED with
    | is_true (isSome (do! _ <- ?X; _)) =>
      destruct X as [sc|] eqn:def_sc; simpl in REFINED; [|done]
  end.
  rewrite bind_assoc -INIT def_sc; simpl.
  specialize EQ_ALL_J with sc; specialize EQ_ALL_S with sc.
  destruct (forallb _ <$> MAP_J) as [[]|] eqn:ALL_J; simpl in REFINED; try done.
  destruct (forallb _ <$> MAP_S) as [[]|] eqn:ALL_S; simpl in REFINED; try done.
  lapply EQ_ALL_J; [clear EQ_ALL_J; intro ALL_J' | done].
  lapply EQ_ALL_S; [clear EQ_ALL_S; intro ALL_S' | done].
  destruct (forallb _ <$> MAP_J') as [[]|]; try done.
  destruct (forallb _ <$> MAP_S') as [[]|]; done.
Qed.  

Lemma forallb_map_options_insert_unique : forall {A B} `{ord : Ordered A}
                                                 p (f : A -> option B) xs a,
  (p <$> f a) ?= true ->
  (forallb p <$> map_options f xs) =
  (forallb p <$> map_options f (insert_unique a xs)).
Proof.
  intros until 0; intros OK.
  destruct (forallb p <$> map_options f xs) as [[]|] eqn:ALL.
  - destruct (map_options f xs) as [ys|] eqn:MO; [move: ALL => [ALL] | done].
    destruct (map_options f (insert_unique a xs)) as [ys'|] eqn:MO'; simpl.
    + f_equal; symmetry; apply forallb_forall.
      intros y IN.
      move/map_options_in in MO'; apply MO' in IN.
      move: IN => [x [fx /insert_unique_spec [? | IN]]]; subst.
      * by rewrite fx in OK; move: OK => [OK].
      * move/map_options_in in MO.
        assert (EX : exists x, f x ?= y /\ In x xs) by by exists x.
        apply MO in EX.
        by move/forallb_forall in ALL; apply ALL in EX.
    + apply map_options_none in MO'.
      move: MO' => [x [/insert_unique_spec [? | IN] NONE]];
        [subst; rewrite NONE in OK; done|].
      assert (MO_SOME : is_some (map_options f xs)) by by rewrite MO.
      move/map_options_somes in MO_SOME; apply MO_SOME in IN.
      by rewrite NONE in IN.
  - destruct (map_options f xs) as [ys|] eqn:MO; [move: ALL => [ALL'] | done].
    destruct (map_options f (insert_unique a xs)) as [ys'|] eqn:MO'; simpl.
    + f_equal; symmetry.
      apply Bool.negb_true_iff; apply/negP.
      apply Bool.negb_true_iff in ALL'; move/negP in ALL'.
      move=> /forallb_forall ALL; apply ALL'; clear ALL'; apply/forallb_forall.
      intros y IN; apply ALL.
      move/map_options_in in MO; move/map_options_in in MO'.
      apply MO in IN; apply MO'.
      move: IN => [x [fx IN]]; exists x; split; auto.
    + apply map_options_none in MO'.
      move: MO' => [x [/insert_unique_spec [? | IN] NONE]];
        [subst; rewrite NONE in OK; done|].
      assert (MO_SOME : is_some (map_options f xs)) by by rewrite MO.
      move/map_options_somes in MO_SOME; apply MO_SOME in IN.
      by rewrite NONE in IN.
  - destruct (map_options f xs) as [ys|] eqn:MO; [done | clear ALL OK].
    destruct (map_options f (insert_unique a xs)) as [ys'|] eqn:MO'; simpl.
    + move/map_options_none in MO.
      move: MO => [x [IN fx]].
      assert (MO'_SOME : is_some (map_options f (insert_unique a xs))) by
        by rewrite MO'.
      assert (IN' : In x (insert_unique a xs)) by auto.
      move/map_options_somes in MO'_SOME; apply MO'_SOME in IN'.
      by rewrite fx in IN'.
    + reflexivity.
Qed.

Lemma refined_compartment_same : forall sst sst' c,
  equilabeled sst sst' ->
  refined_compartment c sst = refined_compartment c sst'.
Proof.
  clear S I; intros sst sst' [A J S] SAME.
  rewrite /equilabeled in SAME.
  rewrite /refined_compartment /=.
  assert (INIT :
    (do! sxs <- map_options (Sym.sget sst) A;
     the =<< map_options (Sym.stag_compartment ∘ slabel) sxs)
    =
    (do! sxs' <- map_options (Sym.sget sst') A;
     the =<< map_options (Sym.stag_compartment ∘ slabel) sxs')).
  {
    rewrite (lock the) 2!bind_assoc -(lock the) 2!map_options_bind; f_equal.
    induction A as [|a A]; simpl in *; [reflexivity|].
    specialize SAME with a.
    destruct (Sym.sget sst a) as [[x L]|], (Sym.sget sst' a) as [[x' L']|];
      try done; simpl in SAME; inversion SAME; subst L'; simpl.
    rewrite IHA; reflexivity.
  }
  set MAP_J := (map_options _ J); set MAP_J' := (map_options _ J).
  assert (EQ_MAP_J : MAP_J = MAP_J'). {
    subst MAP_J MAP_J'.
    induction J as [|a J]; [reflexivity|simpl].
    specialize SAME with a.
    destruct (Sym.sget sst a) as [[x L]|], (Sym.sget sst' a) as [[x' L']|];
      try done.
    simpl in SAME; inversion SAME; subst; simpl.
    by rewrite IHJ.
  }
  set MAP_S := (map_options _ S); set MAP_S' := (map_options _ S).
  assert (EQ_MAP_S : MAP_S = MAP_S'). {
    subst MAP_S MAP_S'.
    induction S as [|a S']; [reflexivity|simpl].
    specialize SAME with a.
    destruct (Sym.sget sst a) as [[x L]|], (Sym.sget sst' a) as [[x' L']|];
      try done.
    simpl in SAME; inversion SAME; subst; simpl.
    by rewrite IHS'.
  }
  rewrite bind_assoc INIT -bind_assoc EQ_MAP_J EQ_MAP_S; reflexivity.
Qed.


Lemma refined_compartment_irrelevancies : forall c SM SR SR' Spc Spc'
                                                 Snext Snext' SiT SaJT SaST,
  refined_compartment c (SState SM SR  Spc  (SInternal Snext  SiT SaJT SaST)) =
  refined_compartment c (SState SM SR' Spc' (SInternal Snext' SiT SaJT SaST)).
Proof. reflexivity. Qed.

Theorem isolate_create_set_refined : forall AM SM,
  refine_memory AM SM ->
  forall p, isolate_create_set id AM p = isolate_create_set svalue SM p.
Proof.
  move=> AM SM REFINE p;
    rewrite /refine_memory /refine_mem_loc_b /pointwise in REFINE.
  rewrite /isolate_create_set.

  erewrite refined_mem_value; [|eassumption].
  set G := get SM p; destruct G as [[wpairs ?]|]; subst; simpl; try done.

  remember (word_to_nat wpairs) as pairs; clear Heqpairs.
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
        eapply Sym.sget_supd_eq in def_sst'; [|eassumption].
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

Theorem isolate_refined : forall ast sst sst',
  Abs.good_state ast ->
  refine ast sst ->
  Sym.isolate sst ?= sst' ->
  exists ast',
    Abs.isolate_fn ast ?= ast' /\
    refine ast' sst'.
Proof.
  clear S I; move=> ast sst sst' AGOOD REFINE ISOLATE.
  assert (SGOOD : Sym.good_state sst) by (eapply refine_good; eassumption).
  destruct REFINE as [RPC RREGS RMEMS RCOMP RPREV     RSC RINT],
           ast    as [Apc AR    AM    AC    Ask Aprev],
           sst    as [SM SR Spc [Snext SiT SaJT SaST]].
  generalize SGOOD; move=> [[SGMEM [SGREG SGPC]] SGINT].
  generalize AGOOD =>
    /andP [/andP [/andP [AELEM AGOODCS] ASS] ASP];
    generalize AGOODCS => /andP [/andP [AGOODS ANOL] ACC];
    assert (AIN : In Aprev AC) by by simpl in *; destruct (elem Aprev AC).
  rewrite /Abs.semantics /Abs.isolate /Abs.isolate_fn
          (lock Abs.in_compartment_opt);
    simpl in *.
  
  rewrite /refine_pc_b in RPC.
  destruct Spc as [pc [F cid| |]]; try done; move/eqP in RPC; subst.
  
  move/id in ISOLATE;
    undo2 ISOLATE i LI;
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
  
  repeat (erewrite refined_reg_value; [|eassumption]).
  rewrite def_pA_LpA def_pJ_LpJ def_pS_LpS def_pc'_Lpc' /=.
  destruct Aprev as [Aprev Jprev Sprev].
  
  generalize RCOMP;
    rewrite /refine_compartments /refine_compartment_tag /= in RCOMP;
    move: RCOMP => [RCOMPS RCTAGS] RCOMP.
  move: (RCTAGS pc) => RCTAGS'; rewrite def_i_LI in RCTAGS';
    destruct RCTAGS' as [SET_I_sys [SET_W_sys [c_sys [IN_c_sys RTAG_sys]]]].
  
  assert (PNI : Abs.permitted_now_in AC Ask <<Aprev,Jprev,Sprev>> pc ?= c_sys) by
    (eapply prove_permitted_now_in; eassumption);
    rewrite PNI; simpl.
  assert (R_c_sys : refined_compartment
                      c_sys
                      (SState SM SR pc@(Sym.PC F cid)
                              (SInternal Snext SiT SaJT SaST))
                      ?= cid_sys)
    by eauto using prove_refined_compartment.

  repeat (erewrite isolate_create_set_refined; [|eassumption]).
  rewrite def_A' def_J' def_S' /= NE_A' /=.
  
  assert (SGINT' : Sym.good_internal (SState SM SR pc@(Sym.PC F cid) si')). {
    fold (Sym.fresh (SInternal Snext SiT SaJT SaST)) in def_c'_si'.
    eapply Sym.fresh_preserves_good in def_c'_si'; eassumption.
  }
  rewrite /Sym.good_pc_tag in SGPC; move: SGPC => [p [x [I [W def_cid]]]].
  destruct (Snext == max_word) eqn:SMALL_Snext; move/eqP in SMALL_Snext;
    inversion def_c'_si'; subst c' si'; clear def_c'_si'.
  
  assert (REFINED_cid : forall Snext,
                          refined_compartment
                            <<Aprev,Jprev,Sprev>>
                            (SState SM SR pc@(Sym.PC F cid)
                                    (SInternal Snext SiT SaJT SaST)) 
                            ?= cid). {
    intros Snext'.
    rewrite (@refined_compartment_irrelevancies
               _ _ _ SR _ pc@(Sym.PC F cid) _ Snext);
      clear Snext'.
    rewrite /refine_previous_b /= in RPREV;
      move: RPREV => /andP [_ /eqP?] //.
  }
  
  assert (SGOOD_sA : forall p, Sym.good_memory_tag sA p). {
    eapply Sym.retag_set_preserves_good_memory_tag; try eassumption.
    by move=> /= *; apply/andP.
  }
  
  assert (SGOOD_sJ : forall p, Sym.good_memory_tag sJ p). {
    eapply Sym.retag_set_preserves_good_memory_tag; try eassumption.
    move=> /= *; apply/andP; auto.
  }
  
  assert (SGOOD_sS : forall p, Sym.good_memory_tag (SState MS RS pcS siS) p). {
    eapply Sym.retag_set_preserves_good_memory_tag; try eassumption.
    move=> /= *; apply/andP; auto.
  }

  assert (SET_A'   : is_set A') by eauto 3.
  assert (SET_J'   : is_set J') by eauto 3.
  assert (SET_S'   : is_set S') by eauto 3.
  
  (* These will come in handy later *)
  assert (NODUP_A' : NoDup A') by eauto 2.
  assert (NODUP_J' : NoDup J') by eauto 2.
  assert (NODUP_S' : NoDup S') by eauto 2.

  assert (SUBSET_A' : subset A' Aprev). {
    apply/subset_spec; intros a IN.
    eapply Sym.retag_set_forall in IN; try eassumption.
    move: IN => /= [x' [c' [I' [W' [SGET /eqP OK]]]]]; subst c'.
    eapply refined_sget_in_compartment in SGET; eauto 1.
    apply Abs.in_compartment_spec in SGET; tauto.
  }
  rewrite SUBSET_A'.
  
  assert (IN_A' : forall a x' I' W',
                    Sym.sget sA a ?= x'@(Sym.DATA Snext I' W') ->
                    In a A'). {
    intros until 0; intros SGET.
    destruct (elem a A') as [IN | NIN]; auto.
    eapply Sym.retag_set_not_in in NIN; [|eassumption].
    rewrite SGET in NIN.
    eapply Sym.sget_lt_next in RINT; [simpl in RINT | eassumption].
    by apply lt_irrefl in RINT.
  }
  
  assert (SUBSET_J' : subset J' (set_union Aprev Jprev)). {
    apply/subset_spec; move=> a IN; apply/set_union_spec.
    generalize def_sA => def_sA';
      apply @Sym.retag_set_or with (p := a) in def_sA'; try assumption.
    generalize IN => IN'; eapply Sym.retag_set_forall in IN'; eauto 1.
    move: IN' =>
      /= [x' [c' [I' [W' [SGET /orP [/orP [/eqP? | /eqP?] | ELEM]]]]]];
      [subst c'; left | subst c'; left | right].
   - eapply Sym.retag_set_in in IN; try eassumption.
     rewrite SGET in IN.
     move: IN => [? [? [? [? [/esym EQ NOW]]]]]; move: EQ => [] *; subst.
     rewrite SGET in def_sA'; move: def_sA' => [OLD | NEW].
     + eapply refined_sget_in_compartment in OLD; eauto 1.
       apply Abs.in_compartment_spec in OLD; tauto.
     + move: NEW => [xnew [cnew [Inew [Wnew [NEW /esym[]]]]]] *; subst.
       move/id in SGET. apply IN_A' in SGET.
       move/subset_spec in SUBSET_A'; auto.
   - apply IN_A' in SGET.
     move/subset_spec in SUBSET_A'; auto.
   - move: (RCTAGS p) => RCTAGS'; rewrite def_cid in RCTAGS'.
     move: RCTAGS' => [_ [_ [c [IC' RTAG]]]]; specialize RTAG with a.
     replace c with <<Aprev,Jprev,Sprev>> in * by
       (eapply refined_sget_in_compartment in def_cid; try eassumption;
        eauto 3).
     specialize SGOOD_sA with a; rewrite /Sym.good_memory_tag SGET in SGOOD_sA;
       move: SGOOD_sA => /andP [SET_I' SET_W'].
     apply set_elem_true in ELEM; auto.
     rewrite SGET in def_sA'; move: def_sA' => [OLD | NEW].
     + rewrite /Sym.sget /= in OLD.
       rewrite /Sym.sget /= OLD in RTAG.
       repeat invh and; auto.
     + move: NEW => [xnew [cnew [Inew [Wnew [NEW /esym[]]]]]] *; subst.
       rewrite /Sym.sget /= in NEW.
       rewrite /Sym.sget /= NEW in RTAG.
       repeat invh and; auto.
  }
  rewrite SUBSET_J'.
  
  assert (IN_A'_sJ : forall a x' I' W',
                       Sym.sget sJ a ?= x'@(Sym.DATA Snext I' W') ->
                       In a A'). {
    intros until 0; intros SGET.
    apply @Sym.retag_set_or with (p := a) in def_sJ; try assumption.
    rewrite SGET in def_sJ.
    destruct def_sJ as [OLD | NEW].
    - by apply IN_A' in OLD.
    - move: NEW => [xnew [cnew [Inew [Wnew [SGET' /esym[]]]]]] *; subst.
      by apply IN_A' in SGET'.
  }
  
  assert (SUBSET_S' : subset S' (set_union Aprev Sprev)). {
    apply/subset_spec; move=> a IN; apply/set_union_spec.
    generalize def_sA => def_sA';
      apply @Sym.retag_set_or with (p := a) in def_sA'; try assumption.
    generalize def_sJ => def_sJ';
      apply @Sym.retag_set_or with (p := a) in def_sJ'; try assumption.
    set scompartment := fun sst =>
      do! _ @ DATA c _ _ <- Sym.sget sst a;
      Some c.
    assert (COMPARTMENT :
                 scompartment (SState SM SR pc@(Sym.PC F cid)
                                      (SInternal (Snext + 1)%w SiT SaJT SaST))
                   = scompartment sJ
              \/ In a A'). {
      subst scompartment; simpl.
      destruct def_sJ' as [OLD | NEW].
      - rewrite -OLD.
        destruct def_sA' as [OLD' | NEW'].
        + rewrite OLD'.
          by left.
        + move: NEW' => [? [? [? [? [_ NEW']]]]].
          rewrite NEW' /=.
          apply IN_A' in NEW'.
          by right.
      - destruct NEW as [? [? [? [? [SGET_sA SGET_sJ]]]]].
        rewrite SGET_sJ /=.
        destruct def_sA' as [OLD' | NEW'].
        + rewrite OLD' SGET_sA /=.
          by left.
        + move: NEW' => [? [? [? [? [_ NEW']]]]].
          rewrite NEW' in SGET_sA.
          inversion SGET_sA; subst.
          apply IN_A' in NEW'.
          by right.
    }
    move/subset_spec in SUBSET_A'.
    subst scompartment; simpl in *.
    generalize IN => IN'; eapply Sym.retag_set_forall in IN';
      try eassumption.
    move: IN' =>
      /= [x' [c' [I' [W' [SGET /orP [/orP [/eqP? | /eqP?] | ELEM]]]]]];
      [subst c'; left | subst c'; left | ].
   - rewrite SGET /= in COMPARTMENT.
     move: COMPARTMENT => [OLD | DONE]; auto.
     undoDATA OLD xold cold Iold Wold.
     move: OLD => [] /esym?; subst.
     eapply refined_sget_in_compartment in def_xcIW0; eauto 1.
     apply Abs.in_compartment_spec in def_xcIW0; tauto.
   - apply IN_A'_sJ in SGET; auto.
   - assert (SAME_W : forall x c I W x' c' I' W',
                        Sym.sget
                          (SState SM SR pc@(Sym.PC F cid)
                                  (SInternal (Snext + 1)%w SiT SaJT SaST))
                          a ?= x@(Sym.DATA c I W) ->
                        Sym.sget sJ a ?= x'@(Sym.DATA c' I' W') ->
                        W' = W). {
       intros; repeat invh or; repeat invh ex; repeat invh and; congruence.
     }
     move: (RCTAGS p) => RCTAGS'; rewrite def_cid in RCTAGS'.
     move: RCTAGS' => [_ [_ [c [IC' RTAG]]]]; specialize RTAG with a.
     replace c with <<Aprev,Jprev,Sprev>> in * by
       (eapply refined_sget_in_compartment in def_cid; try eassumption;
        eauto 3).
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
         + move: NEW' => [? [? [? [? [_ NEW']]]]].
           rewrite NEW' in SGET; move: SGET => [] *; subst.
           eapply SAME_W; eauto 1.
       - destruct NEW as [? [? [? [? [SGET_sA SGET_sJ]]]]].
         rewrite SGET_sJ /= in SGET.
         move: SGET => [] *; subst.
         destruct def_sA' as [OLD' | NEW'].
         + rewrite -OLD' in SGET_sA.
           by move: SGET_sA => [].
         + move: NEW' => [? [? [? [? [_ NEW']]]]].
           rewrite NEW' in SGET_sA; move: SGET_sA => [] *; subst.
           eapply SAME_W; eauto 1.
     }
     right.
     rewrite /Sym.sget /= in def_xcIW0.
     rewrite /Sym.sget /= def_xcIW0 in RTAG.
     specialize SGOOD_sJ with a; rewrite /Sym.good_memory_tag SGET in SGOOD_sJ;
       move: SGOOD_sJ => /andP [SET_I' SET_W'].
     apply set_elem_true in ELEM; auto.
     repeat invh and; auto.
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
                | Some x1@(Sym.DATA cid1 _ _) , Some x2@(Sym.DATA cid2 _ _) =>
                  x1 = x2 /\ (cid1 = cid2 \/ (cid1 = cid /\ cid2 = Snext))
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
    generalize def_sA => def_sA';
      apply @Sym.retag_set_or_ok with (p := a) in def_sA'; try assumption.
    generalize def_sJ => def_sJ';
      apply @Sym.retag_set_or with (p := a) in def_sJ'; try assumption.
    generalize def_sS => def_sS';
      apply @Sym.retag_set_or with (p := a) in def_sS'; try assumption.
    idtac;
      destruct def_sA' as [OLD_A | [xA [cA [IA [WA [THEN_A [OK_A NOW_A]]]]]]];
      destruct def_sJ' as [OLD_J | [xJ [cJ [IJ [WJ [THEN_J NOW_J]]]]]];
      destruct def_sS' as [OLD_S | [xS [cS [IS [WS [THEN_S NOW_S]]]]]];
      try move/eqP in OK_A; subst;
      first [move/id in OLD_A | move/id in THEN_A; move/id in NOW_A];
      first [move/id in OLD_J | move/id in THEN_J; move/id in NOW_J];
      first [move/id in OLD_S | move/id in THEN_S; move/id in NOW_S].
    - rewrite OLD_A OLD_J OLD_S.
      rewrite /Sym.good_memory_tag in SGOOD_sS.
      specialize SGOOD_sS with a.
      set G := Sym.sget _ a in SGOOD_sS *; destruct G as [[? []]|]; auto.
    - rewrite OLD_A OLD_J THEN_S NOW_S.
      by split; [|left].
    - rewrite OLD_A THEN_J -OLD_S NOW_J.
      by split; [|left].
    - rewrite OLD_A THEN_J NOW_S.
      rewrite THEN_S in NOW_J.
      by inversion NOW_J; subst; split; [|left].
    - rewrite THEN_A -OLD_S -OLD_J NOW_A.
      by split; [|right].
    - rewrite THEN_A NOW_S.
      rewrite NOW_A THEN_S in OLD_J.
      by inversion OLD_J; subst; split; [|right].
    - rewrite THEN_A -OLD_S NOW_J.
      rewrite NOW_A in THEN_J.
      by inversion THEN_J; subst; split; [|right].
    - rewrite THEN_A NOW_S.
      rewrite NOW_A in THEN_J.
      rewrite THEN_S in NOW_J.
      by inversion THEN_J; inversion NOW_J; subst; split; [|right].
  }
  
  assert (IC_pc' : AC ⊢ pc' ∈ <<Aprev, Jprev, Sprev>>). {
    specialize COMPARTMENTS with pc'.
    rewrite /Sym.sget /= in def_xcIW.
    rewrite {2 3}/Sym.sget /= def_xcIW in COMPARTMENTS.
    set G := Sym.sget _ pc' in COMPARTMENTS;
      destruct G as [[xpc' [|cpc' Ipc' Wpc'|]]|] eqn:SGET;
      subst G;
      try done.
    destruct COMPARTMENTS as [? COMPARTMENTS]; subst.
    replace cpc' with cid in * by (destruct COMPARTMENTS; symmetry; tauto).
    eapply refined_sget_in_compartment; eauto 1.
  }
  
  assert (DIFF : cid <> Snext). {
    intros ?; subst.
    eapply Sym.sget_lt_next in RINT; [simpl in RINT | eassumption].
    by apply lt_irrefl in RINT.
  }
  
  assert (DIFF_sys : cid_sys <> Snext). {
    intros ?; subst.
    eapply Sym.sget_lt_next in RINT; [simpl in RINT | eassumption].
    by apply lt_irrefl in RINT.
  }
  
  assert (NIN : ~ In pc' A'). {
    intros IN.
    eapply Sym.retag_set_in_ok in IN; try eassumption.
    simpl in IN.
    destruct IN as [xpc' [cpc' [Ipc' [Wpc' [THEN [OK NOW]]]]]].
    move/eqP in OK; subst cpc'.
    move/id in def_xcIW;
      apply @Sym.retag_set_or with (p := pc') in def_sJ; try assumption;
      apply @Sym.retag_set_or with (p := pc') in def_sS; try assumption;
      destruct def_sJ as [OLD_J | [xJ [cJ [IJ [WJ [THEN_J NOW_J]]]]]];
      destruct def_sS as [OLD_S | [xS [cS [IS [WS [THEN_S NOW_S]]]]]];
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
  
  generalize IC_pc' => /Abs.in_compartment_spec [IN_prev_AC IN_pc'_Aprev].
  
  assert (AGOODC_prev : Abs.good_compartment <<Aprev,Jprev,Sprev>>) by
    (move/forallb_forall in AGOODS; apply AGOODS; assumption).
  assert (SET_Aprev : is_set Aprev) by
    (eapply Abs.good_compartment_decomposed__is_set_address_space; eassumption).
  assert (SET_Jprev : is_set Jprev) by
    (eapply Abs.good_compartment_decomposed__is_set_jump_targets;  eassumption).
  assert (SET_Sprev : is_set Sprev) by
    (eapply Abs.good_compartment_decomposed__is_set_shared_memory; eassumption).
  
  assert (ELEM_pc' : set_elem pc' (set_difference Aprev A'))
    by (apply set_elem_true; auto; apply set_difference_spec; auto).
  rewrite -(lock Abs.in_compartment_opt) /= ELEM_pc' /= eq_refl.
  
  assert (IN_Jsys : In pc' (Abs.jump_targets c_sys)). {
    apply set_elem_true in NEXT.
    - move/id in RTAG_sys; specialize RTAG_sys with pc'.
      replace (Sym.sget _ pc')
         with (Sym.sget (SState SM SR pc@(Sym.PC F cid)
                                (SInternal (Snext+1)%w SiT SaJT SaST))
                        pc')
           in RTAG_sys
           by reflexivity.
      generalize def_sA => def_sA';
        apply @Sym.retag_set_or with (p := pc') in def_sA'; try assumption.
      generalize def_sJ => def_sJ';
        apply @Sym.retag_set_or with (p := pc') in def_sJ'; try assumption.
      generalize def_sS => def_sS';
        apply @Sym.retag_set_or with (p := pc') in def_sS'; try assumption.
      idtac;
        destruct def_sA' as [OLD_A | [xA [cA [IA [WA [THEN_A NOW_A]]]]]];
        destruct def_sJ' as [OLD_J | [xJ [cJ [IJ [WJ [THEN_J NOW_J]]]]]];
        destruct def_sS' as [OLD_S | [xS [cS [IS [WS [THEN_S NOW_S]]]]]];
        try move/eqP in OK_A; subst;
        first [move/id in OLD_A | move/id in THEN_A; move/id in NOW_A];
        first [move/id in OLD_J | move/id in THEN_J; move/id in NOW_J];
        first [move/id in OLD_S | move/id in THEN_S; move/id in NOW_S];
        move/id in def_xcIW;
        try abstract congruence.
      + rewrite OLD_A OLD_J OLD_S def_xcIW in RTAG_sys.
        repeat invh and; auto.
      + rewrite OLD_A OLD_J THEN_S in RTAG_sys.
        rewrite NOW_S in def_xcIW.
        inversion def_xcIW; subst.
        repeat invh and; auto.
      + rewrite OLD_A THEN_J in RTAG_sys.
        rewrite -OLD_S NOW_J in def_xcIW.
        inversion def_xcIW; subst; clear def_xcIW.
        apply insert_unique_spec in NEXT.
        destruct NEXT as [? | NEXT]; subst.
        * congruence. 
        * repeat invh and; auto.
      + rewrite OLD_A THEN_J in RTAG_sys.
        rewrite NOW_S in def_xcIW.
        inversion def_xcIW; subst; clear def_xcIW.
        rewrite NOW_J in THEN_S.
        inversion THEN_S; subst; clear THEN_S.
        apply insert_unique_spec in NEXT.
        destruct NEXT as [? | NEXT]; subst.
        * congruence.
        * repeat invh and; auto.
    - rewrite /Sym.good_memory_tag in SGOOD_sS; specialize SGOOD_sS with pc'.
      rewrite def_xcIW in SGOOD_sS.
      move: SGOOD_sS => /andP [] //.
  }
  
  assert (ELEM_Jsys : set_elem pc' (Abs.jump_targets c_sys)).
    (apply Abs.in_compartment_spec in IN_c_sys; destruct IN_c_sys;
     move/forallb_forall in AGOODS; apply set_elem_true; eauto 3).
  rewrite ELEM_Jsys.
  
  eexists; split; [reflexivity|].
  
  assert (RMEMS' : refine_memory AM MS). {
    move/id in def_sA; move/id in def_sJ; move/id in def_sS;
      eapply retag_set_preserves_memory_refinement in def_sA; [|eassumption];
      eapply retag_set_preserves_memory_refinement in def_sJ; [|eassumption];
      eapply retag_set_preserves_memory_refinement in def_sS; [|eassumption];
      simpl in *.
    assumption.
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
  - admit.
  - admit.
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
  - rewrite /refine_syscall_addrs_b /= in RSC *.
    move/id in RSC.
    move: RSC => /andP [/andP [/andP [/andP [/andP [/andP [/andP [/andP [
                 ANGET_i ANGET_aJ] ANGET_aS]
                 SNGET_i] SNGET_aJ] SNGET_aS]
                 /eqP NEQiaJ] /eqP NEQiaS] /eqP NEQaJaS].
    
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
                                          add_to_shared_memory_addr))
      by by apply/negP; intros H; apply GETS_sA in H; move/negP in SNGET_aS.

    assert (SNGET_sJ_i : ~~ is_some (get (Symbolic.mem sJ) isolate_addr))
      by by apply/negP; intros H; apply GETS_sJ in H; move/negP in SNGET_sA_i.
    assert (SNGET_sJ_aJ : ~~ is_some (get (Symbolic.mem sJ)
                                          add_to_jump_targets_addr))
      by by apply/negP; intros H; apply GETS_sJ in H; move/negP in SNGET_sA_aJ.
    assert (SNGET_sJ_aS : ~~ is_some (get (Symbolic.mem sJ)
                                          add_to_shared_memory_addr))
      by by apply/negP; intros H; apply GETS_sJ in H; move/negP in SNGET_sA_aS.

    assert (SNGET_sS_i : ~~ is_some (get MS isolate_addr))
      by by apply/negP; intros H; apply GETS_sS in H; move/negP in SNGET_sJ_i.
    assert (SNGET_sS_aJ : ~~ is_some (get MS add_to_jump_targets_addr))
      by by apply/negP; intros H; apply GETS_sS in H; move/negP in SNGET_sJ_aJ.
    assert (SNGET_sS_aS : ~~ is_some (get MS add_to_shared_memory_addr))
      by by apply/negP; intros H; apply GETS_sS in H; move/negP in SNGET_sJ_aS.
    
    assert (SGINT_sA : Sym.good_internal sA). {
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
      
      assert (NIN_aS : ~ In add_to_shared_memory_addr A'). {
        intros IN.
        rewrite /Abs.syscalls_separated in ASS; move/forallb_forall in ASS.
        specialize (ASS _ IN_prev_AC); move: ASS => /orP [UAS | SAS].
        - rewrite /Abs.user_address_space /= in UAS; move/forallb_forall in UAS.
          assert (IN' : In add_to_shared_memory_addr Aprev)
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
    apply SGINT_sS.
Qed.
    
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
  destruct REFINE as [RPC RREGS RMEMS RCOMP RPREV     RSC RINT],
           ast    as [Apc AR    AM    AC    Ask Aprev],
           sst    as [SM SR Spc [Snext SiT SaJT SaST]].
  generalize SGOOD; move=> [[SGMEM [SGREG SGPC]] SGINT].
  generalize AGOOD =>
    /andP [/andP [/andP [AELEM /andP [/andP [AGOODS ANOL] ACC]] ASS] ASP];
    assert (AIN : In Aprev AC) by by simpl in *; destruct (elem Aprev AC).
  rewrite /Abs.semantics /Abs.add_to_jump_targets
          /Abs.add_to_compartment_component
          (lock Abs.in_compartment_opt);
    simpl in *.
  
  rewrite /refine_pc_b in RPC.
  destruct Spc as [pc [F cid'| |]]; try done; move/eqP in RPC; subst.
  
  move/id in ADD;
    undo2 ADD i LI;
    undo1 ADD cid_sys;
    destruct LI as [|cid I W|]; try discriminate;
    undo1 ADD NEQ_cid_sys;
    undo2 ADD p Lp;
    undoDATA ADD x cid'' I'' W'';
    undo1 ADD OK;
    undo1 ADD s';
    undo2 ADD pc' Lpc';
    undoDATA ADD i' cid_next I_next W_next;
    undo1 ADD NEXT_EQ; move/eqP in NEXT_EQ; subst cid_next.
    undo1 ADD NEXT;
    destruct s' as [M_next R_next not_pc si_next];
    unoption.
  
  generalize RCOMP;
    rewrite /refine_compartments /refine_compartment_tag /= in RCOMP;
    move: RCOMP => [RCOMPS RCTAGS] RCOMP.
  move: (RCTAGS pc) => RCTAGS'; rewrite def_i_LI in RCTAGS';
    destruct RCTAGS' as [SET_I [SET_W [c_sys [IN_c RTAG]]]].
  
  assert (PNI : Abs.permitted_now_in AC Ask Aprev pc ?= c_sys) by
    (eapply prove_permitted_now_in; eassumption);
    rewrite PNI; simpl.
  assert (R_c_sys : refined_compartment
                      c_sys
                      (SState SM SR pc@(Sym.PC F cid')
                              (SInternal Snext SiT SaJT SaST))
                    == Some cid_sys)
    by (eapply prove_refined_compartment' with (pc := pc); try eassumption).
  
  rewrite /Sym.good_pc_tag in SGPC; move: SGPC => [p' [x' [I' [W' def_cid']]]].
  move: RPREV => /andP [/eqP? RPREV]; subst.
  assert (SYS_SEP : Aprev != c_sys). {
    apply/eqP; intro; subst.
    move/eqP in R_c_sys; move/eqP in RPREV;
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
  assert (IC_p' : AC ⊢ p' ∈ <<Aprev,Jprev,Sprev>>). {
    (* This lemma's proof cribbed from a lemma in `prove_permitted_now_in'. *)
    move/eqP in RPREV; explode_refined_compartment' RPREV.
    move/id in def_sxs; move/id in MAP_sxs;
      move/id in SAME_cid; move/id in NE_cids.
    destruct cids as [|temp_cid cids];
      [discriminate | clear NE_cids; simpl in *].
    move: (SAME_cid temp_cid (or_introl Logic.eq_refl)) => ?; subst.
    move: (MAP_sxs cid') => [MAP_sxs' _];
      specialize (MAP_sxs' (or_introl Logic.eq_refl)).
    move: MAP_sxs' => [[v Lv] [TAG IN_sxs]]; simpl in *.
    apply def_sxs in IN_sxs.
    destruct IN_sxs as [p'' [GET_p'' IN_p'']].
    move: (RCTAGS p'') => RTAG''; rewrite GET_p'' in RTAG''.
    destruct Lv as [|cid''' I''' W'''|]; try done.
    simpl in TAG; inversion TAG; subst.
    move: RTAG'' => [_ [_ [c''' [IC''' RTAG''']]]].
    specialize RTAG''' with p'; rewrite def_cid' in RTAG''';
      move: RTAG''' => [[SAME _] _].
    specialize (SAME Logic.eq_refl).
    assert (IC_p''_prev : AC ⊢ p'' ∈ <<Aprev,Jprev,Sprev>>) by
      by apply Abs.in_compartment_spec.
    replace c''' with <<Aprev,Jprev,Sprev>> in * by eauto 3.
    assumption.
  }
  assert (IN_p : In p Aprev \/ In p Jprev). {
    (* This lemma's proof cribbed from `prove_permitted_now_in'. *)
    move/eqP in RPREV; explode_refined_compartment' RPREV.
    move/id in def_xcIW; move/id in OK.
    move: (RCTAGS p) => RCTAGS'; rewrite def_xcIW /= in RCTAGS';
      move: RCTAGS' => [SET_I'' [SET_W'' [prev' [IC_p RTAG']]]].
    move: OK => /orP [/eqP? | IN_I'']; [subst; left | right].
    - move: NE_cids => /nonempty_iff_in [temp_cid IN_cid].
      specialize (SAME_cid temp_cid IN_cid); subst.
      apply MAP_sxs in IN_cid.
      move: IN_cid => [[v [F' cid''|cid''' I''' W'''|]] [EQ_cid''' IN_sxs]];
        simpl in *; try discriminate;
        inversion EQ_cid'''; subst; clear EQ_cid''';
        apply def_sxs in IN_sxs; destruct IN_sxs as [p'' [GET'' IN_p'']];
        specialize RTAG' with p''; rewrite GET'' in RTAG'; try done.
      destruct RTAG' as [[SAME _] _].
      assert (IC_p''_prev' : AC ⊢ p'' ∈ prev') by auto.
      assert (IC_p''_prev  : AC ⊢ p'' ∈ <<Aprev,Jprev,Sprev>>) by
        by apply Abs.in_compartment_spec.
      replace prev' with <<Aprev,Jprev,Sprev>> in * by eauto 3.
      apply Abs.in_compartment_spec in IC_p; tauto.
    - move: (RCTAGS p') => RCTAGS'; rewrite def_cid' in RCTAGS';
        move: RCTAGS' => [_ [_ [c''' [IC''' RTAG''']]]].
      specialize RTAG''' with p; rewrite def_xcIW in RTAG'''.
      move: RTAG''' => [_ [IN_I _]].
      apply set_elem_true, IN_I in IN_I''; auto.
      by replace c''' with <<Aprev,Jprev,Sprev>> in * by eauto 3.
  }
  assert (ELEM_p : set_elem p (set_union Aprev Jprev)). {
    assert (Abs.good_compartment <<Aprev,Jprev,Sprev>>) by eauto 2.
    apply set_elem_true;
      [apply set_union_preserves_set; eauto 2 | by apply set_union_spec].
  }
  rewrite ELEM_p; simpl.
  
  generalize RREGS => RREGS';
    rewrite /refine_registers /pointwise /refine_reg_b in RREGS';
    specialize (RREGS' ra); rewrite def_pc'_Lpc' in RREGS'.
  destruct (get AR ra) as [Apc'|]; destruct Lpc'; try done;
    move/eqP in RREGS'; subst; simpl.
  
  assert (EQUICOMPARTMENTAL :
            equicompartmental
              (SState SM SR pc@(Sym.PC F cid')
                      (SInternal Snext SiT SaJT SaST))
              (SState M_next R_next not_pc si_next)). {
    rewrite /equicompartmental; intros a.
    destruct (a == p) eqn:EQ; move/eqP in EQ; [subst p|].
    - eapply Sym.sget_supd_eq in def_s'; eauto.
      by rewrite def_s' def_xcIW.
    - eapply Sym.sget_supd_neq in def_s'; eauto.
      rewrite def_s'.
      match goal with |- context[Sym.sget ?sst' a] =>
        by destruct (Sym.sget sst' a) as [[]|]
      end.
  }
  assert (IC_pc' : AC ⊢ pc' ∈ <<Aprev,Jprev,Sprev>>). {
    specialize RCTAGS with p'; rewrite def_cid' in RCTAGS.
    move: RCTAGS => [_ [_ [c_temp [IC_temp RTAG']]]].
    replace c_temp with <<Aprev,Jprev,Sprev>> in * by eauto 3; simpl in *.
    specialize RTAG' with pc'.
    remember (Sym.sget _ pc') as v eqn:SGET in RTAG'; symmetry in SGET.
    move/id in SGET; move/id in def_xcIW0; rename def_xcIW0 into SGET'.
    rewrite /equicompartmental in EQUICOMPARTMENTAL;
      specialize EQUICOMPARTMENTAL with pc'.
    rewrite SGET SGET' in EQUICOMPARTMENTAL.
    destruct v as [[w Lw]|]; [|done].
    destruct Lw; try done;
      inversion EQUICOMPARTMENTAL; subst; clear EQUICOMPARTMENTAL.
    by destruct RTAG' as [SAME _]; apply SAME.
  }
  assert (IN_pc' : In pc' Aprev) by
    (apply Abs.in_compartment_spec in IC_pc'; tauto).
  assert (ELEM_pc' : set_elem pc' Aprev). by
    (move/forallb_forall in AGOODS; apply set_elem_true; eauto 3).
  rewrite -(lock Abs.in_compartment_opt) /= ELEM_pc' /= eq_refl.

  assert (IN_Jsys : In pc' (Abs.jump_targets c_sys)). {
    undo1 def_cid_sys COND; unoption.
    apply set_elem_true in NEXT.
    - destruct (pc' == p) eqn:EQ; move/eqP in EQ; [subst p|].
      + eapply Sym.sget_supd_eq in def_s'; eauto 1.
        specialize RTAG with pc'. move/id in RTAG.
        move/id in def_xcIW0.
        rewrite def_xcIW0 in def_s'; inversion def_s'; subst; clear def_s'.
        rewrite def_xcIW in RTAG.
        destruct RTAG as [_ [IN_I_next _]].
        move: NEXT => /insert_unique_spec [? | NEXT]; subst.
        * by move/eqP in NEQ_cid_sys.
        * by apply IN_I_next.
      + eapply Sym.sget_supd_neq in def_s'; eauto 1.
        specialize RTAG with pc'; rewrite -def_s' def_xcIW0 in RTAG.
        destruct RTAG as [_ [IN_I_next _]].
        by apply IN_I_next.
    - rewrite /Sym.good_memory_tag in SGMEM; specialize SGMEM with pc'.
      destruct (pc' == p) eqn:EQ; move/eqP in EQ; [subst p|].
      + eapply Sym.sget_supd_eq in def_s'; eauto 1.
        rewrite def_xcIW0 in def_s'; inversion def_s'; subst; clear def_s'.
        rewrite def_xcIW in SGMEM.
        move: SGMEM => /andP []; auto.
      + eapply Sym.sget_supd_neq in def_s'; eauto 1.
        rewrite -def_s' def_xcIW0 in SGMEM.
        move: SGMEM => /andP [] //.
  }
  assert (ELEM_Jsys : set_elem pc' (Abs.jump_targets c_sys)) by 
    (apply Abs.in_compartment_spec in IN_c; destruct IN_c;
     move/forallb_forall in AGOODS; apply set_elem_true; eauto 3).
  rewrite ELEM_Jsys.

  eexists; split; [reflexivity|].
  
  assert (sget_next_spec : forall a,
            Sym.sget (SState M_next R_next not_pc si_next) a =
            Sym.sget (SState SM SR pc@(Sym.PC F cid')
                             (SInternal Snext SiT SaJT SaST)) a
            
            \/
            (Sym.sget (SState M_next R_next not_pc si_next) a ?=
               x@(Sym.DATA cid'' (insert_unique cid' I'') W'') /\
             p = a))
    by abstract
         (intros a; destruct (a == p) eqn:EQ; move/eqP in EQ; subst;
          [ eapply Sym.sget_supd_eq in def_s'
          | eapply Sym.sget_supd_neq in def_s']; eauto).

  assert (M_next_spec : forall a,
            get M_next a = get SM a \/
            (get M_next a ?= x@(Sym.DATA cid'' (insert_unique cid' I'') W'')  /\
             p = a)).
  {
    intros a; destruct (a == p) eqn:EQ; move/eqP in EQ; subst.
    - rewrite /Sym.supd /upd in def_s'.
      set G := get SM p in def_s' *; destruct G eqn:GET; subst G.
      + inversion def_s'; subst; clear def_s'.
        by right; rewrite get_set_eq.
      + let finish := by inversion def_s'; subst; left
        in destruct (p == isolate_addr);              [finish|];
           destruct (p == add_to_jump_targets_addr);  [finish|];
           destruct (p == add_to_shared_memory_addr); [finish|];
           discriminate.
    - left; rewrite /Sym.supd in def_s'.
      set U := upd SM p _ in def_s'; destruct U eqn:UPD; subst U.
      + eapply get_upd_neq in UPD; eauto.
        by inversion def_s'; subst.
      + let finish := by inversion def_s'; subst
        in destruct (p == isolate_addr);              [finish|];
           destruct (p == add_to_jump_targets_addr);  [finish|];
           destruct (p == add_to_shared_memory_addr); [finish|];
           discriminate.
  }
  undo1 def_cid_sys COND; inversion def_cid_sys; subst cid; clear def_cid_sys.
  rewrite /Sym.supd /= in def_s'.
  destruct (upd SM p _) as [SM'|] eqn:UPD.
  - inversion def_s'; subst; clear def_s'.
    constructor; simpl; auto.
    + rewrite /refine_memory /pointwise /refine_mem_loc_b in RMEMS *;
        intros a; specialize RMEMS with a.
      destruct (a == p) eqn:EQ; move/eqP in EQ; subst.
      * generalize UPD => UPD'; apply get_upd_eq in UPD'; auto; rewrite UPD'.
        rewrite /upd in UPD.
        rewrite /Sym.sget in def_xcIW.
        set G := get SM p in def_xcIW UPD RMEMS; destruct G eqn:GET;
          [subst G | discriminate].
        by inversion def_xcIW; subst; clear def_xcIW.
      * apply get_upd_neq with (key' := a) in UPD; auto.
        by rewrite UPD.
    + rewrite /refine_compartments; split.
      * rewrite (lock refined_compartment); simpl.
        { apply/andP; split.
        - rewrite -(lock refined_compartment); move: RPREV => /eqP; simpl.
          set sst := SState SM R_next pc@(Sym.PC F cid')
                            (SInternal Snext SiT SaJT SaST).
          set sst' := SState M_next R_next pc'@(Sym.PC JUMPED cid_sys)
                             (SInternal Snext SiT SaJT SaST).
          assert (GOOD : forall p, Sym.good_memory_tag sst  p) by auto.
          assert (GOOD' : forall p, Sym.good_memory_tag sst' p).
          { move => p''.
            have [->|/eqP NEQ] := altP (p'' =P p).
            - rewrite /Sym.good_memory_tag /Sym.sget /sst'.
              generalize (PartMaps.get_upd_eq UPD) => EQ.
              rewrite EQ.
              move: GOOD => /(_ p) GOOD.
              rewrite /Sym.good_memory_tag /sst def_xcIW in GOOD.
              move/andP: GOOD => [GOOD1 GOOD2].
              apply/andP. split; last by [].
              by apply insert_unique_preserves_set_true.
            - rewrite /Sym.good_memory_tag /Sym.sget /sst'. 
              generalize (PartMaps.get_upd_neq NEQ UPD) => EQ.
              rewrite EQ.
              move: GOOD => /(_ p'') GOOD.
              rewrite /Sym.good_memory_tag /Sym.sget /sst in GOOD.
              exact: GOOD. }
          assert (COMPAT : tags_subsets sst sst').
          { move => p''.
            have [->|/eqP NEQ] := altP (p'' =P p).
            - rewrite def_xcIW. 
              generalize (PartMaps.get_upd_eq UPD) => EQ.
              rewrite /Sym.sget /sst' EQ. 
              split; first by [].
              split; last by [].
              move => a. apply insert_unique_preserves.
            - generalize (PartMaps.get_upd_neq NEQ UPD) => EQ.
              rewrite /Sym.sget /sst /sst' EQ.
              move: GOOD => /(_ p'') GOOD.
              rewrite /Sym.good_memory_tag /sst /Sym.sget in GOOD.
              case GET: (get SM p'') GOOD => [[v [? ?|c1 I1 W1|]]|] GOOD //.
              move: GOOD.
              case: (p'' == isolate_addr); first by case SiT.
              case: (p'' == add_to_jump_targets_addr); first by case SaJT.
              case: (p'' == add_to_shared_memory_addr); by [case SaST | ]. }
          rewrite /tags_subsets in COMPAT.
          rename Aprev into A; rename Jprev into J; rename Sprev into S.
          
          assert (INIT :
            (do! sxs <- map_options (Sym.sget sst) A;
             the =<< map_options (Sym.stag_compartment ∘ slabel) sxs)
            =
            (do! sxs' <- map_options (Sym.sget sst') A;
             the =<< map_options (Sym.stag_compartment ∘ slabel) sxs')).
          {
            clear AELEM AIN AGOOD SYS_SEP IC_p' IN_p PNI ELEM_p IC_pc' IN_pc'
                  ELEM_pc'.
            rewrite (lock the) 2!bind_assoc -(lock the) 2!map_options_bind;
              f_equal.
            induction A as [|a A]; simpl in *; [reflexivity|].
            specialize COMPAT with a.
            destruct (Sym.sget sst  a) as [[z  [|cz  Iz  Wz|]]|],
                     (Sym.sget sst' a) as [[z' [|cz' Iz' Wz'|]]|];
              try done; destruct COMPAT as [EQ _]; subst; simpl.
            rewrite IHA; try done.
          }
         
          intros REFINED; rewrite bind_assoc in REFINED.
          undo1 REFINED sc.
          rewrite bind_assoc -INIT def_sc; simpl.
          rewrite -forallb_map_options_insert_unique.
          move: REFINED.
          
          set MAP_J := map_options _ J; set MAP_J' := map_options _ J.
          assert (EQ_ALL_J :
                    (forallb (set_elem sc) <$> MAP_J)  ?= true ->
                    (forallb (set_elem sc) <$> MAP_J') ?= true). {
            clear AELEM AIN AGOOD SYS_SEP IC_p' IN_p PNI ELEM_p IC_pc' IC_pc'
                  IN_p.
            subst MAP_J MAP_J'; simpl.
            induction J as [|a J]; [reflexivity|simpl].
            specialize COMPAT with a;
              specialize GOOD with a; specialize GOOD' with a.
            rewrite /Sym.good_memory_tag in GOOD GOOD'.
            destruct (Sym.sget sst  a) as [[z  [|cz  Iz  Wz|]]|],
                     (Sym.sget sst' a) as [[z' [|cz' Iz' Wz'|]]|];
              try done; simpl.
            move: GOOD GOOD' => /andP [SET_Iz SET_Wz] /andP [SET_Iz' SET_Wz'].
            destruct COMPAT as [EQ [SUB_Iz SUB_Wz]]; subst.
            let unMO ys MO := match goal with
                                |- context[map_options ?f J] =>
                                destruct (map_options f J) as [ys|] eqn:MO
                              end
            in unMO ys MO; unMO ys' MO'; try done; simpl in *.
            - specialize SUB_Iz with sc.
              move=> [/andP [ELEM ALL]]; f_equal; apply/andP; split; auto.
              + apply/set_elem_true; [|apply set_elem_true in ELEM]; auto.
              + destruct (forallb _ ys); try done.
                destruct (forallb _ ys'); try done.
                lapply IHJ; [inversion 1 | auto].
            - destruct (forallb _ ys).
              + lapply IHJ; [inversion 1 | auto].
              + rewrite Bool.andb_false_r; inversion 1.
          }
          
          set MAP_S := map_options _ S; set MAP_S' := map_options _ S.
          assert (EQ_ALL_S :
                    (forallb (set_elem sc) <$> MAP_S)  ?= true ->
                    (forallb (set_elem sc) <$> MAP_S') ?= true). {
            clear AELEM AIN AGOOD PNI SYS_SEP IC_p' IC_pc'.
            subst MAP_S MAP_S'; simpl.
            induction S as [|a S' IHS];
              [reflexivity | simpl; clear S; rename S' into S].
            specialize COMPAT with a;
              specialize GOOD with a; specialize GOOD' with a.
            rewrite /Sym.good_memory_tag in GOOD GOOD'.
            destruct (Sym.sget sst  a) as [[z  [|cz  Iz  Wz|]]|],
                     (Sym.sget sst' a) as [[z' [|cz' Iz' Wz'|]]|];
              try done; simpl.
            move: GOOD GOOD' => /andP [SET_Iz SET_Wz] /andP [SET_Iz' SET_Wz'].
            destruct COMPAT as [EQ [SUB_Iz SUB_Wz]]; subst.
            let unMO ys MO := match goal with
                                |- context[map_options ?f S] =>
                                destruct (map_options f S) as [ys|] eqn:MO
                              end
            in unMO ys MO; unMO ys' MO'; try done; simpl in *.
            - specialize SUB_Wz with sc.
              move=> [/andP [ELEM ALL]]; f_equal; apply/andP; split; auto.
              + apply/set_elem_true; [|apply set_elem_true in ELEM]; auto.
              + destruct (forallb _ ys); try done.
                destruct (forallb _ ys'); try done.
                lapply IHS; [inversion 1 | auto].
            - destruct (forallb _ ys).
              + lapply IHS; [inversion 1 | auto].
              + rewrite Bool.andb_false_r; inversion 1.
          }
         
          intros REFINED.
          destruct (forallb _ <$> MAP_J) as [[]|] eqn:ALL_J; simpl in REFINED;
            try done.
          destruct (forallb _ <$> MAP_S) as [[]|] eqn:ALL_S; simpl in REFINED;
            try done.
          lapply EQ_ALL_J; [clear EQ_ALL_J; intro ALL_J' | done].
          lapply EQ_ALL_S; [clear EQ_ALL_S; intro ALL_S' | done].
          destruct (forallb _ <$> MAP_J') as [[]|]; try done.
          destruct (forallb _ <$> MAP_S') as [[]|]; done.

          specialize COMPAT with p;
            specialize GOOD with p; specialize GOOD' with p.
          rewrite /Sym.good_memory_tag in GOOD GOOD'.
          rewrite def_xcIW in COMPAT.
          destruct (Sym.sget sst' p) as [[z [|cz Iz Wz|]]|];
            try done; simpl.
          rewrite def_xcIW in GOOD.
          move: GOOD GOOD' => /andP [SET_I'' SET_W''] /andP [SET_Iz SET_Wz].
          destruct COMPAT as [EQ [SUB_I'' SUB_W'']]; subst cz.
          f_equal; apply set_elem_true; auto.
          have -> : sc = cid'.
          { undo1 REFINED X1.
            undo1 REFINED X2. by unoption. }
          move/orP: OK => [/eqP EQ' | IN''].
          + admit.
          + apply SUB_I''.
            by apply/(set_elem_true _ _ SET_I'').
        - rewrite -(lock refined_compartment); apply delete_preserves_forallb.
          eapply forallb_impl; [|apply RCOMPS].
          simpl; intros d RCSOME.
          eapply refined_compartment_preserved in RCSOME; try apply RCSOME;
            eauto 3.
          + intros a; specialize SGMEM with a;
              rewrite /Sym.good_memory_tag in SGMEM *.
            move: (sget_next_spec a) => [OLD | [NEW ?]]; subst.
            * rewrite {1}/Sym.sget /= in OLD.
              rewrite /Sym.sget OLD.
              assumption.
            * rewrite {1}/Sym.sget /= in NEW.
              rewrite /Sym.sget NEW.
              rewrite def_xcIW in SGMEM.
              move: SGMEM => /andP [] *; apply /andP; auto.
          + rewrite /tags_subsets /=; intros a. 
            move: (sget_next_spec a) => [OLD | [NEW ?]]; subst.
            * specialize SGMEM with a; rewrite /Sym.good_memory_tag in SGMEM.
              rewrite -OLD; rewrite -OLD in SGMEM.
              replace (Sym.sget (SState M_next R_next pc@(Sym.PC F cid')
                                        (SInternal Snext SiT SaJT SaST))
                                a)
                 with (Sym.sget (SState M_next R_next pc@(Sym.PC JUMPED cid_sys)
                                        (SInternal Snext SiT SaJT SaST))
                                a)
                   by trivial.
              clear OLD; destruct (Sym.sget _ a) as [[? []]|]; done.
            * rewrite {1}/Sym.sget /= in NEW.
              rewrite def_xcIW /Sym.sget NEW.
              repeat split; auto. }
      * intros a. rewrite /refine_compartment_tag /=.
        { move: (sget_next_spec a) => [OLD | [NEW ?]]; subst.
          - rewrite {1}/Sym.sget /= in OLD.
            rewrite {1}/Sym.sget /= OLD.
            move: (RCTAGS a) => RCTAGS'.
            set G := (Sym.sget _ a) in RCTAGS' *.
            destruct G as [[w [|cw Iw Ww|]]|] eqn:SGET; subst; try done.
            move: RCTAGS' => [SET_Iw [SET_Ww [c [IC RTAG']]]].
            do 2 (split; auto).
            destruct (<<Aprev,Jprev,Sprev>> == c) eqn:EQ; move/eqP in EQ; subst.
            + exists <<Aprev,insert_unique p Jprev,Sprev>>; split.
              * apply/Abs.in_compartment_spec;
                  move: IC => /Abs.in_compartment_spec [IN_c_AC IN_a_c];
                  split; auto.
              * intros a'.
                { move: (sget_next_spec a') => [OLD' | [NEW' ?]]; subst.
                  - rewrite {1}/Sym.sget /= in OLD'.
                    rewrite {1}/Sym.sget /= OLD'.
                    move/id in RTAG'; specialize RTAG' with a'.
                    set G := (Sym.sget _ a') in RTAG' *.
                    destruct G as [[w' [|cw' Iw' Ww'|]]|] eqn:SGET'; subst;
                      try done.
                    simpl in *.
                    destruct RTAG' as [SAME [IN_Iw' IN_Ww']].
                    split; [|split; auto].
                    rewrite SAME 2!Abs.in_compartment_spec /= delete_in_iff.
                    tauto.
                  - rewrite {1}/Sym.sget /= in NEW'.
                    rewrite {1}/Sym.sget /= NEW'.
                    move/id in RTAG'; specialize RTAG' with a'.
                    rewrite def_xcIW /= in RTAG'.
                    destruct RTAG' as [SAME [IN_I'' IN_W'']].
                    split; [|split; auto].
                    rewrite SAME 2!Abs.in_compartment_spec /= delete_in_iff.
                    tauto. }
            + exists c; split.
              * apply/Abs.in_compartment_spec; simpl.
                move: IC => /Abs.in_compartment_spec [IN_c_AC IN_a_c].
                rewrite delete_in_iff; auto.
              * intros a'.
                { move: (sget_next_spec a') => [OLD' | [NEW' ?]]; subst.
                  - rewrite {1}/Sym.sget /= in OLD'.
                    rewrite {1}/Sym.sget /= OLD'.
                    move/id in RTAG'; specialize RTAG' with a'.
                    set G := (Sym.sget _ a') in RTAG' *.
                    destruct G as [[w' [|cw' Iw' Ww'|]]|] eqn:SGET'; subst;
                      try done.
                    simpl in *.
                    destruct RTAG' as [SAME [IN_Iw' IN_Ww']].
                    split; [|split; auto].
                    move/Abs.in_compartment_spec in IC.
                    rewrite SAME 2!Abs.in_compartment_spec /= delete_in_iff.
                    abstract intuition.
                  - rewrite {1}/Sym.sget /= in NEW'.
                    rewrite {1}/Sym.sget /= NEW'.
                    move/id in RTAG'; specialize RTAG' with a'.
                    rewrite def_xcIW /= in RTAG'.
                    destruct RTAG' as [SAME [IN_I'' IN_W'']].
                    split; [|split; auto].
                    + move/Abs.in_compartment_spec in IC.
                      rewrite SAME 2!Abs.in_compartment_spec /= delete_in_iff.
                      abstract intuition.
                    + rewrite insert_unique_spec.
                      intros [? | ?]; subst; auto.
                      assert (AC ⊢ a ∈ <<Aprev,Jprev,Sprev>>) by
                        (move/eqP in RPREV; eapply refined_sget_in_compartment;
                         eauto 3).
                      replace c with <<Aprev,Jprev,Sprev>> in * by eauto 3.
                      congruence.
                }
          - rewrite /Sym.sget.  
            rewrite /Sym.sget in NEW.
            rewrite NEW. 
            move: (RCTAGS a) => RCTAGSa.
            rewrite def_xcIW in RCTAGSa.
            move: RCTAGSa => [SET_I'' [SET_W'' [c [Hc1 Hc2]]]].
            split3.
            + by apply insert_unique_preserves_set_true.
            + by [].
            + exists c.
              have INCOMP : <<Aprev,insert_unique a Jprev,Sprev>> :: delete <<Aprev,Jprev,Sprev>> AC ⊢ a ∈ c
                by admit. (* Should be possible to show by reasoning over Hc1 and delete *)
              split; first by [].
              move => p''.
              move: Hc2 RTAG => /(_ p'') Hc2 /(_ p'') RTAG.
              rewrite /Sym.sget in Hc2 RTAG.
              have [EQap''|/eqP NEQap''] := altP (p'' =P a).
              * subst p''.
                generalize (PartMaps.get_upd_eq UPD) => EQ.
                rewrite EQ.
                split; first by eauto.
                admit.
              * generalize (PartMaps.get_upd_neq NEQap'' UPD) => EQ.
                rewrite EQ.
                admit.
        }
    + rewrite /refine_previous_b /=.
      (*eapply prove_refined_compartment; eauto 3.*)
      admit.
    + admit.
    + admit.
  - destruct (p == isolate_addr);
      [|destruct (p == add_to_jump_targets_addr);
         [|destruct (p == add_to_shared_memory_addr);
           [|discriminate]]];
      inversion def_s'; subst; clear def_s'; simpl in *.
    + constructor; simpl; auto.
      * admit.
      * rewrite /refine_previous_b /=.
        admit. 
        (*rewrite /Sym.good_internal /= in RINT *.
        destruct SiT; try done.
        destruct SaJT; try done.
        destruct SaST; try done.
        destruct RINT as [? [? [? RINT]]].
        
        do 3 (split; auto).*)
      * admit.
    + admit.
    + admit.
Qed.

Theorem add_to_shared_memory_refined : forall ast sst sst',
  Abs.good_state ast ->
  refine ast sst ->
  Sym.add_to_shared_memory sst ?= sst' ->
  exists ast',
    Abs.semantics (Abs.add_to_shared_memory (t:=t)) ast ?= ast' /\
    refine ast' sst'.
Proof. Admitted.

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
  destruct REFINE as [RPC RREGS RMEMS RCOMP RPREV     RSC RINT],
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
      unfold Sym.can_execute,Sym.sfi_rvec in *; unoption; simpl in *.
    destruct tpc as [F cid'| |]; try discriminate;
      destruct ti as [|cid'' I W|]; try discriminate.
    move/eqP in RPC; subst Apc.
    generalize RCOMP;
      rewrite /refine_compartments /refine_compartment_tag /= in RCOMP;
      move: RCOMP => [RCOMPS RCTAGS] RCOMP.
    move: (RCTAGS pc) => RCTAGS'; rewrite /Sym.sget PC in RCTAGS';
      destruct RCTAGS' as [SET_I [SET_W [c [IN_c RTAG]]]].
    exists (AState (pc+1)%w AR AM AC INTERNAL c); split.
    + eapply Abs.step_nop; try reflexivity.
      * unfold Abs.decode.
        unfold refine_memory,pointwise,refine_mem_loc_b in RMEMS;
          specialize RMEMS with pc; rewrite PC in RMEMS;
          destruct (get AM pc); [simpl|contradiction].
        move/eqP in RMEMS; subst; assumption.
      * solve_permitted_now_in.
    + constructor; simpl;
        try solve [done | eapply prove_refined_compartment';
                          solve [ eassumption
                                | rewrite /Sym.sget /= PC; reflexivity ]].
  - (* Const *)
    undo1 NEXT rvec;
      destruct told as [| |]; try discriminate;
      undo1 def_rvec cid;
      undo1 NEXT regs';
      unfold Sym.can_execute,Sym.sfi_rvec in *; unoption; simpl in *.
    destruct tpc as [F cid'| |]; try discriminate;
      destruct ti as [|cid'' I W|]; try discriminate.
    move/eqP in RPC; subst Apc.
    generalize RCOMP;
      rewrite /refine_compartments /refine_compartment_tag /= in RCOMP;
      move: RCOMP => [RCOMPS RCTAGS] RCOMP.
    move: (RCTAGS pc) => RCTAGS'; rewrite /Sym.sget PC in RCTAGS';
      destruct RCTAGS' as [SET_I [SET_W [c [IN_c RTAG]]]].
    evar (AR' : registers t);
      exists (AState (pc+1)%w AR' AM AC INTERNAL c); split;
      subst AR'.
    + eapply Abs.step_const; try reflexivity.
      * unfold Abs.decode.
        unfold refine_memory,pointwise,refine_mem_loc_b in RMEMS;
          specialize RMEMS with pc; rewrite PC in RMEMS;
          destruct (get AM pc); [simpl|contradiction].
        move/eqP in RMEMS; subst; eassumption.
      * solve_permitted_now_in.
      * unfold upd; rewrite /refine_registers /pointwise in RREGS;
          specialize RREGS with r.
        destruct (get AR r) eqn:GET;
          [reflexivity | rewrite OLD in RREGS; done].
    + constructor; simpl;
        try solve [done | eapply prove_refined_compartment';
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
      unfold Sym.can_execute,Sym.sfi_rvec in *; unoption; simpl in *.
    destruct tpc as [F cid'| |]; try discriminate;
      destruct ti as [|cid'' I W|]; try discriminate.
    move/eqP in RPC; subst Apc.
    generalize RCOMP;
      rewrite /refine_compartments /refine_compartment_tag /= in RCOMP;
      move: RCOMP => [RCOMPS RCTAGS] RCOMP.
    move: (RCTAGS pc) => RCTAGS'; rewrite /Sym.sget PC in RCTAGS';
      destruct RCTAGS' as [SET_I [SET_W [c [IN_c RTAG]]]].
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
      * solve_permitted_now_in.
      * eassumption.
      * unfold upd; rewrite GET2; reflexivity.
    + constructor; simpl;
        try solve [done | eapply prove_refined_compartment';
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
      unfold Sym.can_execute,Sym.sfi_rvec in *; unoption; simpl in *.
    destruct tpc as [F cid'| |]; try discriminate;
      destruct ti as [|cid'' I W|]; try discriminate.
    move/eqP in RPC; subst Apc.
    generalize RCOMP;
      rewrite /refine_compartments /refine_compartment_tag /= in RCOMP;
      move: RCOMP => [RCOMPS RCTAGS] RCOMP.
    move: (RCTAGS pc) => RCTAGS'; rewrite /Sym.sget PC in RCTAGS';
      destruct RCTAGS' as [SET_I [SET_W [c [IN_c RTAG]]]].
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
      * solve_permitted_now_in.
      * eassumption.
      * eassumption.
      * unfold upd; rewrite GET3; reflexivity.
    + constructor; simpl;
        try solve [done | eapply prove_refined_compartment';
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
      unfold Sym.can_execute,Sym.sfi_rvec in *; unoption; simpl in *.
    destruct tpc as [F cid'| |]; try discriminate;
      destruct ti as [|cid'' I'' W''|]; try discriminate.
    move/eqP in RPC; subst Apc.
    generalize RCOMP;
      rewrite /refine_compartments /refine_compartment_tag /= in RCOMP;
      move: RCOMP => [RCOMPS RCTAGS] RCOMP.
    move: (RCTAGS pc) => RCTAGS'; rewrite /Sym.sget PC in RCTAGS';
      destruct RCTAGS' as [SET_I [SET_W [ac [IN_ac RTAG]]]].
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
      * solve_permitted_now_in.
      * eassumption.
      * eassumption.
      * unfold upd; rewrite GET2; reflexivity.
    + constructor; simpl;
        try solve [done | eapply prove_refined_compartment';
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
      unfold Sym.can_execute,Sym.sfi_rvec in *; unoption; simpl in *.
    destruct tpc as [F cid'| |]; try discriminate;
      destruct ti as [|cid'' I'' W''|]; try discriminate.
    move/eqP in RPC; subst Apc.
    generalize RCOMP;
      rewrite /refine_compartments /refine_compartment_tag /= in RCOMP;
      move: RCOMP => [RCOMPS RCTAGS] RCOMP.
    move: (RCTAGS pc) => RCTAGS'; rewrite /Sym.sget PC in RCTAGS';
      destruct RCTAGS' as [SET_I'' [SET_W'' [ac [IN_ac RTAG]]]].
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
      * solve_permitted_now_in.
      * eassumption.
      * eassumption.
      * { undo1 def_cid COND; unoption.
          specialize RTAG with w1; rewrite OLD in RTAG.
          move: RTAG => [[SAME _] [_ IN_W]].
          apply in_app_iff; move: WRITE_OK => /orP [/eqP? | ELEM];
            subst; [left | right].
        - specialize (SAME Logic.eq_refl);
           apply Abs.in_compartment_spec in SAME;
           tauto.
        - apply set_elem_true in ELEM; auto.
          move: SGOOD => [[SMEM _] _].
          specialize SMEM with w1;
            rewrite /Sym.good_memory_tag /Sym.sget OLD in SMEM;
          by move: SMEM => /andP []. }
      * unfold upd; rewrite GETM1; reflexivity.
    + assert (SAME :
                equilabeled
                  (SState mem  reg pc@(Sym.PC F cid')             int)
                  (SState mem' reg (pc+1)%w@(Sym.PC INTERNAL cid) int)). {
        rewrite /equilabeled; intros p.
        destruct (p == w1) eqn:EQ_w1; move/eqP in EQ_w1; [subst p|].
        - apply get_upd_eq in def_mem'; auto.
          by rewrite /Sym.sget OLD def_mem'.
        - apply get_upd_neq with (key' := p) in def_mem'; auto.
          rewrite /Sym.sget def_mem'; destruct (get mem p) as [[x L]|] eqn:GET;
            rewrite GET; try done.
          destruct (if      p == isolate_addr              then _
                    else if p == add_to_jump_targets_addr  then _
                    else if p == add_to_shared_memory_addr then _
                    else None)
            as [[z []]|]; auto.
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
      * { unfold refine_compartments; simpl; split.
        - apply forallb_forall; intros ac' IN.
          erewrite <-refined_compartment_same; [|eassumption].
          move/forallb_forall in RCOMPS; auto.
        - intros p; unfold refine_compartment_tag.
          generalize def_mem' => def_mem''.
          destruct (p == w1) eqn:EQ_w1; move/eqP in EQ_w1; [subst p|].
          + apply get_upd_eq in def_mem'; auto.
            specialize RCTAGS with w1; rewrite /Sym.sget OLD in RCTAGS.
            move: RCTAGS => [SET_I [SET_W [ac' [IC' RTAG']]]].
            rewrite /Sym.sget def_mem'; repeat split; auto.
            exists ac'; split; auto.
            intros p'; specialize RTAG' with p'.
            destruct (p' == w1) eqn:EQ_w1'; move/eqP in EQ_w1'; [subst p'|].
            * rewrite OLD in RTAG'; rewrite def_mem'; assumption.
            * apply get_upd_neq with (key' := p') in def_mem''; auto.
              rewrite def_mem''; assumption.
          + apply get_upd_neq with (key' := p) in def_mem'; auto.
            specialize RCTAGS with p; rewrite /Sym.sget def_mem'.
            rewrite /Sym.sget in RCTAGS.
            destruct (get mem p) as [[? []]|] eqn:GET;
              rewrite GET in RCTAGS; auto.
            * move: RCTAGS => [SET_I [SET_W [ac' [IC' RTAG']]]].
              repeat split; auto.
              exists ac'; split; auto.
              intros p'; specialize RTAG' with p'.
              { destruct (p' == w1) eqn:EQ_w1'; move/eqP in EQ_w1'; [subst p'|].
              - apply get_upd_eq in def_mem''; auto.
                rewrite OLD in RTAG'; rewrite def_mem''; assumption.
              - apply get_upd_neq with (key' := p') in def_mem''; auto.
                rewrite def_mem''; assumption. }
            * destruct (if      p == isolate_addr              then _
                        else if p == add_to_jump_targets_addr  then _
                        else if p == add_to_shared_memory_addr then _
                        else None)
                as [[z []]|]; auto.
              move: RCTAGS => [SET_I' [SET_W' [c' [IC' RTAG']]]].
              repeat split; auto.
              exists c'; split; auto.
              intros p'.
              rewrite /equilabeled /Sym.sget in SAME;
                specialize RTAG' with p'; specialize SAME with p'.
              by set G  := get mem  p' in RTAG' SAME;
                 set G' := get mem' p' in SAME *;
                 destruct G as [[x Lx]|] , G' as [[x' Lx']|];
                 simpl in *; subst; try done;
                 destruct (if      p' == isolate_addr              then _
                           else if p' == add_to_jump_targets_addr  then _
                           else if p' == add_to_shared_memory_addr then _
                           else None)
                   as [[z' []]|]; subst. }
      * rewrite /refine_previous_b; simpl.
        erewrite <-refined_compartment_same; [|eassumption].
        (* eassumption picked the wrong thing first *)
        eapply prove_refined_compartment'; try apply def_cid; try eassumption;
          rewrite /Sym.sget /= PC; reflexivity.
      * rewrite /refine_syscall_addrs_b /= in RSC *.
        repeat move: RSC => /andP [RSC ?].
        destruct (w1 == isolate_addr) eqn:EQ_i; move/eqP in EQ_i;
          [subst; rewrite ->GETM1 in *; done|].
        destruct (w1 == add_to_jump_targets_addr) eqn:EQ_aJ; move/eqP in EQ_aJ;
          [subst; rewrite ->GETM1 in *; done|].
        destruct (w1 == add_to_shared_memory_addr) eqn:EQ_aS; move/eqP in EQ_aS;
          [subst; rewrite ->GETM1 in *; done|].
        repeat rewrite get_set_neq; auto.
        do 3 (erewrite (get_upd_neq (key := w1) (m' := mem')); eauto 2).
        andb_true_split; auto.
      * rewrite /Sym.good_internal /= in RINT *.
        destruct int as [next iT aJT aST].
        destruct iT,aJT,aST; auto.
        destruct RINT as [? [? [? [? [? [? RINT]]]]]].
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
      unfold Sym.can_execute,Sym.sfi_rvec in *; unoption; simpl in *.
    destruct tpc as [F cid'| |]; try discriminate;
      destruct ti as [|cid'' I W|]; try discriminate.
    move/eqP in RPC; subst Apc.
    generalize RCOMP;
      rewrite /refine_compartments /refine_compartment_tag /= in RCOMP;
      move: RCOMP => [RCOMPS RCTAGS] RCOMP.
    move: (RCTAGS pc) => RCTAGS'; rewrite /Sym.sget PC in RCTAGS';
      destruct RCTAGS' as [SET_I [SET_W [c [IN_c RTAG]]]].
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
      * solve_permitted_now_in.
      * assumption.
    + constructor; simpl;
        try solve [done | eapply prove_refined_compartment';
                          solve [ eassumption
                                | rewrite /Sym.sget /= PC; reflexivity ]].
  - (* Bnz *)
    undo1 NEXT rvec;
      destruct t1; try discriminate;
      undo1 def_rvec cid;
      unfold Sym.can_execute,Sym.sfi_rvec in *; unoption; simpl in *.
    destruct tpc as [F cid'| |]; try discriminate;
      destruct ti as [|cid'' I W|]; try discriminate.
    move/eqP in RPC; subst Apc.
    generalize RCOMP;
      rewrite /refine_compartments /refine_compartment_tag /= in RCOMP;
      move: RCOMP => [RCOMPS RCTAGS] RCOMP.
    move: (RCTAGS pc) => RCTAGS'; rewrite /Sym.sget PC in RCTAGS';
      destruct RCTAGS' as [SET_I [SET_W [c [IN_c RTAG]]]].
    rewrite /refine_registers /pointwise in RREGS.
    destruct (get AR r) as [x|] eqn:GET;
      [| specialize RREGS with r; rewrite RW GET in RREGS; done].
    assert (EQ : x = w) by
      (by specialize RREGS with r;
          rewrite RW GET /refine_reg_b in RREGS; move/eqP in RREGS);
      subst x.
    evar (AR' : registers t);
      exists (AState (pc + (if w == 0 then 1 else imm_to_word n))%w
                     AR' AM AC INTERNAL c); split;
      subst AR'.
    + eapply Abs.step_bnz; try reflexivity.
      * unfold Abs.decode.
        unfold refine_memory,pointwise,refine_mem_loc_b in RMEMS;
          specialize RMEMS with pc; rewrite PC in RMEMS;
          destruct (get AM pc); [simpl|contradiction].
        move/eqP in RMEMS; subst; eassumption.
      * eassumption.
      * solve_permitted_now_in.
    + constructor; simpl;
        try solve [done | eapply prove_refined_compartment';
                          solve [ eassumption
                                | rewrite /Sym.sget /= PC; reflexivity ]].
  - (* Jal *)
    undo1 NEXT rvec;
      destruct t1; try discriminate;
      destruct told; try discriminate;
      undo1 def_rvec cid;
      undo1 NEXT regs';
      unfold Sym.can_execute,Sym.sfi_rvec in *; unoption; simpl in *.
    destruct tpc as [F cid'| |]; try discriminate;
      destruct ti as [|cid'' I W|]; try discriminate.
    move/eqP in RPC; subst Apc.
    generalize RCOMP;
      rewrite /refine_compartments /refine_compartment_tag /= in RCOMP;
      move: RCOMP => [RCOMPS RCTAGS] RCOMP.
    move: (RCTAGS pc) => RCTAGS'; rewrite /Sym.sget PC in RCTAGS';
      destruct RCTAGS' as [SET_I [SET_W [c [IN_c RTAG]]]].
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
      * solve_permitted_now_in.
      * assumption.
      * unfold upd; rewrite /refine_registers /pointwise in RREGS.
        match goal with |- context[get AR ?ra] =>
          (* This finds the type class instances *)
          specialize RREGS with ra;
          destruct (get AR ra) eqn:GET';
            [reflexivity | rewrite OLD in RREGS; done]
        end.
    + constructor; simpl;
        try solve [done | eapply prove_refined_compartment';
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
        | clear EQ; destruct (add_to_shared_memory_addr == pc) eqn:EQ;
          [ move/eqP in EQ; subst
          | discriminate ]]];
      inversion GETCALL; subst;
      rewrite /Symbolic.run_syscall /Symbolic.handler /sym_sfi
              /Sym.sfi_handler /Symbolic.sem
        in CALL;
      [ eapply isolate_refined              in CALL
      | eapply add_to_jump_targets_refined  in CALL
      | eapply add_to_shared_memory_refined in CALL ];
      try constructor; try eassumption;
      destruct CALL as [ast' [STEP REFINE]];
      exists ast'; split; auto;
      [ eapply Abs.step_syscall with (sc := Abs.isolate              (t:=t))
      | eapply Abs.step_syscall with (sc := Abs.add_to_jump_targets  (t:=t))
      | eapply Abs.step_syscall with (sc := Abs.add_to_shared_memory (t:=t)) ];
      try solve [reflexivity | eassumption];
      destruct tpc as []; try discriminate; move/eqP in RPC; subst;
      try match goal with |- context[get AM ?addr] =>
        rewrite /refine_memory /pointwise in RMEMS;
        specialize (RMEMS addr); rewrite PC in RMEMS;
        by destruct (get AM addr)
      end;
      rewrite /refine_syscall_addrs_b in RSC; repeat move: RSC => /andP [RSC ?];
      rewrite /Abs.get_syscall /= eq_refl.
      * done.
      * by destruct (isolate_addr == add_to_jump_targets_addr).
      * by destruct (isolate_addr == add_to_shared_memory_addr),
                    (add_to_jump_targets_addr == add_to_shared_memory_addr).
Qed.

End RefinementSA.
