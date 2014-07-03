Require Import List. Import ListNotations.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Require Import lib.utils lib.ordered lib.partial_maps common.common.
Require Import symbolic.symbolic symbolic.rules.
Require Import sfi.common sfi.list_utils sfi.set_utils sfi.isolate_sets
               sfi.ranges.

Set Bullet Behavior "Strict Subproofs".

Module Sym.

Inductive stag {t : machine_types} :=
| PC     : forall (S : where_from) (c : word t), stag
| DATA   : forall (c : word t) (I W : list (word t)), stag
| REG    : stag.

Module EnhancedDo.
Export DoNotation.

Notation "'do!' ( X , Y ) <- A ; B" :=
  (bind (fun XY => let '(X,Y) := XY in B) A)
  (at level 200, X ident, Y ident, A at level 100, B at level 200).

Notation "'do!' X @ L <- A ; B" :=
  (bind (fun XL => let '(X @ L) := XL in B) A)
  (at level 200, X ident, L ident, A at level 100, B at level 200).

Notation "'do!' X @ 'REG' <- A ; B" :=
  (bind (fun XREG => match XREG with X @ REG => B | _ => None end) A)
  (at level 200, X ident, A at level 100, B at level 200).

Notation "'do!' X @ 'DATA' c' I' W' <- A ; B" :=
  (bind (fun XcIW => match XcIW with X @ (DATA c' I' W') => B | _ => None end) A)
  (at level 200, X ident, c' ident, I' ident, W' ident,
   A at level 100, B at level 200).

Notation "'do!' 'REG' <- A ; B" :=
  (bind (fun maybeREG => match maybeREG with REG => B | _ => None end) A)
  (at level 200, A at level 100, B at level 200).

Notation "'do!' 'DATA' c' I' W' <- A ; B" :=
  (bind (fun cIW => match cIW with DATA c' I' W' => B | _ => None end) A)
  (at level 200, c' ident, I' ident, W' ident, A at level 100, B at level 200).

Notation "'do!' 'REG' <-! A ; B" :=
  (match A with REG => B | _ => None end)
  (at level 200, A at level 100, B at level 200).

Notation "'do!' 'DATA' c' I' W' <-! A ; B" :=
  (match A with DATA c' I' W' => B | _ => None end)
  (at level 200, c' ident, I' ident, W' ident, A at level 100, B at level 200).

Ltac undo1 hyp var :=
  let def_var := fresh "def_" var in
  match type of hyp with
    | (do! _ <- ?GET; _) = Some _ =>
      destruct GET as [var|] eqn:def_var
    | (do! guard ?COND; _) = Some _ =>
      destruct COND eqn:var
    | match ?OCOND with _ => _ end = Some _ =>
      destruct OCOND as [[|]|] eqn:var
  end; simpl in hyp; try discriminate.

Ltac undo2 hyp v1 v2 :=
  let GET := match type of hyp with
               | (do! (_,_) <- ?GET; _) = Some _ => GET
               | (do! _ @ _ <- ?GET; _) = Some _ => GET
             end
  in let def_v1_v2 := fresh "def_" v1 "_" v2 in
     destruct GET as [[v1 v2]|] eqn:def_v1_v2;
     simpl in hyp; [|discriminate].

Ltac undoDATA hyp x c I W :=
  let xcIW := fresh "xcIW" in
  undo1 hyp xcIW; destruct xcIW as [x [|c I W|]];
  [discriminate | simpl in hyp | discriminate].
End EnhancedDo.

Section WithClasses.

Import PartMaps.
Import EnhancedDo.

Context {t            : machine_types}
        {ops          : machine_ops t}
        {spec         : machine_ops_spec ops}
        {scr          : @syscall_regs t}
        {sfi_syscalls : sfi_syscall_addrs t}.

(* I want to use S and I as variables. *)
Let S := Datatypes.S.
Let I := Logic.I.
(* ssreflect exposes `succn' as a synonym for `S' *)
Local Notation II := Logic.I.

Notation stag := (@stag t).

Definition stag_is_PC (L : stag) : bool :=
  match L with PC _ _ => true | _ => false end.

Definition stag_is_DATA (L : stag) : bool :=
  match L with DATA _ _ _ => true | _ => false end.

Definition stag_is_REG (L : stag) : bool :=
  match L with REG => true | _ => false end.

Definition stag_compartment (L : stag) : option (word t) :=
  match L with PC _ c | DATA c _ _ => Some c | _ => None end.

Definition stag_source (L : stag) : option where_from :=
  match L with PC S _ => Some S | _ => None end.

Definition stag_incoming (L : stag) : option (list (word t)) :=
  match L with DATA _ I _ => Some I | _ => None end.

Definition stag_writers (L : stag) : option (list (word t)) :=
  match L with DATA _ _ W => Some W | _ => None end.

Definition stag_eq (t1 t2 : stag) : bool :=
  match t1, t2 with
    | PC S1 c1      , PC S2 c2      => (S1 == S2) && (c1 == c2)
    | DATA c1 I1 W1 , DATA c2 I2 W2 => (c1 == c2) && (I1 == I2) && (W1 == W2)
    | REG           , REG           => true
    | _             , _             => false
  end.

Lemma stag_eqP : Equality.axiom stag_eq.
Proof.
  by move=> [S1 c1|c1 I1 W1|] [S2 c2|c2 I2 W2|] /=; apply: (iffP idP) => //;
     do [ do ! move/andP=> []; do ! move=> /eqP->
        | case; do ! move=> ->; do ! (apply/andP; split) ].
Qed.

Definition stag_eqMixin := EqMixin stag_eqP.
Canonical stag_eqType := Eval hnf in EqType stag stag_eqMixin.

Context {memory    : Type}
        {sm        : partial_map memory (word t) (atom (word t) stag)}
        {sma       : axioms sm}
        {registers : Type}
        {sr        : partial_map registers (reg t) (atom (word t) stag)}
        {sra       : axioms sr}.

Section WithVectors.
Import Symbolic Coq.Vectors.Vector.VectorNotations.

Definition can_execute (Lpc LI : stag) : option (word t) :=
  match Lpc , LI with
    | PC S c , DATA c' I _ =>
      if      c == c'                       then Some c
      else if (S == JUMPED) && set_elem c I then Some c'
      else None
    | _ , _ => None
  end.

Definition sfi_rvec (S : where_from) (c : word t) : RVec stag :=
  mkRVec (PC S c) REG.  

Definition rvec_step (rv : word t -> option (RVec stag))
                     (Lpc LI : stag)  : option (RVec stag) :=
  do! c <- can_execute Lpc LI;
  rv c.

Definition rvec_simple (S : where_from) : stag -> stag -> option (RVec stag) :=
  rvec_step (fun c => Some (sfi_rvec S c)).

Definition rvec_next : stag -> stag -> option (RVec stag) :=
  rvec_simple INTERNAL.
Definition rvec_jump : stag -> stag -> option (RVec stag) :=
  rvec_simple JUMPED.
Definition rvec_store (c : word t) (I W : list (word t))
                      : stag -> stag -> option (RVec stag) :=
  rvec_step (fun c' =>
    do! guard (c == c') || set_elem c' W;
    Some (mkRVec (PC INTERNAL c') (DATA c I W))).

(* The `REG's in the MVec's fields can also be _s; it's an invariant that
   registers are always tagged with `REG'. *)
Definition sfi_handler (mv : MVec stag) : option (RVec stag) :=
  match mv with
    | mkMVec NOP       Lpc LI []                     => rvec_next        Lpc LI
    | mkMVec CONST     Lpc LI [REG]                  => rvec_next        Lpc LI
    | mkMVec MOV       Lpc LI [REG; REG]             => rvec_next        Lpc LI
    | mkMVec (BINOP _) Lpc LI [REG; REG; REG]        => rvec_next        Lpc LI
    | mkMVec LOAD      Lpc LI [REG; DATA _ _ _; REG] => rvec_next        Lpc LI
    | mkMVec STORE     Lpc LI [REG; REG; DATA c I W] => rvec_store c I W Lpc LI
    | mkMVec JUMP      Lpc LI [REG]                  => rvec_jump        Lpc LI
    | mkMVec BNZ       Lpc LI [REG]                  => rvec_next        Lpc LI
    | mkMVec JAL       Lpc LI [REG; REG]             => rvec_jump        Lpc LI
    | mkMVec SERVICE   _   _  []                     => Some (mkRVec REG REG)
    | mkMVec _         _   _  _                      => None
  end.

End WithVectors.

Record sfi_internal := Internal { next_id : word t
                                ; set_ids : list (list (word t) * word t) }.

Instance sym_sfi : Symbolic.symbolic_params t := {
  tag := stag_eqType;
  
  handler := sfi_handler;
  
  internal_state := sfi_internal;
  
  memory := memory;
  sm     := sm;
  
  registers := registers;
  sr        := sr
}.

Definition fresh (si : sfi_internal) : option (word t * sfi_internal) :=
  let 'Internal next ids := si in
  if next == max_word
  then None
  else Some (next, Internal (next+1)%w ids).

Definition register_set (X : list (word t))
                        (si : sfi_internal) : option sfi_internal :=
  let 'Internal next ids := si in
  match assoc_list_lookup ids (eq_op X) with
    | Some _ => Some si
    | None   => do! (id,si') <- fresh si;
                Some (Internal (next_id si') ((X,id) :: set_ids si'))
  end.  

Fixpoint retag_set (ok : word t -> list (word t) -> list (word t) -> bool)
                   (retag : word t -> list (word t) -> list (word t) -> stag)
                   (ps : list (word t))
                   (M : memory) (si : sfi_internal)
                   : option (memory * sfi_internal) :=
  match ps with
    | []       => Some (M,si)
    | p :: ps' => do! x @ DATA c I W <-  get M p;
                  do! guard (ok c I W);
                  do! DATA _ I' W'   <-! retag c I W;
                  do! si'            <-  register_set I' si;
                  do! si''           <-  register_set W' si';
                  do! M'             <-  upd M p (x @ (DATA c I' W'));
                  retag_set ok retag ps' M' si''
  end.

Definition isolate (s : Symbolic.state t) : option (Symbolic.state t) :=
  match s with
    | Symbolic.State M R (pc @ (PC _ c)) si =>
      do! (c',si') <- fresh si;
      
      do! pA @ _ <- get R syscall_arg1;
      do! pJ @ _ <- get R syscall_arg2;
      do! pS @ _ <- get R syscall_arg3;
      
      do! A'       <- isolate_create_set (@val _ _) M pA;
      do! guard nonempty A';
      do! (MA,siA) <- retag_set (fun c'' _ _ => c == c'')
                                (fun _   I W => DATA c' I W)
                                A' M si';
      
      do! J'       <- isolate_create_set (@val _ _) M pJ;
      do! (MJ,siJ) <- retag_set (fun c'' I _ => (c == c'') || set_elem c I)
                                (fun c'' I W => DATA c'' (insert_unique c' I) W)
                                J' MA siA;
      
      do! S'       <- isolate_create_set (@val _ _) M pS;
      do! (MS,siS) <- retag_set (fun c'' _ W => (c == c'') || set_elem c W)
                                (fun c'' I W => DATA c'' I (insert_unique c' W))
                                S' MJ siJ;
      
      do! pc' @ _ <- get R ra;
      Some (Symbolic.State MS R (pc' @ (PC INTERNAL c)) siS)
    | _ => None
  end.

Definition add_to_jump_targets (s : Symbolic.state t)
                               : option (Symbolic.state t) :=
  match s with
    | Symbolic.State M R (pc @ (PC _ c)) si =>
      do! p @ _           <- get R syscall_arg1;
      do! x @ DATA c' I W <- get M p;
      let I'              := insert_unique c I in
      do! si'             <- register_set I' si;
      do! M'              <- upd M p (x @ (DATA c' I' W));
      do! pc' @ _         <- get R ra;
      Some (Symbolic.State M' R (pc' @ (PC INTERNAL c)) si')
    | _ => None
  end.

Definition add_to_shared_memory (s : Symbolic.state t)
                                : option (Symbolic.state t) :=
  match s with
    | Symbolic.State M R (pc @ (PC _ c)) si =>
      do! p @ _           <- get R syscall_arg1;
      do! x @ DATA c' I W <- get M p;
      let W'              := insert_unique c W in
      do! si'             <- register_set W' si;
      do! M'              <- upd M p (x @ (DATA c' I W'));
      do! pc' @ _         <- get R ra;
      Some (Symbolic.State M' R (pc' @ (PC INTERNAL c)) si')
    | _ => None
  end.

Definition syscalls : list (Symbolic.syscall t) :=
  [Symbolic.Syscall isolate_addr              REG isolate;
   Symbolic.Syscall add_to_jump_targets_addr  REG add_to_jump_targets;
   Symbolic.Syscall add_to_shared_memory_addr REG add_to_shared_memory].

Definition step := Symbolic.step syscalls.

Definition good_internal (si : sfi_internal) : bool :=
  let: Internal next ids := si in
  forallb (fun set_id => let: (set,id) := set_id in
                         is_set set && (id <? next))
          ids.

Definition interned_tag (ids : list (list (word t) * word t))
                        (L : stag) : bool :=
  match L with
    | DATA _ I W => is_some (assoc_list_lookup ids (eq_op I)) &&
                    is_some (assoc_list_lookup ids (eq_op W))
    | _ => false (* or true *)
  end.

Definition good_memory_tag (ids : list (list (word t) * word t))
                           (M : Symbolic.memory t)
                           (p : word t) : bool :=
  match get M p with
    | Some (_ @ (DATA _ I W)) =>
      is_some (assoc_list_lookup ids (eq_op I)) &&
      is_some (assoc_list_lookup ids (eq_op W))
    | Some (_ @ _)            => false
    | None                    => true
  end.

Definition good_register_tag (R : Symbolic.registers t) (r : reg t) : bool :=
  match get R r with
    | Some (_ @ REG) => true
    | Some (_ @ _)   => false
    | None           => true
  end.

Definition good_pc_tag (pc : atom (word t) stag) : bool :=
  match pc with
    | _ @ (PC _ _) => true
    | _ @ _        => false
  end.

Definition good_tags (s : Symbolic.state t) : Prop :=
  let: Symbolic.State M R pc (Internal next ids) := s in
  (forall p, good_memory_tag   ids M p) /\
  (forall r, good_register_tag     R r) /\
  good_pc_tag pc.

Definition good_state (s : Symbolic.state t) : Prop :=
  good_tags s /\ good_internal (Symbolic.internal s).  

(* Implied by the others *)
Definition memory_has_sets (M : memory) (p : word t) : bool :=
  match get M p with
    | Some (_ @ (DATA _ I W)) => is_set I && is_set W
    | Some (_ @ _)            => false
    | None                    => true
  end.

Generalizable All Variables.

Corollary assoc_list_lookup_some_eq : forall (K : eqType) V (kvs : list (K * V))
                                             k v,
  assoc_list_lookup kvs (eq_op k) = Some v ->
  In (k,v) kvs.
Proof.
  intros K V kvs k v ASSOC; apply assoc_list_lookup_some in ASSOC.
  case ASSOC => [k' [/eqP<- IN]]; exact IN.
Qed.

Corollary in_assoc_list_lookup_eq : forall (K : eqType) V (kvs : list (K * V))
                                           k v,
  In (k,v) kvs ->
  exists v', assoc_list_lookup kvs (eq_op k) = Some v'.
Proof.
  intros K V kvs k v IN; eapply in_assoc_list_lookup in IN;
    [eassumption | apply eq_refl].
Qed.

Lemma good_internal_and_memory__memory_has_sets : forall si M p,
  good_internal si ->
  good_memory_tag (set_ids si) M p ->
  memory_has_sets M p.
Proof.
  clear S I.
  unfold good_memory_tag, memory_has_sets; intros si M p GOOD MEM.
  set GET := get M p in MEM *; destruct GET as [[x [|c I W|]]|]; auto.
  destruct si as [next ids]; simpl in *.
  assert (SET : forall X, is_some (assoc_list_lookup ids (eq_op X)) ->
                          is_set X). {
    clear MEM; intros X SOME.
    destruct (assoc_list_lookup _ _) as [id|] eqn:ASSOC; simpl in *; auto.
    apply assoc_list_lookup_some_eq in ASSOC.
    move/forallb_forall in GOOD; apply GOOD in ASSOC.
    by move: ASSOC => /andP [].
  }
  move: MEM => /andP [IN_I IN_W]; apply/andP; auto.
Qed.

Corollary good_state__good_memory : forall s,
  good_state s ->
  forall p, memory_has_sets (Symbolic.mem s) p.
Proof.
  unfold good_state,good_tags;
    move=> [M R pc [next ids]] [[MEM [REG PC]] INT] p.
  eapply good_internal_and_memory__memory_has_sets; eauto.
Qed.

Lemma fresh_preserves_good : forall si si' fid,
  fresh si = Some (fid,si') ->
  good_internal si ->
  good_internal si'.
Proof.
  intros [next ids] [next' ids'] fid FRESH; simpl in *.
  destruct (next == max_word) eqn:BOUND; [discriminate|].
  move=> /eqP in BOUND.
  inversion FRESH; subst; clear FRESH.
  apply forallb_impl.
  move=> [set id] /andP [SET LT]; andb_true_split; auto.
  eapply ltb_trans; [exact LT | apply lebw_succ with max_word].
  generalize (lew_max fid) => /le_iff_lt_or_eq [] //.
Qed.

Lemma register_set_preserves_good : forall si si' X,
  is_set X ->
  register_set X si = Some si' ->
  good_internal si ->
  good_internal si'.
Proof.
  clear S I.
  move=> [next ids] [next' ids'] /= X SET REG GOOD.
  destruct (assoc_list_lookup _ _) eqn:LOOKUP.
  - inversion REG; subst; exact GOOD.
  - destruct (next == max_word) eqn:MAX; simpl in REG; inversion REG; subst.
    simpl; andb_true_split; auto.
    + apply lebw_succ with max_word.
      generalize (lew_max next) => MAX'; apply le__lt_or_eq in MAX'.
      destruct MAX'; [assumption | subst; rewrite eq_refl in MAX; discriminate].
    + eapply forallb_impl; [|apply GOOD]; cbv beta.
      move=> [set id] /andP [SET' LT]; apply /andP; split; auto.
      eapply ltb_trans; [apply LT | apply lebw_succ with max_word].
      generalize (lew_max next) => MAX'; apply le__lt_or_eq in MAX'.
      destruct MAX'; [assumption | subst; rewrite eq_refl in MAX; discriminate].
Qed.

Lemma retag_set_preserves_good : forall si si' ok retag ps M M',
  (forall osi c I W,
     good_internal osi ->
     is_some (assoc_list_lookup (set_ids osi) (eq_op I)) ->
     is_some (assoc_list_lookup (set_ids osi) (eq_op W)) ->
     match retag c I W with
       | DATA _ I' W' =>
         match bind (register_set W') (register_set I' osi) with
           | Some osi' =>
             is_set I' && is_set W' &&
             is_some (assoc_list_lookup (set_ids osi') (eq_op I')) &&
             is_some (assoc_list_lookup (set_ids osi') (eq_op W')) /\
             forall X,
               is_some (assoc_list_lookup (set_ids osi)  (eq_op X)) ->
               is_some (assoc_list_lookup (set_ids osi') (eq_op X))
           | None => True
         end
       | _ => False
     end) ->
  retag_set ok retag ps M si = Some (M',si') ->
  (forall p, good_memory_tag (set_ids si) M p) ->
  good_internal si ->
  (forall p, good_memory_tag (set_ids si') M' p) /\ good_internal si'.
Proof.
  clear S I.
  intros si si' ok retag ps M M' RETAG RETAG_SET; simpl.
  move: si si' M M' RETAG_SET; induction ps as [|p ps];
    move=> /= si si' M M' RETAG_SET.
  - by inversion RETAG_SET; subst.
  - idtac;
      undoDATA RETAG_SET x c I' W; rename I' into I;
      undo1 RETAG_SET OK;
      destruct (retag c I W) as [|c' I' W'|] eqn:def_c'_I'_W'; try discriminate;
      undo1 RETAG_SET si1; undo1 RETAG_SET si2; undo1 RETAG_SET M2.
    intros MEM GOOD.
    unfold good_memory_tag in *.
    move: (MEM p); rewrite def_xcIW; move=> /andP [OK_I OK_W].
    specialize (RETAG si c I W GOOD OK_I OK_W);
      rewrite def_c'_I'_W' def_si1 /= def_si2 in RETAG;
      repeat rewrite <-Bool.andb_assoc in RETAG;
      case: RETAG => [/and4P[SET_I' SET_W' OK_I' OK_W'] PRESERVE].
    eapply IHps; try eassumption.
    + intros p'; destruct (p == p') eqn:EQ_p_p'; move/eqP in EQ_p_p'.
      * subst p'.
        apply get_upd_eq in def_M2; [rewrite def_M2 | exact sma].
        by apply/andP.
      * apply get_upd_neq with (key' := p') in def_M2; auto.
        rewrite def_M2; specialize MEM with p'.
        set GET_M_p' := get M p' in MEM *;
          destruct GET_M_p' as [[? [|c'' I'' W''|]]|]; auto.
        move/andP in MEM; apply/andP; split; apply PRESERVE; tauto.
    + do 2 (
        eapply register_set_preserves_good; [|eassumption|]; [eassumption|]
      ); assumption.
Qed.

Theorem isolate_good : forall s s',
  isolate s = Some s' ->
  good_state s ->
  good_state s'.
Proof.
  clear S I.
  intros [M R [pc [S c| |]] si] s' ISOLATE GOOD;
    simpl in *; try discriminate.
  let DO2 := undo2 ISOLATE in let DO1 := undo1 ISOLATE
  in DO2 c' si'; DO2 pA LA; DO2 pJ LJ; DO2 pS LS;
     DO1 A'; DO1 NONEMPTY_A'; DO2 MA siA;
     DO1 J'; DO2 MJ siJ;
     DO1 S'; DO2 MS siS;
     DO2 pc' Lpc';
     inversion ISOLATE; subst; clear ISOLATE; simpl.
  rewrite /good_state /= in GOOD; destruct GOOD as [TAGS INT].
  assert (GOOD_si' : good_internal si') by eauto 2 using fresh_preserves_good.
  assert (GOOD_MA_siA : (forall p, good_memory_tag (set_ids siA) MA p) /\
                        good_internal siA). {
    apply retag_set_preserves_good in def_MA_siA; auto.
    - intros osi _ I W OGOOD OK_I OK_W;
        destruct (register_set I osi)  as [osi'|]  eqn:REG; simpl; auto;
        destruct (register_set W osi') as [osi''|] eqn:REG'; auto.
      unfold register_set in *;
        destruct osi as [onext oids], osi' as [onext' oids']; simpl in *.
      destruct (assoc_list_lookup oids (eq_op I)) eqn:ASSOC_I;
        auto; simpl in *.
      inversion REG; subst; simpl in *.
      destruct (assoc_list_lookup oids' (eq_op W)) eqn:ASSOC_W;
        auto; simpl in *.
      inversion REG'; subst; simpl in *.
      rewrite ASSOC_I ASSOC_W; simpl; do ! rewrite andbT.
      split; auto.
      hnf in OGOOD; rewrite ->forallb_forall in OGOOD;
        apply assoc_list_lookup_some_eq, OGOOD in ASSOC_W;
        apply assoc_list_lookup_some_eq, OGOOD in ASSOC_I;
        move: ASSOC_W ASSOC_I => /andP[SET_W _] /andP[SET_I _].
      by apply/andP.
    - destruct si as [next ids], TAGS as [MEM [REG _]]; simpl in def_c'_si'.
      destruct (next == max_word); [discriminate|].
      inversion def_c'_si'; subst; simpl in *; apply MEM.
  }
  assert (GOOD_MJ_siJ : (forall p, good_memory_tag (set_ids siJ) MJ p) /\
                        good_internal siJ). {
    apply retag_set_preserves_good in def_MJ_siJ; try tauto.
    intros osi _ I W OGOOD OK_I OK_W;
      destruct (register_set (insert_unique c' I) osi)  as [osi'|] eqn:REG;
      simpl; auto;
      destruct (register_set W osi') as [osi''|] eqn:REG'; auto.
    unfold register_set in *;
      destruct osi as [onext oids], osi' as [onext' oids']; simpl in *.
    hnf in OGOOD; rewrite ->forallb_forall in OGOOD.
    destruct (assoc_list_lookup oids (eq_op I)) eqn:ASSOC_I; auto.
    destruct (assoc_list_lookup oids (eq_op (insert_unique c' I)))
             eqn:ASSOC_I';
      auto; simpl in *.
    - inversion REG; subst; simpl in *.
      destruct (assoc_list_lookup oids' (eq_op W)) eqn:ASSOC_W;
        auto; simpl in *.
      inversion REG'; subst; simpl in *.
      rewrite ASSOC_I' ASSOC_W; simpl; do ! rewrite andbT.
      split; auto;
        apply assoc_list_lookup_some_eq, OGOOD in ASSOC_W;
        apply assoc_list_lookup_some_eq, OGOOD in ASSOC_I';
        move: ASSOC_W ASSOC_I' => /andP[SET_W _] /andP[SET_I' _].
      by apply/andP.
    - destruct (onext == max_word); [discriminate|]; simpl in REG.
      inversion REG; subst; simpl in *.
      destruct (assoc_list_lookup oids (eq_op W)) eqn:ASSOC_W; auto;
        simpl in *.
      destruct (W == insert_unique c' I) eqn:EQ_W; [move: EQ_W => /eqP->|];
        inversion REG'; subst; simpl in *.
      + rewrite eq_refl; simpl in *.
        do ! rewrite andbT; rewrite Bool.andb_diag.
        split; [|intros X SOME; destruct (X == _); auto].
        apply insert_unique_preserves_set_true.
        apply assoc_list_lookup_some_eq,OGOOD in ASSOC_I.
        by move: ASSOC_I => /andP[].
      + rewrite eq_refl EQ_W ASSOC_W; simpl; do ! rewrite andbT.
        split; [|intros X SOME; destruct (X == _); auto].
        idtac;
          apply assoc_list_lookup_some_eq,OGOOD in ASSOC_I;
          apply assoc_list_lookup_some_eq,OGOOD in ASSOC_W.
        move: ASSOC_W ASSOC_I => /andP[SET_W _] /andP[SET_I _].
        apply/andP; auto.
  }
  assert (GOOD_MS_siS : (forall p, good_memory_tag (set_ids siS) MS p) /\
                        good_internal siS). {
    apply retag_set_preserves_good in def_MS_siS; try tauto.
    intros osi _ I W OGOOD OK_I OK_W;
      destruct (register_set I osi)  as [osi'|] eqn:REG; simpl; auto;
      destruct (register_set (insert_unique c' W) osi') as [osi''|] eqn:REG';
      auto.
    unfold register_set in *;
      destruct osi as [onext oids], osi' as [onext' oids']; simpl in *.
    hnf in OGOOD; rewrite ->forallb_forall in OGOOD.
    destruct (assoc_list_lookup oids (eq_op W)) eqn:ASSOC_W; auto.
    destruct (assoc_list_lookup oids (eq_op I)) eqn:ASSOC_I; auto.
    inversion REG; subst; simpl in *.
    destruct (assoc_list_lookup oids' (eq_op (insert_unique c' W)))
             eqn:ASSOC_W'.
    - inversion REG'; subst; simpl in *.
      rewrite ASSOC_I ASSOC_W'; simpl; do ! rewrite andbT.
      split; auto;
        apply assoc_list_lookup_some_eq, OGOOD in ASSOC_I;
        apply assoc_list_lookup_some_eq, OGOOD in ASSOC_W';
        move: ASSOC_I ASSOC_W' => /andP[SET_I _] /andP[SET_W' _].
      by apply/andP.
    - destruct (onext' == max_word); [discriminate|]; simpl in REG'.
      inversion REG'; subst; simpl in *.
      destruct (I == insert_unique c' W) eqn:EQ_I; [move: EQ_I => /eqP->|].
      + rewrite eq_refl; simpl in *.
        do ! rewrite andbT; rewrite Bool.andb_diag.
        split; [|intros X SOME; destruct (X == _); auto].
        apply insert_unique_preserves_set_true.
        apply assoc_list_lookup_some_eq,OGOOD in ASSOC_W.
        by move: ASSOC_W => /andP[].
      + rewrite eq_refl ASSOC_I; simpl; do ! rewrite andbT.
        split; [|intros X SOME; destruct (X == _); auto].
        idtac;
          apply assoc_list_lookup_some_eq,OGOOD in ASSOC_I;
          apply assoc_list_lookup_some_eq,OGOOD in ASSOC_W.
        move: ASSOC_W ASSOC_I => /andP[SET_W _] /andP[SET_I _].
        apply/andP; auto.
  }
  destruct si as [next ids], siS as [nextS idsS]; rewrite /good_state /=; tauto.
Qed.

Theorem add_to_jump_targets_good : forall s s',
  add_to_jump_targets s = Some s' ->
  good_state s ->
  good_state s'.
Proof.
  clear S I.
  intros [M R [pc [S c| |]] si] s' ADD GOOD; try discriminate; simpl in *.
  undo2 ADD p Lp; undo2 ADD x Lx; destruct Lx as [|c' I W|]; try discriminate;
    undo1 ADD si'; undo1 ADD M'; undo2 ADD pc' Lpc';
  inversion ADD; subst; simpl in *.
  destruct si as [next ids].
  rewrite /good_state /= in GOOD; destruct GOOD as [[MEM [REG _]] INT].
  assert (SET_I : is_set I). {
    specialize MEM with p; unfold good_memory_tag in MEM;
      rewrite def_x_Lx in MEM; move: MEM => /andP [OK_I OK_W].
    unfold is_true in INT; rewrite ->forallb_forall in INT.
    destruct (assoc_list_lookup ids (eq_op I)) eqn:ASSOC_I; auto.
    apply assoc_list_lookup_some_eq,INT in ASSOC_I.
    by move: ASSOC_I => /andP [].
  }
  assert (INT' : good_internal si') by
    (apply register_set_preserves_good in def_si'; auto).
  rewrite /good_state /=.
  destruct si' as [next' ids']; repeat split; try tauto.
  simpl in def_si'.
  intros p'; specialize MEM with p'; unfold good_memory_tag in *.
  destruct (p == p') eqn:EQ_P; move/eqP in EQ_P; [subst p'|].
  - apply get_upd_eq in def_M'; [rewrite def_M' | exact sma].
    rewrite def_x_Lx in MEM.
    move: MEM => /andP [OK_I OK_W]; apply/andP.
    destruct (assoc_list_lookup ids (eq_op (insert_unique c I))) eqn:ASSOC_I'.
    + by inversion def_si'; subst; rewrite ASSOC_I'.
    + destruct (next == max_word); [discriminate|]; simpl in def_si';
        inversion def_si'; subst; simpl in *.
      by rewrite eq_refl; destruct (W == insert_unique c I).
  - apply get_upd_neq with (key' := p') in def_M'; auto; rewrite def_M'.
    set GET_M_p' := get M p' in MEM *;
      destruct GET_M_p' as [[? [|c'' I'' W''|]]|]; auto.
    destruct (assoc_list_lookup ids (eq_op (insert_unique c I))) eqn:ASSOC_I'.
    + by inversion def_si'; subst.
    + destruct (next == max_word); [discriminate|]; simpl in def_si';
        inversion def_si'; subst; simpl in *.
      move: MEM => /andP [OK_I'' OK_W''].
      by apply/andP; destruct (I'' == _), (W'' == _).
Qed.

Theorem add_to_shared_memory_good : forall s s',
  add_to_shared_memory s = Some s' ->
  good_state s ->
  good_state s'.
Proof.
  clear S I.
  intros [M R [pc [S c| |]] si] s' ADD GOOD; try discriminate; simpl in *.
  undo2 ADD p Lp; undo2 ADD x Lx; destruct Lx as [|c' I W|]; try discriminate;
    undo1 ADD si'; undo1 ADD M'; undo2 ADD pc' Lpc';
  inversion ADD; subst; simpl in *.
  destruct si as [next ids].
  rewrite /good_state /= in GOOD; destruct GOOD as [[MEM [REG _]] INT].
  assert (SET_I : is_set W). {
    specialize MEM with p; unfold good_memory_tag in MEM;
      rewrite def_x_Lx in MEM; move: MEM => /andP [OK_I OK_W].
    unfold is_true in INT; rewrite ->forallb_forall in INT.
    destruct (assoc_list_lookup ids (eq_op W)) eqn:ASSOC_W; auto.
    apply assoc_list_lookup_some_eq,INT in ASSOC_W.
    by move: ASSOC_W => /andP [].
  }
  assert (INT' : good_internal si') by
    (apply register_set_preserves_good in def_si'; auto).
  rewrite /good_state /=.
  destruct si' as [next' ids']; repeat split; try tauto.
  simpl in def_si'.
  intros p'; specialize MEM with p'; unfold good_memory_tag in *.
  destruct (p == p') eqn:EQ_P; move/eqP in EQ_P; [subst p'|].
  - apply get_upd_eq in def_M'; [rewrite def_M' | exact sma].
    rewrite def_x_Lx in MEM.
    move: MEM => /andP [OK_I OK_W]; apply/andP.
    destruct (assoc_list_lookup ids (eq_op (insert_unique c W))) eqn:ASSOC_W'.
    + by inversion def_si'; subst; rewrite ASSOC_W'.
    + destruct (next == max_word); [discriminate|]; simpl in def_si';
        inversion def_si'; subst; simpl in *.
      by rewrite eq_refl; destruct (I == insert_unique c W).
  - apply get_upd_neq with (key' := p') in def_M'; auto; rewrite def_M'.
    set GET_M_p' := get M p' in MEM *;
      destruct GET_M_p' as [[? [|c'' I'' W''|]]|]; auto.
    destruct (assoc_list_lookup ids (eq_op (insert_unique c W))) eqn:ASSOC_W'.
    + by inversion def_si'; subst.
    + destruct (next == max_word); [discriminate|]; simpl in def_si';
        inversion def_si'; subst; simpl in *.
      move: MEM => /andP [OK_I'' OK_W''].
      by apply/andP; destruct (I'' == _), (W'' == _).
Qed.

Theorem good_state_preserved : forall `(STEP : step s s'),
  good_state s ->
  good_state s'.
Proof.
  clear S I.
  intros s s' STEP GOOD; destruct STEP;
    unfold Symbolic.next_state_reg, Symbolic.next_state_pc,
           Symbolic.next_state_reg_and_pc, Symbolic.next_state in *;
    simpl in *;
    unfold rvec_next, rvec_jump, rvec_store, rvec_simple, rvec_step in *;
    repeat match goal with
      | NEXT : (do! _ <- ?m; _) = Some _ |- _ =>
        destruct m eqn:?; simpl in NEXT; [|discriminate]
      | TAG  : match ?t with _ => _ end = Some _ |- _ =>
        destruct t; try discriminate
      | EQN  : Some _ = Some _ |- _ =>
        inversion EQN; subst; simpl; auto; clear EQN
    end;
    try (
      destruct int as [next ids], GOOD as [[MEM [REG PC]] INT];
      repeat split; try tauto;
      let k' := fresh "k'" in
      intros k';
      match goal with
        | UPD : upd _ ?k _ = Some _ |- appcontext[?good_fn _] =>
          unfold good_fn;
          destruct (k' == k) eqn:EQ; move/eqP in EQ;
          [ subst; apply get_upd_eq in UPD
          | apply get_upd_neq with (key' := k') in UPD ];
          auto; rewrite UPD;
          [ auto
          | first [apply MEM | apply REG] ]
      end);
    simpl in *;
    try match type of CALL with
      | ?t =>
        match t with
          | Symbolic.run_syscall (Symbolic.Syscall _ _ ?fn) _ = _ =>
            replace t with (fn (Symbolic.State mem reg pc@tpc int) = Some s')
              in * by reflexivity
        end
    end.
  - (* store *)
    unfold is_true in INT; rewrite ->forallb_forall in INT.
    by specialize MEM with w1; rewrite /good_memory_tag OLD in MEM.
  - (* isolate *)
    apply isolate_good in CALL; assumption.
  - (* add_to_jump_targets *)
    apply add_to_jump_targets_good in CALL; assumption.
  - (* add_to_shared_memory *)
    apply add_to_shared_memory_good in CALL; assumption.
Qed.

End WithClasses.

End Sym.
