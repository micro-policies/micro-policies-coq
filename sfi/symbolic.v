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

Context {word_map  : Type -> Type}
        {sw        : partial_map word_map (word t)}
        {swa       : axioms sw}
        {reg_map   : Type -> Type}
        {sr        : partial_map reg_map (reg t)}
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

Record sfi_internal := Internal { next_id : word t }.

Instance sym_sfi : Symbolic.symbolic_params t := {
  tag := stag_eqType;
  
  handler := sfi_handler;
  
  internal_state := sfi_internal;
  
  word_map := word_map;
  sw       := sw;
  
  reg_map   := reg_map;
  sr        := sr
}.

Definition fresh (si : sfi_internal) : option (word t * sfi_internal) :=
  let 'Internal next := si in
  if next == max_word
  then None
  else Some (next, Internal (next+1)%w).

Fixpoint retag_set (ok : word t -> list (word t) -> list (word t) -> bool)
                   (retag : word t -> list (word t) -> list (word t) -> stag)
                   (ps : list (word t))
                   (M : Symbolic.memory t)
                   : option (Symbolic.memory t) :=
  match ps with
    | []       => Some M
    | p :: ps' => do! x @ DATA c I W <-  get M p;
                  do! guard (ok c I W);
                  do! DATA _ I' W'   <-! retag c I W;
                  do! M'             <-  upd M p (x @ (DATA c I' W'));
                  retag_set ok retag ps' M'
  end.

Definition isolate (s : Symbolic.state t) : option (Symbolic.state t) :=
  match s with
    | Symbolic.State M R (pc @ (PC _ c)) si =>
      do! (c',si') <- fresh si;
      
      do! pA @ _ <- get R syscall_arg1;
      do! pJ @ _ <- get R syscall_arg2;
      do! pS @ _ <- get R syscall_arg3;
      
      do! A' <- isolate_create_set (@val _ _) M pA;
      do! guard nonempty A';
      do! MA <- retag_set (fun c'' _ _ => c == c'')
                          (fun _   I W => DATA c' I W)
                          A' M;
      
      do! J' <- isolate_create_set (@val _ _) M pJ;
      do! MJ <- retag_set (fun c'' I _ => (c == c'') || set_elem c I)
                          (fun c'' I W => DATA c'' (insert_unique c' I) W)
                          J' MA;
      
      do! S' <- isolate_create_set (@val _ _) M pS;
      do! MS <- retag_set (fun c'' _ W => (c == c'') || set_elem c W)
                          (fun c'' I W => DATA c'' I (insert_unique c' W))
                          S' MJ;
      
      do! pc' @ _ <- get R ra;
      Some (Symbolic.State MS R (pc' @ (PC INTERNAL c)) si')
    | _ => None
  end.

Definition add_to_jump_targets (s : Symbolic.state t)
                               : option (Symbolic.state t) :=
  match s with
    | Symbolic.State M R (pc @ (PC _ c)) si =>
      do! p @ _           <- get R syscall_arg1;
      do! x @ DATA c' I W <- get M p;
      do! M'              <- upd M p (x @ (DATA c' (insert_unique c I) W));
      do! pc' @ _         <- get R ra;
      Some (Symbolic.State M' R (pc' @ (PC INTERNAL c)) si)
    | _ => None
  end.

Definition add_to_shared_memory (s : Symbolic.state t)
                                : option (Symbolic.state t) :=
  match s with
    | Symbolic.State M R (pc @ (PC _ c)) si =>
      do! p @ _           <- get R syscall_arg1;
      do! x @ DATA c' I W <- get M p;
      do! M'              <- upd M p (x @ (DATA c' I (insert_unique c W)));
      do! pc' @ _         <- get R ra;
      Some (Symbolic.State M' R (pc' @ (PC INTERNAL c)) si)
    | _ => None
  end.

Definition syscalls : list (Symbolic.syscall t) :=
  [Symbolic.Syscall isolate_addr              REG isolate;
   Symbolic.Syscall add_to_jump_targets_addr  REG add_to_jump_targets;
   Symbolic.Syscall add_to_shared_memory_addr REG add_to_shared_memory].

Definition step := Symbolic.step syscalls.

Definition good_internal (si : sfi_internal) : bool :=
  true.

Definition good_memory_tag (M : Symbolic.memory t)
                           (p : word t) : bool :=
  match get M p with
    | Some (_ @ (DATA _ I W)) => is_set I && is_set W
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
  let: Symbolic.State M R pc si := s in
  (forall p, good_memory_tag   M p) /\
  (forall r, good_register_tag R r) /\
  good_pc_tag pc.

Definition good_state (s : Symbolic.state t) : Prop :=
  good_tags s /\ good_internal (Symbolic.internal s).

Generalizable All Variables.

Lemma fresh_preserves_good : forall si si' fid,
  fresh si = Some (fid,si') ->
  good_internal si ->
  good_internal si'.
Proof. auto. Qed.

Lemma retag_set_preserves_good : forall ok retag ps M M',
  (forall c I W,
     is_set I ->
     is_set W ->
     match retag c I W with
       | DATA _ I' W' => is_set I' && is_set W'
       | _            => false
     end) ->
  retag_set ok retag ps M = Some M' ->
  (forall p, good_memory_tag M  p) ->
  (forall p, good_memory_tag M' p).
Proof.
  clear S I.
  intros ok retag ps M M' RETAG RETAG_SET; simpl.
  move: M M' RETAG_SET; induction ps as [|p ps];
    move=> /= M M' RETAG_SET.
  - by inversion RETAG_SET; subst.
  - idtac;
      undoDATA RETAG_SET x c I' W; rename I' into I;
      undo1 RETAG_SET OK;
      destruct (retag c I W) as [|c' I' W'|] eqn:def_c'_I'_W'; try discriminate;
      undo1 RETAG_SET M2.
    intros MEM GOOD.
    unfold good_memory_tag in *.
    move: (MEM p); rewrite def_xcIW; move=> /andP [SET_I SET_W].
    specialize (RETAG c I W SET_I SET_W);
      rewrite def_c'_I'_W' /= in RETAG;
      repeat rewrite <-Bool.andb_assoc in RETAG.
      move: RETAG => /andP [SET_I' SET_W'].
    eapply IHps; try eassumption.
    intros p'; destruct (p == p') eqn:EQ_p_p'; move/eqP in EQ_p_p'.
    + subst p'.
      apply get_upd_eq in def_M2; [rewrite def_M2 | exact swa].
      by apply/andP.
    + apply get_upd_neq with (key' := p') in def_M2; auto.
      rewrite def_M2; specialize MEM with p'.
      by set GET_M_p' := get M p' in MEM *; 
         destruct GET_M_p' as [[? [|c'' I'' W''|]]|].
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
     DO1 A'; DO1 NONEMPTY_A'; DO1 MA;
     DO1 J'; DO1 MJ;
     DO1 S'; DO1 MS;
     DO2 pc' Lpc';
     inversion ISOLATE; subst; clear ISOLATE; simpl.
  rewrite /good_state in GOOD *; simpl in *;
    move: GOOD => [[MEM [REG _]] _];
    repeat split; auto.
  assert (GOOD_MA_siA : forall p, good_memory_tag MA p). {
    intros p; apply retag_set_preserves_good with (p := p) in def_MA; auto.
    intros _ I W SET_I SET_W; apply/andP; auto.
  }
  assert (GOOD_MJ_siJ : forall p, good_memory_tag MJ p). {
    intros p; apply retag_set_preserves_good with (p := p) in def_MJ; auto.
    intros _ I W SET_I SET_W; apply/andP; auto.
  }
  assert (GOOD_MS_siS : forall p, good_memory_tag MS p). {
    intros p; apply retag_set_preserves_good with (p := p) in def_MS; auto.
    intros _ I W SET_I SET_W; apply/andP; auto.
  }
  auto.
Qed.

Theorem add_to_jump_targets_good : forall s s',
  add_to_jump_targets s = Some s' ->
  good_state s ->
  good_state s'.
Proof.
  clear S I.
  intros [M R [pc [S c| |]] si] s' ADD GOOD; try discriminate; simpl in *.
  undo2 ADD p Lp; undo2 ADD x Lx; destruct Lx as [|c' I W|]; try discriminate;
    undo1 ADD M'; undo2 ADD pc' Lpc';
    inversion ADD; subst; simpl in *; clear ADD.
  move: GOOD => [[MEM [REG _]] _]; rewrite /good_state; repeat split; auto.
  intros p'; specialize MEM with p'; unfold good_memory_tag in *.
  destruct (p == p') eqn:EQ_P; move/eqP in EQ_P; [subst p'|].
  - apply get_upd_eq in def_M'; [rewrite def_M' | exact swa].
    rewrite def_x_Lx in MEM; move: MEM => /andP [SET_I' SET_W]; apply/andP;
      auto.
  - apply get_upd_neq with (key' := p') in def_M'; auto; rewrite def_M'.
    set GET_M_p' := get M p' in MEM *;
      destruct GET_M_p' as [[? [|c'' I'' W''|]]|]; auto.
Qed.

Theorem add_to_shared_memory_good : forall s s',
  add_to_shared_memory s = Some s' ->
  good_state s ->
  good_state s'.
Proof.
  clear S I.
  intros [M R [pc [S c| |]] si] s' ADD GOOD; try discriminate; simpl in *.
  undo2 ADD p Lp; undo2 ADD x Lx; destruct Lx as [|c' I W|]; try discriminate;
    undo1 ADD M'; undo2 ADD pc' Lpc';
    inversion ADD; subst; simpl in *; clear ADD.
  move: GOOD => [[MEM [REG _]] _]; rewrite /good_state; repeat split; auto.
  intros p'; specialize MEM with p'; unfold good_memory_tag in *.
  destruct (p == p') eqn:EQ_P; move/eqP in EQ_P; [subst p'|].
  - apply get_upd_eq in def_M'; [rewrite def_M' | exact swa].
    rewrite def_x_Lx in MEM; move: MEM => /andP [SET_I SET_W']; apply/andP;
      auto.
  - apply get_upd_neq with (key' := p') in def_M'; auto; rewrite def_M'.
    set GET_M_p' := get M p' in MEM *;
      destruct GET_M_p' as [[? [|c'' I'' W''|]]|]; auto.
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
      destruct int as [next], GOOD as [[MEM [REG PC]] INT];
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
