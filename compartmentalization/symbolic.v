Require Import List. Import ListNotations.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Require Import lib.utils lib.ordered lib.partial_maps common.common.
Require Import symbolic.symbolic symbolic.rules.
Require Import lib.list_utils lib.set_utils.
Require Import compartmentalization.common.
Require Import compartmentalization.isolate_sets compartmentalization.ranges.

Set Bullet Behavior "Strict Subproofs".

Module Sym.

Inductive stag {t : machine_types} :=
| PC     : forall (F : where_from) (c : word t), stag
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

Notation "'do!' X @ 'PC' F c <- A ; B" :=
  (bind (fun XFc => match XFc with X @ (PC F c) => B | _ => None end) A)
  (at level 200, X ident, F ident, c ident, A at level 100, B at level 200).

Notation "'do!' X @ 'DATA' c' I' W' <- A ; B" :=
  (bind (fun XcIW => match XcIW with X @ (DATA c' I' W') => B | _ => None end) A)
  (at level 200, X ident, c' ident, I' ident, W' ident,
   A at level 100, B at level 200).

Notation "'do!' X @ 'REG' <- A ; B" :=
  (bind (fun XREG => match XREG with X @ REG => B | _ => None end) A)
  (at level 200, X ident, A at level 100, B at level 200).

Notation "'do!' 'PC' F c <- A ; B" :=
  (bind (fun Fc => match Fc with PC F c => B | _ => None end) A)
  (at level 200, F ident, c ident, A at level 100, B at level 200).

Notation "'do!' 'DATA' c' I' W' <- A ; B" :=
  (bind (fun cIW => match cIW with DATA c' I' W' => B | _ => None end) A)
  (at level 200, c' ident, I' ident, W' ident, A at level 100, B at level 200).

Notation "'do!' 'REG' <- A ; B" :=
  (bind (fun maybeREG => match maybeREG with REG => B | _ => None end) A)
  (at level 200, A at level 100, B at level 200).

Notation "'do!' 'PC' F c <-! A ; B" :=
  (match A with PC F c => B | _ => None end)
  (at level 200, F ident, c ident, A at level 100, B at level 200).

Notation "'do!' 'DATA' c' I' W' <-! A ; B" :=
  (match A with DATA c' I' W' => B | _ => None end)
  (at level 200, c' ident, I' ident, W' ident, A at level 100, B at level 200).

Notation "'do!' 'REG' <-! A ; B" :=
  (match A with REG => B | _ => None end)
  (at level 200, A at level 100, B at level 200).

Ltac undo1 hyp var :=
  let def_var := fresh "def_" var in
  match type of hyp with
    | (do! _ <- ?GET; _) ?= _ =>
      destruct GET as [var|] eqn:def_var
    | (do! guard ?COND; _) ?= _ =>
      destruct COND eqn:var
    | match ?OCOND with _ => _ end ?= _ =>
      destruct OCOND as [[|]|] eqn:var
  end; simpl in hyp; try discriminate.

Ltac undo2 hyp v1 v2 :=
  let GET := match type of hyp with
               | (do! (_,_) <- ?GET; _) ?= _ => GET
               | (do! _ @ _ <- ?GET; _) ?= _ => GET
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
        {cmp_syscalls : compartmentalization_syscall_addrs t}.

(* I want to use I as a variable. *)
Let I := Logic.I.
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
  match L with PC F _ => Some F | _ => None end.

Definition stag_incoming (L : stag) : option (list (word t)) :=
  match L with DATA _ I _ => Some I | _ => None end.

Definition stag_writers (L : stag) : option (list (word t)) :=
  match L with DATA _ _ W => Some W | _ => None end.

Definition stag_eq (t1 t2 : stag) : bool :=
  match t1, t2 with
    | PC F1 c1      , PC F2 c2      => (F1 == F2) && (c1 == c2)
    | DATA c1 I1 W1 , DATA c2 I2 W2 => (c1 == c2) && (I1 == I2) && (W1 == W2)
    | REG           , REG           => true
    | _             , _             => false
  end.

Lemma stag_eqP : Equality.axiom stag_eq.
Proof.
  by move=> [F1 c1|c1 I1 W1|] [F2 c2|c2 I2 W2|] /=; apply: (iffP idP) => //;
     do [ do ! move/andP=> []; do ! move=> /eqP->
        | case; do ! move=> ->; do ! (apply/andP; split) ].
Qed.

Definition stag_eqMixin := EqMixin stag_eqP.
Canonical stag_eqType := Eval hnf in EqType stag stag_eqMixin.

Section WithVectors.
Import Symbolic Coq.Vectors.Vector.VectorNotations.

Definition can_execute (Lpc LI : stag) : option (word t) :=
  do! PC   F  c   <-! Lpc;
  do! DATA c' I _ <-! LI;
  do! guard (c' == c) || ((F == JUMPED) && set_elem c I);
  Some c'.

Definition compartmentalization_rvec (F : where_from)
                                     (c : word t) : RVec stag :=
  mkRVec (PC F c) REG.  

Definition rvec_step (rv : word t -> option (RVec stag))
                     (Lpc LI : stag)  : option (RVec stag) :=
  do! c <- can_execute Lpc LI;
  rv c.

Definition rvec_simple (F : where_from) : stag -> stag -> option (RVec stag) :=
  rvec_step (fun c => Some (compartmentalization_rvec F c)).

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
Definition compartmentalization_handler (mv : MVec stag) : option (RVec stag) :=
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
    | mkMVec SERVICE   Lpc LI  []                    => Some (mkRVec REG REG)
    | mkMVec _         _   _  _                      => None
  end.

End WithVectors.

Record compartmentalization_internal :=
  Internal { next_id                  : word t
           ; isolate_tag              : stag
           ; add_to_jump_targets_tag  : stag
           ; add_to_store_targets_tag : stag }.

Instance sym_compartmentalization : Symbolic.params := {
  tag := stag_eqType;
  
  handler := compartmentalization_handler;
  
  internal_state := compartmentalization_internal
}.

Local Notation memory    :=
  (word_map t (atom (word t) (@Symbolic.tag sym_compartmentalization))).
Local Notation registers :=
  (reg_map  t (atom (word t) (@Symbolic.tag sym_compartmentalization))).

Hint Immediate word_map_axioms.
Hint Immediate reg_map_axioms.

Definition sget (s : Symbolic.state t) (p : word t)
                : option (atom (word t) stag) :=
  let: Symbolic.State mem _ _ si := s in
  let sctag get_tag := Some 0%w@(get_tag si) in
  match get mem p with
    | Some v => Some v
    | None   =>
      if      p == isolate_addr              then sctag isolate_tag
      else if p == add_to_jump_targets_addr  then sctag add_to_jump_targets_tag
      else if p == add_to_store_targets_addr then sctag add_to_store_targets_tag
      else None
  end.
Arguments sget s p : simpl never.

Definition supd (s : Symbolic.state t) (p : word t) (v : atom (word t) stag)
                : option (Symbolic.state t) :=
  let: Symbolic.State mem reg pc si := s in
  let: Internal next_id
                isolate_tag
                add_to_jump_targets_tag
                add_to_store_targets_tag :=
       si in
  let sctagged si' := Some (Symbolic.State mem reg pc si') in
  match upd mem p v with
    | Some mem' => Some (Symbolic.State mem' reg pc si)
    | None      =>
      if      p == isolate_addr
        then sctagged (Internal next_id
                                (common.tag v)
                                add_to_jump_targets_tag
                                add_to_store_targets_tag)
      else if p == add_to_jump_targets_addr
        then sctagged (Internal next_id
                                isolate_tag
                                (common.tag v)
                                add_to_store_targets_tag)
      else if p == add_to_store_targets_addr
        then sctagged (Internal next_id
                                isolate_tag
                                add_to_jump_targets_tag
                                (common.tag v))
      else None
  end.
Arguments supd s p v : simpl never.

Definition fresh (si : compartmentalization_internal)
                 : option (word t * compartmentalization_internal) :=
  let 'Internal next iT ajtT asmT := si in
  if next == max_word
  then None
  else Some (next, Internal (next+1)%w iT ajtT asmT).

Fixpoint retag_set (ok : word t -> list (word t) -> list (word t) -> bool)
                   (retag : word t -> list (word t) -> list (word t) -> stag)
                   (ps : list (word t))
                   (s : Symbolic.state t)
                   : option (Symbolic.state t) :=
  match ps with
    | []       => Some s
    | p :: ps' => do! x @ DATA c I W <-  sget s p;
                  do! guard (ok c I W);
                  do! DATA c' I' W'  <-! retag c I W;
                  do! s'             <-  supd s p (x @ (DATA c' I' W'));
                  retag_set ok retag ps' s'
  end.

Definition isolate (s : Symbolic.state t) : option (Symbolic.state t) :=
  match s with
    | Symbolic.State M R (pc @ (PC F c)) si =>
      do! _ @ LI <- sget s pc;
      do! c_sys  <- can_execute (PC F c) LI;
      
      do! (c',si') <- fresh si;
      let s' := Symbolic.State M R (pc @ (PC F c)) si' in
      
      do! pA @ _ <- get R syscall_arg1;
      do! pJ @ _ <- get R syscall_arg2;
      do! pS @ _ <- get R syscall_arg3;
      
      do! A' <- isolate_create_set (@val _ _) M pA;
      do! guard nonempty A';
      do! sA <- retag_set (fun c'' _ _ => c == c'')
                          (fun _   I W => DATA c' I W)
                          A' s';
      
      do! J' <- isolate_create_set (@val _ _) M pJ;
      do! sJ <- retag_set (fun c'' I _ => (c == c'') || (c' == c'') ||
                                          set_elem c I)
                          (fun c'' I W => DATA c'' (insert_unique c' I) W)
                          J' sA;
      
      do! S' <- isolate_create_set (@val _ _) M pS;
      do! sS <- retag_set (fun c'' _ W => (c == c'') || (c' == c'') ||
                                          set_elem c W)
                          (fun c'' I W => DATA c'' I (insert_unique c' W))
                          S' sJ;
      
      do! pc' @ _                    <- get  R  ra;
      do! _   @ DATA c_next I_next _ <- sget sS pc';
      do! guard c == c_next;
      do! guard set_elem c_sys I_next;

      let: Symbolic.State M_next R_next _ si_next := sS in
      Some (Symbolic.State M_next R_next (pc' @ (PC JUMPED c_sys)) si_next)
    | _ => None
  end.

Definition add_to_jump_targets (s : Symbolic.state t)
                               : option (Symbolic.state t) :=
  match s with
    | Symbolic.State M R (pc @ (PC F c)) si =>
      do! _ @ LI <- sget s pc;
      do! c_sys  <- can_execute (PC F c) LI;
      do! guard c != c_sys;
      
      do! p @ _             <- get R syscall_arg1;
      do! x @ DATA c' I' W' <- sget s p;
      
      do! guard (c' == c) || set_elem c I';
      do! s' <- supd s p (x @ (DATA c' (insert_unique c I') W'));
      
      do! pc' @ _                    <- get R ra;
      do! _   @ DATA c_next I_next _ <- sget s' pc';
      do! guard c == c_next;
      do! guard set_elem c_sys I_next;

      let: Symbolic.State M_next R_next _ si_next := s' in
      Some (Symbolic.State M_next R_next (pc' @ (PC JUMPED c_sys)) si_next)
    | _ => None
  end.

Definition add_to_store_targets (s : Symbolic.state t)
                                : option (Symbolic.state t) :=
  match s with
    | Symbolic.State M R (pc @ (PC F c)) si =>
      do! _ @ LI <- sget s pc;
      do! c_sys  <- can_execute (PC F c) LI;
      do! guard c != c_sys;
      
      do! p @ _             <- get R syscall_arg1;
      do! x @ DATA c' I' W' <- sget s p;
      
      do! guard (c' == c) || set_elem c W';
      do! s' <- supd s p (x @ (DATA c' I' (insert_unique c W')));
      
      do! pc' @ _                    <- get R ra;
      do! _   @ DATA c_next I_next _ <- sget s' pc';
      do! guard c == c_next;
      do! guard set_elem c_sys I_next;

      let: Symbolic.State M_next R_next _ si_next := s' in
      Some (Symbolic.State M_next R_next (pc' @ (PC JUMPED c_sys)) si_next)
    | _ => None
  end.

Definition syscalls : list (Symbolic.syscall t) :=
  [Symbolic.Syscall isolate_addr              REG isolate;
   Symbolic.Syscall add_to_jump_targets_addr  REG add_to_jump_targets;
   Symbolic.Syscall add_to_store_targets_addr REG add_to_store_targets].

Definition step := Symbolic.step syscalls.

Definition good_internal (s : Symbolic.state t) : Prop :=
  let: Internal next iT aJT aST := Symbolic.internal s in
  match iT , aJT , aST with
    | DATA iC _ _ , DATA aJC _ _ , DATA aST _ _ =>
      iC <> aJC /\ iC <> aST /\ aJC <> aST /\
      iC < next /\ aJC < next /\ aST < next /\
      forall p x c I W,
        get (Symbolic.mem s) p ?= x@(DATA c I W) ->
        c < next /\ c <> iC /\ c <> aJC /\ c <> aST
    | _ , _ , _ =>
      False
  end.

Definition good_memory_tag (s : Symbolic.state t)
                           (p : word t) : bool :=
  match sget s p with
    | Some (_ @ (DATA _ I W)) => is_set I && is_set W
    | Some (_ @ _)            => false
    | None                    => true
  end.

Definition good_register_tag (R : registers) (r : reg t) : bool :=
  match get R r with
    | Some (_ @ REG) => true
    | Some (_ @ _)   => false
    | None           => true
  end.

Definition good_pc_tag (s : Symbolic.state t)
                       (pc : atom (word t) stag) : Prop :=
  match pc with
    | _ @ (PC _ c) => exists p x I W, sget s p ?= x@(Sym.DATA c I W)
    | _ @ _        => False
  end.

Definition good_tags (s : Symbolic.state t) : Prop :=
  let: Symbolic.State M R pc si := s in
  (forall p, good_memory_tag   s p) /\
  (forall r, good_register_tag R r) /\
  good_pc_tag s pc.

Definition good_state (s : Symbolic.state t) : Prop :=
  good_tags s /\ good_internal s.

Generalizable All Variables.

Theorem sget_supd_eq : forall s s' p x L L',
  sget s  p      ?= x@L ->
  supd s  p x@L' ?= s'  ->
  sget s' p      ?= x@L'.
Proof.
  intros [mem reg pc [next iT aJT aST]] [mem' reg' pc' [next' iT' aJT' aST']]
         p x L L' SGET SUPD;
    unfold sget,supd,upd in *; simpl in *.
  let finish := inversion SGET; subst; clear SGET;
                inversion SUPD; subst; clear SUPD;
                by first [rewrite get_set_eq | rewrite GET]
  in destruct (get mem p) as [[x' Lx']|] eqn:GET; [finish|];
     repeat match type of SUPD with
       | context[if ?COND then _ else _] => destruct COND; [finish|]
     end;
     inversion SUPD.
Qed.  

Theorem sget_supd_neq : forall s s' p p' v,
  p' <> p ->
  supd s p v ?= s' ->
  sget s' p' = sget s p'.
Proof.
  intros [mem reg pc [next iT aJT aST]] [mem' reg' pc' [next' iT' aJT' aST']]
         p p' v NEQ SUPD;
    unfold sget,supd,upd in *; simpl in *.
  destruct (get mem p) as [v'|] eqn:GET.
  - inversion SUPD; subst.
    by rewrite get_set_neq.
  - destruct (p == isolate_addr) eqn:EQI; move/eqP in EQI;
      [|destruct (p == add_to_jump_targets_addr) eqn:EQJ; move/eqP in EQJ;
        [|destruct (p == add_to_store_targets_addr) eqn:EQS; move/eqP in EQS]];
      inversion SUPD; subst;
      (destruct (get mem' p'); [done|]).
    + destruct (p' == isolate_addr) eqn:EQ'; move/eqP in EQ';
        [congruence | done].
    + destruct (p' == isolate_addr); auto.
      destruct (p' == add_to_jump_targets_addr) eqn:EQ'; move/eqP in EQ';
        [congruence | done].
    + destruct (p' == isolate_addr); auto.
      destruct (p' == add_to_jump_targets_addr); auto.
      destruct (p' == add_to_store_targets_addr) eqn:EQ'; move/eqP in EQ';
        [congruence | done].
Qed.          

Theorem get_supd_eq : forall s s' p x L L',
  get (Symbolic.mem s) p ?= x@L ->
  supd s p x@L' ?= s' ->
  get (Symbolic.mem s') p ?= x@L'.
Proof.
  intros [mem reg pc [next iT aJT aST]] [mem' reg' pc' [next' iT' aJT' aST']]
         p x L L' SGET SUPD;
    unfold sget,supd,upd in *; simpl in *.
  let finish := inversion SGET; subst; clear SGET;
                inversion SUPD; subst; clear SUPD;
                by first [rewrite get_set_eq | rewrite GET]
  in destruct (get mem p) as [[x' Lx']|] eqn:GET; [finish|];
     repeat match type of SUPD with
       | context[if ?COND then _ else _] => destruct COND; [finish|]
     end;
     inversion SUPD.
Qed.  

Theorem get_supd_neq : forall s s' p p' v,
  p' <> p ->
  supd s p v ?= s' ->
  get (Symbolic.mem s') p' = get (Symbolic.mem s) p'.
Proof.
  intros [mem reg pc [next iT aJT aST]] [mem' reg' pc' [next' iT' aJT' aST']]
         p p' v NEQ SUPD;
    unfold sget,supd,upd in *; simpl in *.
  destruct (get mem p) as [v'|] eqn:GET.
  - inversion SUPD; subst.
    by rewrite get_set_neq.
  - by destruct (p == isolate_addr);
        [|destruct (p == add_to_jump_targets_addr);
          [|destruct (p == add_to_store_targets_addr)]];
       inversion SUPD; subst.
Qed.

Theorem get_supd_none : forall s s' p p' v,
  get (Symbolic.mem s) p = None ->
  supd s p' v ?= s' ->
  get (Symbolic.mem s') p = None.
Proof.
  intros [mem reg pc [next iT aJT aST]] [mem' reg' pc' [next' iT' aJT' aST']]
         p p' v SGET SUPD; simpl in *.
  destruct (p' == p) eqn:EQ; move/eqP in EQ; subst.
  - unfold sget,supd,upd in *; simpl in *.
    let finish := inversion SGET; subst; clear SGET;
                  inversion SUPD; subst; clear SUPD;
                  by first [rewrite get_set_eq | rewrite GET]
    in destruct (get mem p) as [[x Lx]|] eqn:GET; [finish|];
       repeat match type of SUPD with
         | context[if ?COND then _ else _] => destruct COND; [finish|]
       end;
       inversion SUPD.
  - eapply get_supd_neq in SUPD; eauto; simpl in *.
    congruence.
Qed.

Theorem supd_preserves_regs : forall s p v s',
  supd s p v ?= s' ->
  Symbolic.regs s = Symbolic.regs s'.
Proof.
  move=> [mem reg pc [next iT aJT aST]] /= p v s' SUPD;
    rewrite /supd /= in SUPD.
  destruct (upd mem p v) eqn:UPD; rewrite UPD in SUPD.
  - by inversion SUPD; subst.
  - by destruct (p == isolate_addr);
         [|destruct (p == add_to_jump_targets_addr);
           [|destruct (p == add_to_store_targets_addr)]];
       inversion SUPD; subst.
Qed.

Theorem supd_preserves_pc : forall s p v s',
  supd s p v ?= s' ->
  Symbolic.pc s = Symbolic.pc s'.
Proof.
  move=> [mem reg pc [next iT aJT aST]] /= p v s' SUPD;
    rewrite /supd /= in SUPD.
  destruct (upd mem p v) eqn:UPD; rewrite UPD in SUPD.
  - by inversion SUPD; subst.
  - by destruct (p == isolate_addr);
         [|destruct (p == add_to_jump_targets_addr);
           [|destruct (p == add_to_store_targets_addr)]];
       inversion SUPD; subst.
Qed.

Theorem supd_preserves_next_id : forall s p v s',
  supd s p v ?= s' ->
  next_id (Symbolic.internal s) = next_id (Symbolic.internal s').
Proof.
  move=> [mem reg pc [next iT aJT aST]] /= p v s' SUPD;
    rewrite /supd /= in SUPD.
  destruct (upd mem p v) eqn:UPD; rewrite UPD in SUPD.
  - by inversion SUPD; subst.
  - by destruct (p == isolate_addr);
         [|destruct (p == add_to_jump_targets_addr);
           [|destruct (p == add_to_store_targets_addr)]];
       inversion SUPD; subst.
Qed.

Lemma succ_trans : forall x y,
  y <> max_word -> x < y -> x < (y + 1)%w.
Proof.
  intros x y NEQ LT.
  generalize (lew_max y) => /le_iff_lt_or_eq [] // LT_max.
  apply lt_trans with (b := y); first by [].
  by apply ltb_lt, lebw_succ with (y := max_word).
Qed.
Hint Resolve succ_trans.

Lemma sget_lt_next : forall s p x c I W,
  good_internal s ->
  sget s p ?= x@(DATA c I W) ->
  c < next_id (Symbolic.internal s).
Proof.
  clear I; move=> [mem reg pc [next Li LaJ LaS]] /= p x c I W GOOD SGET.
  rewrite /good_internal /= in GOOD;
    destruct Li  as [|ci  Ii  Wi|];  try done;
    destruct LaJ as [|caJ IaJ WaJ|]; try done;
    destruct LaS as [|caS IaS WaS|]; try done.
  destruct GOOD as [NEQiaJ [NEQiaS [NEQaJaS [LTi [LTaJ [LTaS GOOD]]]]]].
  rewrite /sget in SGET.
  destruct (get mem p) eqn:GET.
  - rewrite SGET in GET; eapply GOOD; eassumption.
  - destruct (p == isolate_addr);              [by inversion SGET; subst|].
    destruct (p == add_to_jump_targets_addr);  [by inversion SGET; subst|].
    destruct (p == add_to_store_targets_addr); [by inversion SGET; subst|].
    discriminate.
Qed.

Lemma fresh_preserves_good : forall mem reg pc si si' fid,
  fresh si ?= (fid,si') ->
  good_internal (Symbolic.State mem reg pc si) ->
  good_internal (Symbolic.State mem reg pc si').
Proof.
  clear I; move=> mem reg pc [next iT aJT aST] /= si' fid FRESH.
  destruct (next == max_word) eqn:EQ;
    [discriminate | simpl in FRESH; move/eqP in EQ].
  inversion FRESH; subst; clear FRESH.
  rewrite /good_internal /=.
  destruct iT  as [|ci Ii Wi|],
           aJT as [|caJ IaJ WaJ|],
           aST as [|caS IaS WaS|];
    auto.
  intros [NEQ_i_aJ [NEQ_i_aS [NEQ_aJ_aS [LT_ci [LT_caJ [LT_caS GOOD]]]]]].
    do 6 (split; eauto 2).
  intros p x c I W GET; specialize (GOOD p x c I W GET).
    move: GOOD => [LT [NEQ_i [NEQ_aJ NEQ_aS]]].
  repeat split; eauto 2.
Qed.

Lemma retag_set_preserves_definedness : forall ok retag ps s s',
  retag_set ok retag ps s ?= s' ->
  forall p, is_some (sget s p) <-> is_some (sget s' p).
Proof.
  clear I; intros ok retag ps; induction ps as [|p ps]; simpl;
    intros s s' RETAG p'.
  - by inversion RETAG; subst.
  - let I := fresh "I"
    in undoDATA RETAG x c I W; undo1 RETAG OK;
       destruct (retag c I W) as [|c' I' W'|]; try discriminate;
       undo1 RETAG s''.
    apply IHps with (p := p') in RETAG.
    assert (EQUIV : is_some (sget s'' p') <-> is_some (sget s p')). {
      destruct (p == p') eqn:EQ; move/eqP in EQ; [subst p'|].
      - eapply sget_supd_eq in def_s''; eauto.
        by rewrite def_s'' def_xcIW.
      - apply sget_supd_neq with (p' := p') in def_s''; auto.
        by rewrite def_s''.
    }
    tauto.
Qed.

Lemma retag_set_preserves_get_definedness : forall ok retag ps s s',
  retag_set ok retag ps s ?= s' ->
  forall p, is_some (get (Symbolic.mem s) p) <->
            is_some (get (Symbolic.mem s') p).
Proof.
  clear I; intros ok retag ps; induction ps as [|p ps]; simpl;
    intros s s'' RETAG p'.
  - by inversion RETAG; subst.
  - let I := fresh "I"
    in undoDATA RETAG x c I W; undo1 RETAG OK;
       destruct (retag c I W) as [|c' I' W'|]; try discriminate;
       undo1 RETAG s'.
    apply IHps with (p := p') in RETAG.
    assert (EQUIV : is_some (get (Symbolic.mem s)  p') <->
                    is_some (get (Symbolic.mem s') p')). {
      destruct s  as [mem  reg  pc  [next  iT  aJT  aST]],
               s' as [mem' reg' pc' [next' iT' aJT' aST']];
        simpl in *.
      destruct (p == p') eqn:EQ; move/eqP in EQ; [subst p'|].
      - destruct (get mem p) as [[y Ly]|] eqn:GET'.
        + rewrite /sget GET' in def_xcIW.
          move: def_xcIW => [] *; subst.
          eapply get_supd_eq in def_s'; eauto; simpl in *.
          by rewrite def_s'.
        + eapply get_supd_none in def_s'; eauto; simpl in *.
          by rewrite def_s'.
      - eapply get_supd_neq in def_s'; eauto; simpl in *.
        by rewrite def_s'.
    }
    tauto.
Qed.

Lemma retag_set_forall : forall ok retag ps s s',
  NoDup ps ->
  retag_set ok retag ps s ?= s' ->
  forall p,
    In p ps ->
    exists x c I W, sget s p ?= x@(DATA c I W) /\ ok c I W.
Proof.
  clear I; move=> ok retag ps; move: ok retag; induction ps as [|p ps];
    move=> //= ok retag s s'' NODUP RETAG_SET p' IN.
  let I := fresh "I"
  in undoDATA RETAG_SET x c I W;
     undo1    RETAG_SET OK;
     destruct (retag c I W) as [|c' I' W'|] eqn:RETAG; simpl in *; try done;
     undo1    RETAG_SET s'.
  move: IN => [? | IN]; [subst p'|].
  - by rewrite def_xcIW; repeat eexists.
  - inversion NODUP as [|? ? NIN NODUP']; subst.
    assert (NEQ : p' <> p) by (by intro; subst).
    apply IHps with (p := p') in RETAG_SET; auto.
    move: RETAG_SET => [x'' [c'' [I'' [W'' [SGET'' OK'']]]]].
    eapply sget_supd_neq in def_s'; [|eassumption].
    by rewrite -def_s' SGET''; repeat eexists.
Qed.

Lemma retag_set_not_in : forall ok retag ps s s',
  retag_set ok retag ps s ?= s' ->
  forall p,
    ~ In p ps ->
    sget s p = sget s' p.
Proof.
  clear I; intros ok retag ps; induction ps as [|p ps]; simpl;
    intros s s' RETAG p' NIN.
  - by inversion RETAG; subst.
  - let I := fresh "I"
    in undoDATA RETAG x c I W; undo1 RETAG OK;
       destruct (retag c I W) as [|c' I' W'|] eqn:TAG; try discriminate;
       undo1 RETAG s''.
    apply Decidable.not_or in NIN; move: NIN => [NEQ NIN].
    apply IHps with (p := p') in RETAG; auto.
    apply sget_supd_neq with (p' := p') in def_s''; auto.
    by rewrite -RETAG def_s''.
Qed.

Lemma retag_set_in_ok : forall ok retag ps s s',
  NoDup ps ->
  retag_set ok retag ps s ?= s' ->
  forall p,
    In p ps ->
    exists x c I W, sget s  p ?= x@(DATA c I W) /\
                    ok c I W /\
                    sget s' p ?= x@(retag c I W).
Proof.
  clear I; intros ok retag ps; induction ps as [|p ps]; simpl;
    intros s s' NODUP RETAG p' IN.
  - inversion IN.
  - let I := fresh "I"
    in undoDATA RETAG x c I W; undo1 RETAG OK;
       destruct (retag c I W) as [|c' I' W'|] eqn:TAG; try discriminate;
       undo1 RETAG s''.
    inversion NODUP as [|p'' ps'' NIN NODUP']; subst;
      clear NODUP; rename NODUP' into NODUP.
    apply retag_set_not_in with (ok := ok) (retag := retag)
                                (s := s'') (s' := s')
      in NIN; [|assumption].
    destruct IN as [? | IN]; subst.
    + exists x,c,I,W.
      split; auto.
      eapply sget_supd_eq in def_s''; eauto.
      by rewrite -NIN def_s'' TAG.
    + destruct (p == p') eqn:EQ; move/eqP in EQ; subst.
      * exists x,c,I,W.
        repeat (split; auto).
        eapply sget_supd_eq in def_s''; eauto.
        by rewrite -NIN def_s'' TAG.
      * apply IHps with (p := p') in RETAG; auto.
        destruct RETAG as [xi [ci [Ii [Wi [GET1 GET2]]]]].
        exists xi,ci,Ii,Wi; split; auto.
        apply sget_supd_neq with (p' := p') in def_s''; auto.
        by rewrite -def_s''.
Qed.

Lemma retag_set_in : forall ok retag ps s s',
  NoDup ps ->
  retag_set ok retag ps s ?= s' ->
  forall p,
    In p ps ->
    exists x c I W, sget s  p ?= x@(DATA c I W) /\
                    sget s' p ?= x@(retag c I W).
Proof.
  intros until 0; intros NODUP RETAG p IN.
  eapply retag_set_in_ok in RETAG; eauto.
  repeat invh ex; repeat invh and; repeat eexists; eassumption.
Qed.

Lemma retag_set_or_ok : forall ok retag ps s s',
  NoDup ps ->
  (forall p, good_memory_tag s p) ->
  retag_set ok retag ps s ?= s' ->
  forall p,
    sget s p = sget s' p \/
    exists x c I W, sget s p ?= x@(DATA c I W) /\
                    ok c I W /\
                    sget s' p ?= x@(retag c I W).
Proof.
  intros ok retag ps s s' NODUP GMEM RETAG p.
  destruct (elem p ps) as [IN | NIN].
  - eapply retag_set_in_ok in RETAG; eauto.
  - eapply retag_set_not_in in RETAG; eauto.
Qed.

Lemma retag_set_or : forall ok retag ps s s',
  NoDup ps ->
  (forall p, good_memory_tag s p) ->
  retag_set ok retag ps s ?= s' ->
  forall p,
    sget s p = sget s' p \/
    exists x c I W, sget s p ?= x@(DATA c I W) /\ sget s' p ?= x@(retag c I W).
Proof.
  intros ok retag ps s s' NODUP GMEM RETAG p.
  destruct (elem p ps) as [IN | NIN].
  - eapply retag_set_in in RETAG; eauto.
  - eapply retag_set_not_in in RETAG; eauto.
Qed.

Lemma sget_eq__get_eq : forall s s' p,
  (is_some (get (Symbolic.mem s) p) <-> is_some (get (Symbolic.mem s') p)) ->
  sget s p = sget s' p ->
  get (Symbolic.mem s) p = get (Symbolic.mem s') p.
Proof.
  intros [mem reg pc [next iT aJT aST]] [mem' reg' pc' [next' iT' aJT' aST']]
         p GETS SGETS; simpl in *.
  rewrite /sget /= in SGETS.
  by destruct (get mem p),(get mem' p); simpl in *;
     try (destruct GETS;
          match goal with H : is_true true -> is_true false |- _ =>
            specialize (H erefl)
          end).
Qed.

Lemma retag_set_or_ok_get : forall ok retag ps s s',
  NoDup ps ->
  (forall p, good_memory_tag s p) ->
  retag_set ok retag ps s ?= s' ->
  forall p,
    get (Symbolic.mem s) p = get (Symbolic.mem s') p \/
    exists x c I W, get (Symbolic.mem s) p ?= x@(DATA c I W) /\
                    ok c I W /\
                    get (Symbolic.mem s') p ?= x@(retag c I W).
Proof.
  clear I; intros ok retag ps s s' NODUP GMEM RETAG p.
  generalize (retag_set_preserves_get_definedness ok retag ps s s' RETAG p)
             => GETS.
  generalize (retag_set_or_ok ok retag ps s s' NODUP GMEM RETAG p)
             => [[EQ | [x [c [I [W [OLD [OK NEW]]]]]]]].
  - by left; apply sget_eq__get_eq in EQ.
  - rewrite /sget /= in OLD; rewrite /sget /= in NEW;
      destruct s  as [mem  reg  pc  [next  iT  aJT  aST]],
               s' as [mem' reg' pc' [next' iT' aJT' aST']];
        simpl in *.
    destruct (get mem p),(get mem' p); simpl in *.
    + right; repeat eexists; eauto.
    + by destruct GETS as [NO _]; specialize (NO erefl).
    + by destruct GETS as [_ NO]; specialize (NO erefl).
    + by left.
Qed.

Lemma retag_set_preserves_good_memory_tag : forall ok retag ps s s',
  (forall c I W,
     is_set I ->
     is_set W ->
     match retag c I W with
       | DATA _ I' W' => is_set I' && is_set W'
       | _            => false
     end) ->
  retag_set ok retag ps s ?= s' ->
  (forall p, good_memory_tag s  p) ->
  (forall p, good_memory_tag s' p).
Proof.
  clear I.
  intros ok retag ps s s' RETAG RETAG_SET; simpl.
  move: s s' RETAG_SET; induction ps as [|p ps];
    move=> /= s s' RETAG_SET.
  - by inversion RETAG_SET; subst.
  - idtac;
      undoDATA RETAG_SET x c I' W; rename I' into I;
      undo1 RETAG_SET OK;
      destruct (retag c I W) as [|c' I' W'|] eqn:def_c'_I'_W'; try discriminate;
      undo1 RETAG_SET s2.
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
      eapply sget_supd_eq in def_s2; eauto 1; rewrite def_s2.
      by apply/andP.
    + apply sget_supd_neq with (p' := p') in def_s2; auto.
      rewrite def_s2; specialize MEM with p'.
      by destruct (sget s p') as [[? [|c'' I'' W''|]]|].
Qed.

Lemma retag_set_preserves_regs : forall ok retag ps s s',
  retag_set ok retag ps s ?= s' ->
  Symbolic.regs s = Symbolic.regs s'.
Proof.
  clear I.
  intros ok retag ps s s' RETAG_SET; simpl.
  move: s s' RETAG_SET; induction ps as [|p ps];
    move=> /= s s' RETAG_SET.
  - by inversion RETAG_SET; subst.
  - idtac;
      undoDATA RETAG_SET x c I' W; rename I' into I;
      undo1 RETAG_SET OK;
      destruct (retag c I W) as [|c' I' W'|] eqn:def_c'_I'_W'; try discriminate;
      undo1 RETAG_SET s2.
    apply supd_preserves_regs in def_s2; apply IHps in RETAG_SET; congruence.
Qed.

Lemma retag_set_preserves_pc : forall ok retag ps s s',
  retag_set ok retag ps s ?= s' ->
  Symbolic.pc s = Symbolic.pc s'.
Proof.
  clear I.
  intros ok retag ps s s' RETAG_SET; simpl.
  move: s s' RETAG_SET; induction ps as [|p ps];
    move=> /= s s' RETAG_SET.
  - by inversion RETAG_SET; subst.
  - idtac;
      undoDATA RETAG_SET x c I' W; rename I' into I;
      undo1 RETAG_SET OK;
      destruct (retag c I W) as [|c' I' W'|] eqn:def_c'_I'_W'; try discriminate;
      undo1 RETAG_SET s2.
    apply supd_preserves_pc in def_s2; apply IHps in RETAG_SET; congruence.
Qed.

Lemma retag_set_preserves_next_id : forall ok retag ps s s',
  retag_set ok retag ps s ?= s' ->
  next_id (Symbolic.internal s) = next_id (Symbolic.internal s').
Proof.
  clear I.
  intros ok retag ps s s' RETAG_SET; simpl.
  move: s s' RETAG_SET; induction ps as [|p ps];
    move=> /= s s' RETAG_SET.
  - by inversion RETAG_SET; subst.
  - idtac;
      undoDATA RETAG_SET x c I' W; rename I' into I;
      undo1 RETAG_SET OK;
      destruct (retag c I W) as [|c' I' W'|] eqn:def_c'_I'_W'; try discriminate;
      undo1 RETAG_SET s2.
    apply supd_preserves_next_id in def_s2; apply IHps in RETAG_SET; congruence.
Qed.

Lemma good_internal_equiv : forall s s',
  (forall p,
     match sget s p , sget s' p with
       | Some _@(DATA c _ _) , Some _@(DATA c' _ _) => c = c'
       | None                , None                 => True
       | _                   , _                    => False
     end) ->
  next_id (Symbolic.internal s) = next_id (Symbolic.internal s') ->
  ~~ is_some (get (Symbolic.mem s) isolate_addr) ->
  ~~ is_some (get (Symbolic.mem s) add_to_jump_targets_addr) ->
  ~~ is_some (get (Symbolic.mem s) add_to_store_targets_addr) ->
  ~~ is_some (get (Symbolic.mem s') isolate_addr) ->
  ~~ is_some (get (Symbolic.mem s') add_to_jump_targets_addr) ->
  ~~ is_some (get (Symbolic.mem s') add_to_store_targets_addr) ->
  isolate_addr != add_to_jump_targets_addr ->
  isolate_addr != add_to_store_targets_addr ->
  add_to_jump_targets_addr != add_to_store_targets_addr ->
  good_internal s ->
  good_internal s'.
Proof.
  clear I; move=> s s'
                  TAGS NEXT
                  NOT_SOME_I NOT_SOME_aJ NOT_SOME_aS
                  NOT_SOME_I' NOT_SOME_aJ' NOT_SOME_aS'
                  DIFF_I_aJ DIFF_I_aS DIFF_aJ_aS.
  
  assert (INONE : get (Symbolic.mem s) isolate_addr = None)
    by by destruct (get (Symbolic.mem s) isolate_addr).
  assert (AJNONE : get (Symbolic.mem s) add_to_jump_targets_addr = None)
    by by destruct (get (Symbolic.mem s) add_to_jump_targets_addr).
  assert (ASNONE : get (Symbolic.mem s) add_to_store_targets_addr = None)
    by by destruct (get (Symbolic.mem s) add_to_store_targets_addr).
  
  assert (INONE' : get (Symbolic.mem s') isolate_addr = None)
    by by destruct (get (Symbolic.mem s') isolate_addr).
  assert (AJNONE' : get (Symbolic.mem s') add_to_jump_targets_addr = None)
    by by destruct (get (Symbolic.mem s') add_to_jump_targets_addr).
  assert (ASNONE' : get (Symbolic.mem s') add_to_store_targets_addr = None)
    by by destruct (get (Symbolic.mem s') add_to_store_targets_addr).

  assert (FALSE_aJ_I : (add_to_jump_targets_addr == isolate_addr) = false)
   by by rewrite eq_sym in DIFF_I_aJ; move/Bool.negb_true_iff in DIFF_I_aJ.
  assert (FALSE_aS_I : (add_to_store_targets_addr == isolate_addr) = false)
   by by rewrite eq_sym in DIFF_I_aS; move/Bool.negb_true_iff in DIFF_I_aS.
  assert (FALSE_aS_aJ: (add_to_store_targets_addr ==
                        add_to_jump_targets_addr) = false)
   by by rewrite eq_sym in DIFF_aJ_aS; move/Bool.negb_true_iff in DIFF_aJ_aS.

  destruct s  as [mem  reg  pc  [next  iT  aJT  aST]],
           s' as [mem' reg' pc' [next' iT' aJT' aST']];
    simpl in *; subst next'.

  assert (SGET_I :
            sget (Symbolic.State mem reg pc (Internal next iT aJT aST))
                 isolate_addr ?= 0%w@iT).
    by by rewrite /sget INONE eq_refl.
  assert (SGET_aJ :
            sget (Symbolic.State mem reg pc (Internal next iT aJT aST))
                 add_to_jump_targets_addr ?= 0%w@aJT)
    by by rewrite /sget AJNONE FALSE_aJ_I eq_refl.
  assert (SGET_aS :
            sget (Symbolic.State mem reg pc (Internal next iT aJT aST))
                 add_to_store_targets_addr ?= 0%w@aST)
    by by rewrite /sget ASNONE FALSE_aS_I FALSE_aS_aJ eq_refl.
  
  assert (SGET_I' :
            sget (Symbolic.State mem' reg' pc' (Internal next iT' aJT' aST'))
                 isolate_addr ?= 0%w@iT')
    by by rewrite /sget INONE' eq_refl.
  assert (SGET_aJ' :
            sget (Symbolic.State mem' reg' pc' (Internal next iT' aJT' aST'))
                 add_to_jump_targets_addr ?= 0%w@aJT')
    by by rewrite /sget AJNONE' FALSE_aJ_I eq_refl.
  assert (SGET_aS' :
            sget (Symbolic.State mem' reg' pc' (Internal next iT' aJT' aST'))
                 add_to_store_targets_addr ?= 0%w@aST')
    by by rewrite /sget ASNONE' FALSE_aS_I FALSE_aS_aJ eq_refl.
  
  rewrite /good_internal /=; move=> GOOD.
  generalize (TAGS isolate_addr) => TAGS_I;
    rewrite SGET_I SGET_I' in TAGS_I;
    destruct iT as [|ci Wi Ii|], iT' as [|ci' Wi' Ii'|]; try done;
    subst ci'.
  generalize (TAGS add_to_jump_targets_addr) => TAGS_aJ;
    rewrite SGET_aJ SGET_aJ' in TAGS_aJ;
    destruct aJT as [|caJ WaJ IaJ|], aJT' as [|caJ' WaJ' IaJ'|]; try done;
    subst caJ'.
  generalize (TAGS add_to_store_targets_addr) => TAGS_aS;
    rewrite SGET_aS SGET_aS' in TAGS_aS;
    destruct aST as [|caS WaS IaS|], aST' as [|caS' WaS' IaS'|]; try done;
    subst caS'.
  repeat move: GOOD => [? GOOD].
  repeat (split; [assumption|]).
  intros p x c I W GET'.
  move/id in TAGS; specialize TAGS with p.
  rewrite /sget GET' in TAGS.
  destruct (get mem p) as [[y [|cy Iy Wy|]]|] eqn:GET; rewrite GET in TAGS;
   try done; subst.
  - apply GOOD in GET; assumption.
  - by destruct (p == isolate_addr) eqn:EQ_I;
         move/eqP in EQ_I;
         [|destruct (p == add_to_jump_targets_addr) eqn:EQ_aJ;
           move/eqP in EQ_aJ;
             [|destruct (p == add_to_store_targets_addr) eqn:EQ_aS;
               move/eqP in EQ_aS]];
       subst; try congruence.
Qed.
  
Lemma retag_set_updating_preserves_good_internal : forall ok cnew ps s s',
  cnew <> max_word ->
  next_id (Symbolic.internal s) = (cnew+1)%w ->
  ~~ is_some (get (Symbolic.mem s) isolate_addr) ->
  ~~ is_some (get (Symbolic.mem s) add_to_jump_targets_addr) ->
  ~~ is_some (get (Symbolic.mem s) add_to_store_targets_addr) ->
  isolate_addr != add_to_jump_targets_addr ->
  isolate_addr != add_to_store_targets_addr ->
  add_to_jump_targets_addr != add_to_store_targets_addr ->
  ~ In isolate_addr ps ->
  ~ In add_to_jump_targets_addr ps ->
  ~ In add_to_store_targets_addr ps ->
  NoDup ps ->
  (forall p, good_memory_tag s p) ->
  retag_set ok (fun _ I W => DATA cnew I W) ps s ?= s' ->
  good_internal (Symbolic.State
                   (Symbolic.mem s) (Symbolic.regs s) (Symbolic.pc s)
                   (Internal
                      cnew
                      (isolate_tag              (Symbolic.internal s))
                      (add_to_jump_targets_tag  (Symbolic.internal s))
                      (add_to_store_targets_tag (Symbolic.internal s)))) ->
  good_internal s'.
Proof.
  clear I; move=> ok cnew ps s s'
                  NMAX NEXT
                  NOT_SOME_i NOT_SOME_aJ NOT_SOME_aS
                  DIFF_i_aJ DIFF_i_aS DIFF_aJ_aS
                  NIN_i NIN_aJ NIN_aS
                  NODUP GMEM
                  RETAG_SET.

  assert (GETS : forall p, is_some (get (Symbolic.mem s) p) <->
                           is_some (get (Symbolic.mem s') p))
    by (eapply retag_set_preserves_get_definedness; eassumption).

  assert (INONE : get (Symbolic.mem s) isolate_addr = None)
    by by destruct (get (Symbolic.mem s) isolate_addr).
  assert (AJNONE : get (Symbolic.mem s) add_to_jump_targets_addr = None)
    by by destruct (get (Symbolic.mem s) add_to_jump_targets_addr) eqn:H.
  assert (ASNONE : get (Symbolic.mem s) add_to_store_targets_addr = None)
    by by destruct (get (Symbolic.mem s) add_to_store_targets_addr) eqn:H.
  
  assert (NOT_SOME_i' : ~~ is_some (get (Symbolic.mem s') isolate_addr)). {
    apply/negP; move=> SOME; apply GETS in SOME.
    simpl in SOME; move/negP in NOT_SOME_i.
    contradiction.
  }
  
  assert (NOT_SOME_aJ' : ~~ is_some (get (Symbolic.mem s')
                                         add_to_jump_targets_addr)). {
    apply/negP; move=> SOME; apply GETS in SOME.
    simpl in SOME; move/negP in NOT_SOME_aJ.
    contradiction.
  }
  
  assert (NOT_SOME_aS' : ~~ is_some (get (Symbolic.mem s')
                                         add_to_store_targets_addr)). {
    apply/negP; move=> SOME; apply GETS in SOME.
    simpl in SOME; move/negP in NOT_SOME_aS.
    contradiction.
  }
  
  assert (INONE' : get (Symbolic.mem s') isolate_addr = None)
    by by destruct (get (Symbolic.mem s') isolate_addr).
  assert (AJNONE' : get (Symbolic.mem s') add_to_jump_targets_addr = None)
    by by destruct (get (Symbolic.mem s') add_to_jump_targets_addr).
  assert (ASNONE' : get (Symbolic.mem s') add_to_store_targets_addr = None)
    by by destruct (get (Symbolic.mem s') add_to_store_targets_addr).
  
  assert (FALSE_aJ_i : (add_to_jump_targets_addr == isolate_addr) = false)
   by by rewrite eq_sym in DIFF_i_aJ; move/Bool.negb_true_iff in DIFF_i_aJ.
  assert (FALSE_aS_i : (add_to_store_targets_addr == isolate_addr) = false)
   by by rewrite eq_sym in DIFF_i_aS; move/Bool.negb_true_iff in DIFF_i_aS.
  assert (FALSE_aS_aJ: (add_to_store_targets_addr ==
                        add_to_jump_targets_addr) = false)
   by by rewrite eq_sym in DIFF_aJ_aS; move/Bool.negb_true_iff in DIFF_aJ_aS.
   
  destruct s  as [mem  reg  pc  [next  iT  aJT  aST]],
           s' as [mem' reg' pc' [next' iT' aJT' aST']];
    simpl in *.
   
  assert (SGET_i : sget (Symbolic.State mem reg pc
                                        (Internal next iT aJT aST))
                        isolate_addr ?= 0%w@iT)
    by by rewrite /sget INONE eq_refl.
  assert (SGET_aJ : sget (Symbolic.State mem reg pc
                                         (Internal next iT aJT aST))
                         add_to_jump_targets_addr ?= 0%w@aJT)
    by by rewrite /sget AJNONE FALSE_aJ_i eq_refl.
  assert (SGET_aS : sget (Symbolic.State mem reg pc
                                         (Internal next iT aJT aST))
                         add_to_store_targets_addr ?= 0%w@aST)
    by by rewrite /sget ASNONE FALSE_aS_i FALSE_aS_aJ eq_refl.
  
  assert (SGET_i' : sget (Symbolic.State mem' reg' pc'
                                         (Internal next' iT' aJT' aST'))
                         isolate_addr ?= 0%w@iT')
    by by rewrite /sget INONE' eq_refl.
  assert (SGET_aJ' : sget (Symbolic.State mem' reg' pc'
                                           (Internal next' iT' aJT' aST'))
                          add_to_jump_targets_addr ?= 0%w@aJT')
    by by rewrite /sget AJNONE' FALSE_aJ_i eq_refl.
  assert (SGET_aS' : sget (Symbolic.State mem' reg' pc'
                                          (Internal next' iT' aJT' aST'))
                          add_to_store_targets_addr ?= 0%w@aST')
    by by rewrite /sget ASNONE' FALSE_aS_i FALSE_aS_aJ eq_refl.
  
  rewrite /good_internal /=; move => GOOD;
    destruct iT  as [|ci  Ii  Wi|];  try done;
    destruct aJT as [|caJ IaJ WaJ|]; try done;
    destruct aST as [|caS IaS WaS|]; try done.
  
  assert (def_iT' : iT' = DATA ci Ii Wi). {
    apply retag_set_not_in with (p := isolate_addr) in RETAG_SET; auto.
    rewrite SGET_i SGET_i' in RETAG_SET.
    by inversion RETAG_SET; subst.
  }
  
  assert (def_aJT' : aJT' = DATA caJ IaJ WaJ). {
    apply retag_set_not_in with (p := add_to_jump_targets_addr) in RETAG_SET;
      auto.
    rewrite SGET_aJ SGET_aJ' in RETAG_SET.
    by inversion RETAG_SET; subst.
  }

  assert (def_aST' : aST' = DATA caS IaS WaS). {
    apply retag_set_not_in with (p := add_to_store_targets_addr) in RETAG_SET;
      auto.
    rewrite SGET_aS SGET_aS' in RETAG_SET.
    by inversion RETAG_SET; subst.
  }

  assert (NEXTS : next = next')
    by by apply retag_set_preserves_next_id in RETAG_SET.
  subst iT' aJT' aST' next' next.

  move: GOOD => [NEQiaJ [NEQiaS [NEQaJaS [LTi [LTaJ [LTaS IF_GET]]]]]].
  repeat (split; [solve [eauto 2]|]).
  intros p x c I W GET'.
  
  apply retag_set_or with (p := p) in RETAG_SET; auto.
  destruct (get mem p) as [[y Ly]|] eqn:GET;
    [|by specialize GETS with p; rewrite GET GET' /= in GETS;
         destruct GETS as [_ NO]; specialize (NO erefl)].
  move: RETAG_SET => [OLD | [x' [c' [I' [W' [THEN NOW]]]]]].
  - rewrite /sget GET' GET in OLD.
    inversion OLD; subst.
    apply IF_GET in GET.
    repeat invh and; repeat split; eauto 2.
  - rewrite /sget GET  in THEN.
    rewrite /sget GET' in NOW.
    inversion THEN; subst; inversion NOW; subst.
    repeat split.
    + generalize (lew_max cnew) => /le_iff_lt_or_eq [LTmax | ?]; [|by subst].
      eapply ltb_lt,lebw_succ; eassumption.
    + by move=> ?; subst; apply lt_irrefl in LTi.
    + by move=> ?; subst; apply lt_irrefl in LTaJ.
    + by move=> ?; subst; apply lt_irrefl in LTaS.
Qed.
    
End WithClasses.

Notation memory    t := (Symbolic.memory    t sym_compartmentalization).
Notation registers t := (Symbolic.registers t sym_compartmentalization).

End Sym.