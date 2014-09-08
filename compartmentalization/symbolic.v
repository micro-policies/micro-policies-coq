Require Import List. Import ListNotations.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype finset.

Require Import lib.hlist lib.Integers lib.utils lib.ordered lib.partial_maps common.common.
Require Import symbolic.symbolic symbolic.rules.
Require Import lib.list_utils.
Require Import compartmentalization.common.
Require Import compartmentalization.isolate_sets compartmentalization.ranges.

Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Module Sym.

Inductive stag {t : machine_types} :=
| PC     : forall (F : where_from) (c : word t), stag
| DATA   : forall (c : word t) (I W : {set (word t)}), stag
| REG    : stag.

Module Exports.

Section Equality.

Context (t : machine_types).

Definition stag_eq (t1 t2 : @stag t) : bool :=
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

End Equality.

End Exports.

Import Exports.

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
  undo1 hyp xcIW; destruct xcIW as [|c I W|];
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

Definition stag_incoming (L : stag) : option {set (word t)} :=
  match L with DATA _ I _ => Some I | _ => None end.

Definition stag_writers (L : stag) : option {set (word t)} :=
  match L with DATA _ _ W => Some W | _ => None end.

Definition stags : Symbolic.tag_kind -> eqType := fun _ => [eqType of stag].

Section WithHLists.
Import Symbolic HListNotations.

Definition can_execute (Lpc LI : stag) : option (word t) :=
  do! PC   F  c   <-! Lpc;
  do! DATA c' I _ <-! LI;
  do! guard (c' == c) || ((F == JUMPED) && (c \in I));
  Some c'.

Definition compartmentalization_rvec (op : opcode)
                                     (F : where_from)
                                     (c : word t)
                                     (tr : type_of_result stags (outputs op)) : OVec stags op :=
  mkOVec (PC F c) tr.

Definition rvec_step op
                     (rv : word t -> option (OVec stags op))
                     (Lpc LI : stag)  : option (OVec stags op) :=
  do! c <- can_execute Lpc LI;
  rv c.

Definition rvec_simple op (F : where_from) (tr : type_of_result stags (outputs op)) :
                       stag -> stag -> option (OVec stags op) :=
  rvec_step op (fun c => Some (compartmentalization_rvec op F c tr)).

Definition rvec_next op (tr : type_of_result stags (outputs op)) : stag -> stag -> option (OVec stags op) :=
  rvec_simple op INTERNAL tr.
Definition rvec_jump op (tr : type_of_result stags (outputs op)) : stag -> stag -> option (OVec stags op) :=
  rvec_simple op JUMPED tr.
Definition rvec_store (c : word t) (I W : {set (word t)})
                      : stag -> stag -> option (OVec stags STORE) :=
  rvec_step STORE (fun c' =>
    do! guard (c == c') || (c' \in W);
    Some (@mkOVec stags STORE (PC INTERNAL c') (DATA c I W))).

(* The `REG's in the IVec's fields can also be _s; it's an invariant that
   registers are always tagged with `REG'. *)
Definition compartmentalization_handler (iv : IVec stags) : option (OVec stags (op iv)) :=
  match iv with
    | mkIVec NOP       Lpc LI []                     => rvec_next NOP       tt  Lpc LI
    | mkIVec CONST     Lpc LI [REG]                  => rvec_next CONST     REG Lpc LI
    | mkIVec MOV       Lpc LI [REG; REG]             => rvec_next MOV       REG Lpc LI
    | mkIVec (BINOP b) Lpc LI [REG; REG; REG]        => rvec_next (BINOP b) REG Lpc LI
    | mkIVec LOAD      Lpc LI [REG; DATA _ _ _; REG] => rvec_next LOAD      REG Lpc LI
    | mkIVec STORE     Lpc LI [REG; REG; DATA c I W] => rvec_store c I W Lpc LI
    | mkIVec JUMP      Lpc LI [REG]                  => rvec_jump JUMP      tt  Lpc LI
    | mkIVec BNZ       Lpc LI [REG]                  => rvec_next BNZ       tt  Lpc LI
    | mkIVec JAL       Lpc LI [REG; REG]             => rvec_jump JAL       REG Lpc LI
    | mkIVec SERVICE   Lpc LI  []                    => Some (@mkOVec stags SERVICE REG tt)
    | mkIVec _         _   _  _                      => None
  end.

End WithHLists.

Record compartmentalization_internal :=
  Internal { next_id                  : word t
           ; isolate_tag              : stag
           ; add_to_jump_targets_tag  : stag
           ; add_to_store_targets_tag : stag }.

Definition compartmentalization_internal_eqb : rel compartmentalization_internal :=
  [rel i1 i2 | [&& next_id i1 == next_id i2,
                   isolate_tag i1 == isolate_tag i2,
                   add_to_jump_targets_tag i1 == add_to_jump_targets_tag i2 &
                   add_to_store_targets_tag i1 == add_to_store_targets_tag i2 ] ].

Lemma compartmentalization_internal_eqbP : Equality.axiom compartmentalization_internal_eqb.
Proof.
  move => [? ? ? ?] [? ? ? ?].
  apply (iffP and4P); simpl.
  - by move => [/eqP -> /eqP -> /eqP -> /eqP ->].
  - by move => [-> -> -> ->].
Qed.

Definition compartmentalization_internal_eqMixin := EqMixin compartmentalization_internal_eqbP.
Canonical compartmentalization_internal_eqType := Eval hnf in EqType _ compartmentalization_internal_eqMixin.

Instance sym_compartmentalization : Symbolic.params := {
  ttypes := stags;

  transfer := compartmentalization_handler;

  internal_state := compartmentalization_internal_eqType
}.

Local Notation memory    := (Symbolic.memory t sym_compartmentalization).
Local Notation registers := (Symbolic.registers t sym_compartmentalization).

Hint Immediate word_map_axioms.
Hint Immediate reg_map_axioms.

Definition sget (s : Symbolic.state t) (p : word t)
                : option stag :=
  let: Symbolic.State mem _ _ si := s in
  let sctag get_tag := Some (get_tag si) in
  match get mem p with
    | Some _@tg => Some tg
    | None   =>
      if      p == isolate_addr              then sctag isolate_tag
      else if p == add_to_jump_targets_addr  then sctag add_to_jump_targets_tag
      else if p == add_to_store_targets_addr then sctag add_to_store_targets_tag
      else None
  end.
Arguments sget s p : simpl never.

Definition supd (s : Symbolic.state t) (p : word t) (tg : stag)
                : option (Symbolic.state t) :=
  let: Symbolic.State mem reg pc si := s in
  let: Internal next_id
                isolate_tag
                add_to_jump_targets_tag
                add_to_store_targets_tag :=
       si in
  let sctagged si' := Some (Symbolic.State mem reg pc si') in
  match rep mem p (fun v => (val v)@tg) with
    | Some mem' => Some (Symbolic.State mem' reg pc si)
    | None      =>
      if      p == isolate_addr
        then sctagged (Internal next_id
                                tg
                                add_to_jump_targets_tag
                                add_to_store_targets_tag)
      else if p == add_to_jump_targets_addr
        then sctagged (Internal next_id
                                isolate_tag
                                tg
                                add_to_store_targets_tag)
      else if p == add_to_store_targets_addr
        then sctagged (Internal next_id
                                isolate_tag
                                add_to_jump_targets_tag
                                tg)
      else None
  end.
Arguments supd s p tg : simpl never.

Definition fresh (si : compartmentalization_internal)
                 : option (word t * compartmentalization_internal) :=
  let 'Internal next iT ajtT asmT := si in
  if next == max_word t
  then None
  else Some (next, Internal (next+1)%w iT ajtT asmT).

Fixpoint retag_set (ok : word t -> {set (word t)} -> {set (word t)} -> bool)
                   (retag : word t -> {set (word t)} -> {set (word t)}-> stag)
                   (ps : list (word t))
                   (s : Symbolic.state t)
                   : option (Symbolic.state t) :=
  match ps with
    | []       => Some s
    | p :: ps' => do! DATA c I W <-  sget s p;
                  do! guard (ok c I W);
                  do! DATA c' I' W'  <-! retag c I W;
                  do! s'             <-  supd s p (DATA c' I' W');
                  retag_set ok retag ps' s'
  end.

Definition isolate (s : Symbolic.state t) : option (Symbolic.state t) :=
  match s with
    | Symbolic.State M R (pc @ (PC F c)) si =>
      do! LI    <- sget s pc;
      do! c_sys <- can_execute (PC F c) LI;

      do! (c',si') <- fresh si;
      let s' := Symbolic.State M R (pc @ (PC F c)) si' in

      do! pA @ _ <- get R syscall_arg1;
      do! pJ @ _ <- get R syscall_arg2;
      do! pS @ _ <- get R syscall_arg3;

      do! A' <- isolate_create_set (@val _ _) M pA;
      do! guard A' != set0;
      do! sA <- retag_set (fun c'' _ _ => c == c'')
                          (fun _   I W => DATA c' I W)
                          (enum A') s';

      do! J' : {set word t} <- isolate_create_set (@val _ _) M pJ;
      do! sJ <- retag_set (fun c'' I _ => (c == c'') || (c' == c'') || (c \in I))
                          (fun c'' I W => DATA c'' ((c' : word t) |: I) W)
                          (enum J') sA;

      do! S' : {set word t} <- isolate_create_set (@val _ _) M pS;
      do! sS <- retag_set (fun c'' _ W => (c == c'') || (c' == c'') ||
                                          (c \in W))
                          (fun c'' I W => DATA c'' I ((c' : word t) |: W))
                          (enum S') sJ;

      do! pc' @ _                    <- get  R  ra;
      do! DATA c_next I_next _ <- sget sS pc';
      do! guard c == c_next;
      do! guard c_sys \in I_next;

      let: Symbolic.State M_next R_next _ si_next := sS in
      Some (Symbolic.State M_next R_next (pc' @ (PC JUMPED c_sys)) si_next)
    | _ => None
  end.

Definition add_to_jump_targets (s : Symbolic.state t)
                               : option (Symbolic.state t) :=
  match s with
    | Symbolic.State M R (pc @ (PC F c)) si =>
      do! LI    <- sget s pc;
      do! c_sys <- can_execute (PC F c) LI;
      do! guard c != c_sys;

      do! p @ _         <- get R syscall_arg1;
      do! DATA c' I' W' <- sget s p;

      do! guard (c' == c) || (c \in I');
      do! s' <- supd s p (DATA c' (c |: I') W');

      do! pc' @ _              <- get R ra;
      do! DATA c_next I_next _ <- sget s' pc';
      do! guard c == c_next;
      do! guard c_sys \in I_next;

      let: Symbolic.State M_next R_next _ si_next := s' in
      Some (Symbolic.State M_next R_next (pc' @ (PC JUMPED c_sys)) si_next)
    | _ => None
  end.

Definition add_to_store_targets (s : Symbolic.state t)
                                : option (Symbolic.state t) :=
  match s with
    | Symbolic.State M R (pc @ (PC F c)) si =>
      do! LI    <- sget s pc;
      do! c_sys <- can_execute (PC F c) LI;
      do! guard c != c_sys;

      do! p @ _         <- get R syscall_arg1;
      do! DATA c' I' W' <- sget s p;

      do! guard (c' == c) || (c \in W');
      do! s' <- supd s p (DATA c' I' (c |: W'));

      do! pc' @ _              <- get R ra;
      do! DATA c_next I_next _ <- sget s' pc';
      do! guard c == c_next;
      do! guard c_sys \in I_next;

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
      uniq [:: iC; aJC; aST] /\
      all  (fun c => c <? next) [:: iC; aJC; aST] /\
      forall p x c I W,
        get (Symbolic.mem s) p ?= x@(DATA c I W) ->
        c <? next /\ c \notin [:: iC; aJC; aST]
    | _ , _ , _ =>
      False
  end.

Definition good_memory_tag (s : Symbolic.state t)
                           (p : word t) : bool :=
  match sget s p with
    | Some (DATA _ _ _) => true
    | Some _            => false
    | None              => true
  end.

CoInductive good_memory_tag_spec (s : Symbolic.state t)
                                 (p : word t) : option stag -> Prop :=
| GoodMemoryTagData c I W : good_memory_tag_spec s p (Some (DATA c I W))
| GoodMemoryTagNone       : good_memory_tag_spec s p None.

Lemma good_memory_tagP s p : good_memory_tag s p ->
                             good_memory_tag_spec s p (sget s p).
Proof.
  rewrite /good_memory_tag.
  by case: (sget s p) => [[|c I' W'|]|] // _; constructor.
Qed.

Definition good_register_tag (R : registers) (r : reg t) : bool :=
  match get R r with
    | Some (_ @ REG) => true
    | Some (_ @ _)   => false
    | None           => true
  end.

Definition good_pc_tag (s : Symbolic.state t)
                       (pc : atom (word t) stag) : Prop :=
  match pc with
    | _ @ (PC _ c) => exists p I W, sget s p ?= Sym.DATA c I W
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

Theorem sget_supd s s' p L :
  supd s p L ?= s' ->
  forall p',
    sget s' p' = if p' == p then Some L else sget s p'.
Proof.
  case: s => m r pc [ni it atjt atst]; case: s' => m' r' pc' [ni' it' atjt' atst'].
  rewrite /supd /= /rep /sget.
  case GET: (get m p) => [[x L']|] /=.
  - move=> {r' pc' ni'} [<- _ _ _ <- <- <-] p' /=.
    have [{p'} ->|NE] := (p' =P p); first by rewrite get_set_eq.
    by rewrite (get_set_neq _ _ NE).
  - move: GET; have [{p} ->|NE1] := (p =P _).
    { move=> GET {r' pc' ni'} [<- _ _ _ <- <- <-] p'.
      by have [{p'} ->|_] := (p' =P _); first by rewrite GET. }
    move: NE1; have [{p} ->|NE2] := (p =P _).
    { move=> NE1 GET {r' pc' ni'} [<- _ _ _ <- <- <-] p'.
      by have [{p'} ->|_] := (p' =P add_to_jump_targets_addr); first by rewrite GET (introF (_ =P _) NE1). }
    move: NE2; have [{p} ->|NE3] := (p =P _) => //.
    move => NE2 NE1 GET [<- _ _ _ <- <- <-] p'.
    by have [{p'} ->|_] := (p' =P add_to_store_targets_addr);
    first by rewrite GET (introF (_ =P _) NE1) (introF (_ =P _) NE2).
Qed.

Theorem sget_supd_eq s s' p L :
  supd s  p L ?= s'  ->
  sget s' p   ?= L.
Proof.
  move=> /sget_supd ->.
  by rewrite eqxx.
Qed.

Theorem sget_supd_neq s s' p p' v :
  p' <> p ->
  supd s p v ?= s' ->
  sget s' p' = sget s p'.
Proof.
  move=> /(introF (_ =P _)) NE /sget_supd ->.
  by rewrite NE.
Qed.

Theorem get_supd_eq s s' p x L L' :
  get (Symbolic.mem s) p ?= x@L ->
  supd s p L' ?= s' ->
  get (Symbolic.mem s') p ?= x@L'.
Proof.
  case: s => m r pc [ni it atjt atst]; case: s' => m' r' pc' [ni' it' atjt' atst'] /=.
  rewrite /supd /rep => -> /= [<- _ _ _ _ _ _].
  by rewrite get_set_eq.
Qed.

Theorem get_supd_neq s s' p p' v :
  p' <> p ->
  supd s p v ?= s' ->
  get (Symbolic.mem s') p' = get (Symbolic.mem s) p'.
Proof.
  case: s => m r pc [ni it atjt atst]; case: s' => m' r' pc' [ni' it' atjt' atst'] NE /=.
  rewrite /supd.
  case REP: (rep _ _ _) => [m''|].
  - move=> [<- _ _ _ _ _ _].
    by rewrite (get_rep REP) (introF (_ =P _) NE).
  - repeat case: (p =P _) => _ //=; congruence.
Qed.

Theorem get_supd_none s s' p p' v :
  get (Symbolic.mem s) p = None ->
  supd s p' v ?= s' ->
  get (Symbolic.mem s') p = None.
Proof.
  case: s => m r pc [ni it atjt atst]; case: s' => m' r' pc' [ni' it' atjt' atst'] /= NONE.
  rewrite /supd.
  case REP: (rep _ _ _) => [m''|].
  - move=> [<- _ _ _ _ _ _].
    rewrite (get_rep REP) NONE.
    move: REP. rewrite /rep.
    have [{p'} <-|//] := (p =P p').
    by rewrite NONE.
  - repeat case: (p' =P _) => _; congruence.
Qed.

Theorem supd_same_val s p L s' :
  supd s p L ?= s' ->
  omap (fun x => val x) \o get (Symbolic.mem s) =1
  omap (fun x => val x) \o get (Symbolic.mem s').
Proof.
  case: s => m r pc [ni it atjt atst]; case: s' => m' r' pc' [ni' it' atjt' atst'] /=.
  rewrite /supd.
  case REP: (rep m p _) => [m''|].
  - move=> [<- _ _ _ _ _ _] p' /=.
    rewrite (get_rep REP).
    have [->|_] := (p' =P p) => //.
    by case: (get m p) => [[? ?]|].
  - repeat case: (p =P _) => _; congruence.
Qed.

Theorem supd_preserves_regs : forall s p v s',
  supd s p v ?= s' ->
  Symbolic.regs s = Symbolic.regs s'.
Proof.
  move=> [mem reg pc [next iT aJT aST]] /= p v s' SUPD;
    rewrite /supd /= in SUPD.
  move: SUPD.
  case: (rep mem p _) => [m'' [<-] //|].
  by repeat case: (p =P _) => _ //; move=> [<-].
Qed.

Theorem supd_preserves_pc : forall s p v s',
  supd s p v ?= s' ->
  Symbolic.pc s = Symbolic.pc s'.
Proof.
  move=> [mem reg pc [next iT aJT aST]] /= p v s' SUPD;
    rewrite /supd /= in SUPD.
  move: SUPD.
  case: (rep mem p _) => [m'' [<-] //|].
  by repeat case: (p =P _) => _ //; move=> [<-].
Qed.

Theorem supd_preserves_next_id : forall s p v s',
  supd s p v ?= s' ->
  next_id (Symbolic.internal s) = next_id (Symbolic.internal s').
Proof.
Proof.
  move=> [mem reg pc [next iT aJT aST]] /= p v s' SUPD;
    rewrite /supd /= in SUPD.
  move: SUPD.
  case: (rep mem p _) => [m'' [<-] //|].
  by repeat case: (p =P _) => _ //; move=> [<-].
Qed.

Lemma succ_trans : forall x y,
  y <> max_word t -> x <? y -> x <? (y + 1)%w.
Proof.
  move=> x y NEQ /ltb_lt LT.
  apply/ltb_lt.
  generalize (lew_max y) => /le_iff_lt_or_eq [] // LT_max.
  apply lt_trans with (b := y); first by [].
  apply ltb_lt.
  by apply (@lebw_succ _ y (max_word t)).
Qed.
Hint Resolve succ_trans.

Lemma sget_lt_next : forall s p c I W,
  good_internal s ->
  sget s p ?= DATA c I W ->
  c <? next_id (Symbolic.internal s).
Proof.
  clear I; move=> [mem reg pc [next Li LaJ LaS]] /= p c I W GOOD SGET.
  rewrite /good_internal /= in GOOD;
    destruct Li  as [|ci  Ii  Wi|];  try done;
    destruct LaJ as [|caJ IaJ WaJ|]; try done;
    destruct LaS as [|caS IaS WaS|]; try done.
  case: GOOD => NEQ [/and4P [? ? ? ?] GOOD].
  rewrite /sget in SGET.
  destruct (get mem p) as [[? ?]|] eqn:GET; rewrite GET in SGET.
  - move: SGET => [SGET]. rewrite SGET in GET; eapply GOOD; eassumption.
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
  destruct (next == max_word t) eqn:EQ;
    [discriminate | simpl in FRESH; move/eqP in EQ].
  inversion FRESH; subst; clear FRESH.
  rewrite /good_internal /=.
  destruct iT  as [|ci Ii Wi|],
           aJT as [|caJ IaJ WaJ|],
           aST as [|caS IaS WaS|];
    auto.
  move=> [NEQ [/and4P [? ? ? _] GOOD]].
    do 2 (split; eauto 2).
    by apply/and4P; split; eauto 2.
  intros p x c I W GET; specialize (GOOD p x c I W GET).
  case: GOOD => *.
  by split; eauto 2.
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
  uniq ps ->
  retag_set ok retag ps s ?= s' ->
  forall p,
    p \in ps ->
    exists c I W, sget s p ?= DATA c I W /\ ok c I W.
Proof.
  clear I; move=> ok retag ps; move: ok retag; induction ps as [|p ps];
    move=> //= ok retag s s'' NODUP RETAG_SET p' IN.
  let I := fresh "I"
  in undoDATA RETAG_SET x c I W;
     undo1    RETAG_SET OK;
     destruct (retag c I W) as [|c' I' W'|] eqn:RETAG; simpl in *; try done;
     undo1    RETAG_SET s'.
  rewrite in_cons in IN.
  case/orP: IN => [/eqP ? | IN]; [subst p'|].
  - by rewrite def_xcIW; repeat eexists.
  - case/andP: NODUP => NIN NODUP.
    have [?|NEQ] := (p' =P p); first by subst p'; rewrite IN in NIN.
    apply IHps with (p := p') in RETAG_SET; auto.
    move: RETAG_SET => [c'' [I'' [W'' [SGET'' OK'']]]].
    eapply sget_supd_neq in def_s'; [|eassumption].
    by rewrite -def_s' SGET''; repeat eexists.
Qed.

Lemma retag_set_not_in : forall ok retag ps s s',
  retag_set ok retag ps s ?= s' ->
  forall p,
    p \notin ps ->
    sget s p = sget s' p.
Proof.
  clear I; intros ok retag ps; induction ps as [|p ps]; simpl;
    intros s s' RETAG p' NIN.
  - by inversion RETAG; subst.
  - let I := fresh "I"
    in undoDATA RETAG x c I W; undo1 RETAG OK;
       destruct (retag c I W) as [|c' I' W'|] eqn:TAG; try discriminate;
       undo1 RETAG s''.
    case/norP: NIN => NEQ NIN.
    apply IHps with (p := p') in RETAG; auto.
    apply sget_supd_neq with (p' := p') in def_s'';
      first by rewrite -RETAG def_s''.
    exact: (elimNTF eqP NEQ).
Qed.

Lemma retag_set_in_ok : forall ok retag ps s s',
  uniq ps ->
  retag_set ok retag ps s ?= s' ->
  forall p,
    p \in ps ->
    exists c I W, sget s  p ?= DATA c I W /\
                  ok c I W /\
                  sget s' p ?= retag c I W.
Proof.
  clear I; intros ok retag ps; induction ps as [|p ps]; simpl;
    intros s s' NODUP RETAG p' IN.
  - inversion IN.
  - let I := fresh "I"
    in undoDATA RETAG x c I W; undo1 RETAG OK;
       destruct (retag c I W) as [|c' I' W'|] eqn:TAG; try discriminate;
       undo1 RETAG s''.
    case/andP: NODUP => NIN NODUP.
    apply retag_set_not_in with (ok := ok) (retag := retag)
                                (s := s'') (s' := s')
      in NIN; [|assumption].
    case/orP: IN => [/eqP ? | IN]; subst.
    + exists c,I,W.
      split; auto.
      eapply sget_supd_eq in def_s''; eauto.
      by rewrite -NIN def_s'' TAG.
    + destruct (p == p') eqn:EQ; move/eqP in EQ; subst.
      * exists c,I,W.
        repeat (split; auto).
        eapply sget_supd_eq in def_s''; eauto.
        by rewrite -NIN def_s'' TAG.
      * apply IHps with (p := p') in RETAG; auto.
        destruct RETAG as [ci [Ii [Wi [GET1 GET2]]]].
        exists ci,Ii,Wi; split; auto.
        apply sget_supd_neq with (p' := p') in def_s''; auto.
        by rewrite -def_s''.
Qed.

Lemma retag_set_in : forall ok retag ps s s',
  uniq ps ->
  retag_set ok retag ps s ?= s' ->
  forall p,
    p \in ps ->
    exists c I W, sget s  p ?= DATA c I W /\
                  sget s' p ?= retag c I W.
Proof.
  intros until 0; intros NODUP RETAG p IN.
  eapply retag_set_in_ok in RETAG; eauto.
  repeat invh ex; repeat invh and; repeat eexists; eassumption.
Qed.

Lemma retag_set_or_ok : forall ok retag ps s s',
  uniq ps ->
  (forall p, good_memory_tag s p) ->
  retag_set ok retag ps s ?= s' ->
  forall p,
    sget s p = sget s' p \/
    exists c I W, sget s p ?= DATA c I W /\
                  ok c I W /\
                  sget s' p ?= retag c I W.
Proof.
  intros ok retag ps s s' NODUP GMEM RETAG p.
  have [IN | NIN] := boolP (p \in ps).
  - by eapply retag_set_in_ok in RETAG; eauto.
  - by eapply retag_set_not_in in RETAG; eauto.
Qed.

Lemma retag_set_or : forall ok retag ps s s',
  uniq ps ->
  (forall p, good_memory_tag s p) ->
  retag_set ok retag ps s ?= s' ->
  forall p,
    sget s p = sget s' p \/
    exists c I W, sget s p ?= DATA c I W /\ sget s' p ?= retag c I W.
Proof.
  intros ok retag ps s s' NODUP GMEM RETAG p.
  have [IN | NIN] := boolP (p \in ps).
  - by eapply retag_set_in in RETAG; eauto.
  - by eapply retag_set_not_in in RETAG; eauto.
Qed.

(*Lemma sget_eq__get_eq : forall s s' p,
  (is_some (get (Symbolic.mem s) p) <-> is_some (get (Symbolic.mem s') p)) ->
  sget s p = sget s' p ->
  get (Symbolic.mem s) p = get (Symbolic.mem s') p.
Proof.
  intros [mem reg pc [next iT aJT aST]] [mem' reg' pc' [next' iT' aJT' aST']]
         p GETS SGETS; simpl in *.
  rewrite /sget /= in SGETS.
  destruct (get mem p) as [[? ?]|],(get mem' p) as [[? ?]|]; simpl in *; try discriminate.
     try (destruct GETS;
          match goal with H : is_true true -> is_true false |- _ =>
            specialize (H erefl)
          end).
Qed.
*)

Lemma retag_set_same_val ok retag ps s s' :
  retag_set ok retag ps s ?= s' ->
  omap (fun x => val x) \o get (Symbolic.mem s) =1
  omap (fun x => val x) \o get (Symbolic.mem s').
Proof.
  clear I.
  elim: ps s s' => [|p ps IH] s s' /=; first by move=> [->].
  case: (sget s p) => //; move=> [|c I W|] //=.
  case: (ok c I W) => //.
  case: (retag c I W) => // c' I' W'.
  case UPD: (supd _ _ _) => [s''|] //= RETAG p'.
  rewrite (supd_same_val _ _ _ _ UPD).
  exact: (IH _ _ RETAG).
Qed.

Lemma retag_set_or_ok_get : forall ok retag ps s s',
  uniq ps ->
  (forall p, good_memory_tag s p) ->
  retag_set ok retag ps s ?= s' ->
  forall p,
    get (Symbolic.mem s) p = get (Symbolic.mem s') p \/
    exists x c I W, get (Symbolic.mem s) p ?= x@(DATA c I W) /\
                    ok c I W /\
                    get (Symbolic.mem s') p ?= x@(retag c I W).
Proof.
  clear I; intros ok retag ps s s' NODUP GMEM RETAG p.
  move: (retag_set_same_val _ _ _ _ _ RETAG p) => /= GET.
  generalize (retag_set_or_ok ok retag ps s s' NODUP GMEM RETAG p)
             => [[EQ | [c [I [W [OLD [OK NEW]]]]]]].
  - move: EQ GET {RETAG GMEM NODUP}.
    rewrite /sget.
    case: s => m ? ? [? ? ? ?]; case: s' => m' ? ? [? ? ? ?] /=.
    case: (get m p)  => [[v l]|];
    case: (get m' p) => [[v' l']|] //=; last by auto.
    by move=> [<-] [<-]; left.
  - move: GET OLD OK NEW {RETAG GMEM}.
    rewrite /sget.
    case: s => m ? ? [? ? ? ?]; case: s' => m' ? ? [? ? ? ?] /=.
    case: (get m p)  => [[v l]|];
    case: (get m' p) => [[v' l']|] //=; last by auto.
    move=> [->] [->] OK [->].
    right.
    eexists v', c, I, W.
    by auto.
Qed.

Lemma retag_set_preserves_good_memory_tag : forall ok retag ps s s',
  (forall c I W,
     match retag c I W with
       | DATA _ I' W' => true
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
    intros MEM.
    unfold good_memory_tag in *.
    eapply IHps; try eassumption.
    intros p'; destruct (p == p') eqn:EQ_p_p'; move/eqP in EQ_p_p'.
    + subst p'.
      by eapply sget_supd_eq in def_s2; eauto 1; rewrite def_s2.
    + apply sget_supd_neq with (p' := p') in def_s2; auto.
      rewrite def_s2; specialize MEM with p'.
      by destruct (sget s p') as [[|c'' I'' W''|]|].
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
       | Some (DATA c _ _) , Some (DATA c' _ _) => c = c'
       | None              , None               => True
       | _                 , _                  => False
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
                 isolate_addr ?= iT).
    by by rewrite /sget INONE eq_refl.
  assert (SGET_aJ :
            sget (Symbolic.State mem reg pc (Internal next iT aJT aST))
                 add_to_jump_targets_addr ?= aJT)
    by by rewrite /sget AJNONE FALSE_aJ_I eq_refl.
  assert (SGET_aS :
            sget (Symbolic.State mem reg pc (Internal next iT aJT aST))
                 add_to_store_targets_addr ?= aST)
    by by rewrite /sget ASNONE FALSE_aS_I FALSE_aS_aJ eq_refl.

  assert (SGET_I' :
            sget (Symbolic.State mem' reg' pc' (Internal next iT' aJT' aST'))
                 isolate_addr ?= iT')
    by by rewrite /sget INONE' eq_refl.
  assert (SGET_aJ' :
            sget (Symbolic.State mem' reg' pc' (Internal next iT' aJT' aST'))
                 add_to_jump_targets_addr ?= aJT')
    by by rewrite /sget AJNONE' FALSE_aJ_I eq_refl.
  assert (SGET_aS' :
            sget (Symbolic.State mem' reg' pc' (Internal next iT' aJT' aST'))
                 add_to_store_targets_addr ?= aST')
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
  destruct (get mem p) as [[y [|cy Iy Wy|]]|] eqn:GET;
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
  cnew <> max_word t ->
  next_id (Symbolic.internal s) = (cnew+1)%w ->
  ~~ is_some (get (Symbolic.mem s) isolate_addr) ->
  ~~ is_some (get (Symbolic.mem s) add_to_jump_targets_addr) ->
  ~~ is_some (get (Symbolic.mem s) add_to_store_targets_addr) ->
  isolate_addr != add_to_jump_targets_addr ->
  isolate_addr != add_to_store_targets_addr ->
  add_to_jump_targets_addr != add_to_store_targets_addr ->
  isolate_addr \notin ps ->
  add_to_jump_targets_addr \notin ps ->
  add_to_store_targets_addr \notin ps ->
  uniq ps ->
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
                        isolate_addr ?= iT)
    by by rewrite /sget INONE eq_refl.
  assert (SGET_aJ : sget (Symbolic.State mem reg pc
                                         (Internal next iT aJT aST))
                         add_to_jump_targets_addr ?= aJT)
    by by rewrite /sget AJNONE FALSE_aJ_i eq_refl.
  assert (SGET_aS : sget (Symbolic.State mem reg pc
                                         (Internal next iT aJT aST))
                         add_to_store_targets_addr ?= aST)
    by by rewrite /sget ASNONE FALSE_aS_i FALSE_aS_aJ eq_refl.

  assert (SGET_i' : sget (Symbolic.State mem' reg' pc'
                                         (Internal next' iT' aJT' aST'))
                         isolate_addr ?= iT')
    by by rewrite /sget INONE' eq_refl.
  assert (SGET_aJ' : sget (Symbolic.State mem' reg' pc'
                                           (Internal next' iT' aJT' aST'))
                          add_to_jump_targets_addr ?= aJT')
    by by rewrite /sget AJNONE' FALSE_aJ_i eq_refl.
  assert (SGET_aS' : sget (Symbolic.State mem' reg' pc'
                                          (Internal next' iT' aJT' aST'))
                          add_to_store_targets_addr ?= aST')
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

  move: GOOD => [NEQ [LT IF_GET]].
  split; first solve [eauto 2].
  split; first by case/and4P: LT => *; apply/and4P; split; eauto 2.
  intros p x c I W GET'.

  apply retag_set_or with (p := p) in RETAG_SET; auto.
  destruct (get mem p) as [[y Ly]|] eqn:GET;
    [|by specialize GETS with p; rewrite GET GET' /= in GETS;
         destruct GETS as [_ NO]; specialize (NO erefl)].
  move: RETAG_SET => [OLD | [c' [I' [W' [THEN NOW]]]]].
  - rewrite /sget GET' GET in OLD.
    inversion OLD; subst.
    apply IF_GET in GET.
    repeat invh and; repeat split; eauto 2.
  - rewrite /sget GET  in THEN.
    rewrite /sget GET' in NOW.
    inversion THEN; subst; inversion NOW; subst.
    repeat split.
    + generalize (lew_max cnew) => /le_iff_lt_or_eq [LTmax | ?]; [|by subst].
      eapply lebw_succ; eassumption.
    + apply/negP.
      by case/or4P => // [/eqP ?|/eqP ?|/eqP ?]; subst cnew;
      rewrite ltb_irrefl /= ?andbF in LT.
Qed.

End WithClasses.

Notation memory    t := (Symbolic.memory    t (@sym_compartmentalization t)).
Notation registers t := (Symbolic.registers t (@sym_compartmentalization t)).

End Sym.

Export Sym.Exports.
