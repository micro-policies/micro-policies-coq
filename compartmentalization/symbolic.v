Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype finset.

Require Import word partmap.

Require Import lib.utils common.common.
Require Import symbolic.symbolic.
Require Import compartmentalization.common.
Require Import compartmentalization.isolate_sets compartmentalization.ranges.

Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Module Sym.

Inductive pc_tag (t : machine_types) :=
| PC (F : where_from) (c : mword t).
Arguments PC [t] F c.

Inductive data_tag (t : machine_types) :=
| DATA (c : mword t) (I W : {set mword t}).
Arguments DATA [t] c I W.

Module Exports.

Section Equality.

Context (t : machine_types).

Definition pc_tag_eq (t1 t2 : pc_tag t) : bool :=
  match t1, t2 with
  | PC F1 c1, PC F2 c2 => (F1 == F2) && (c1 == c2)
  end.

Lemma pc_tag_eqP : Equality.axiom pc_tag_eq.
Proof.
  move=> [F1 c1] [F2 c2] /=.
  apply/(iffP idP) => [/andP [/eqP -> /eqP ->]|[-> ->]] //.
  by rewrite !eqxx.
Qed.

Definition pc_tag_eqMixin := EqMixin pc_tag_eqP.
Canonical pc_tag_eqType := Eval hnf in EqType _ pc_tag_eqMixin.

Definition data_tag_eq (t1 t2 : data_tag t) : bool :=
  match t1, t2 with
  | DATA c1 I1 W1, DATA c2 I2 W2 =>
    [&& c1 == c2, I1 == I2 & W1 == W2]
  end.

Lemma data_tag_eqP : Equality.axiom data_tag_eq.
Proof.
  move=> [? ? ?] [? ? ?] /=.
  apply/(iffP idP) => [/and3P [/eqP -> /eqP -> /eqP ->]|[-> -> ->]] //.
  by rewrite !eqxx.
Qed.

Definition data_tag_eqMixin := EqMixin data_tag_eqP.
Canonical data_tag_eqType := Eval hnf in EqType _ data_tag_eqMixin.

End Equality.

End Exports.

Import Exports.

Module EnhancedDo.
Export DoNotation.

Notation REG := tt.

Notation "'do!' ( X , Y ) <- A ; B" :=
  (obind (fun XY => let '(X,Y) := XY in B) A)
  (at level 200, X ident, Y ident, A at level 100, B at level 200).

Notation "'do!' X @ L <- A ; B" :=
  (obind (fun XL => let '(X @ L) := XL in B) A)
  (at level 200, X ident, L ident, A at level 100, B at level 200).

Notation "'do!' X @ 'PC' F c <- A ; B" :=
  (obind (fun XFc => match XFc with X @ (PC F c) => B | _ => None end) A)
  (at level 200, X ident, F ident, c ident, A at level 100, B at level 200).

Notation "'do!' X @ 'DATA' c' I' W' <- A ; B" :=
  (obind (fun XcIW => match XcIW with X @ (DATA c' I' W') => B | _ => None end) A)
  (at level 200, X ident, c' ident, I' ident, W' ident,
   A at level 100, B at level 200).

Notation "'do!' X @ 'REG' <- A ; B" :=
  (obind (fun XREG => match XREG with X @ REG => B | _ => None end) A)
  (at level 200, X ident, A at level 100, B at level 200).

Notation "'do!' 'PC' F c <- A ; B" :=
  (obind (fun Fc => match Fc with PC F c => B end) A)
  (at level 200, F ident, c ident, A at level 100, B at level 200).

Notation "'do!' 'DATA' c' I' W' <- A ; B" :=
  (obind (fun cIW => match cIW with DATA c' I' W' => B end) A)
  (at level 200, c' ident, I' ident, W' ident, A at level 100, B at level 200).

Notation "'do!' 'REG' <- A ; B" :=
  (obind (fun maybeREG => match maybeREG with REG => B end) A)
  (at level 200, A at level 100, B at level 200).

Ltac undo1 hyp var :=
  let def_var := fresh "def_" var in
  match type of hyp with
    | (do! _ <- ?GET; _) ?= _ =>
      destruct GET as [var|] eqn:def_var
    | (if ?COND then _ else _) ?= _ =>
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
  undo1 hyp xcIW; destruct xcIW as [c I W]; simpl in hyp.
End EnhancedDo.

Section WithClasses.

Import EnhancedDo.

Context {t            : machine_types}
        {ops          : machine_ops t}
        {spec         : machine_ops_spec ops}
        {scr          : @syscall_regs t}
        {cmp_syscalls : compartmentalization_syscall_addrs t}.

(* I want to use I as a variable. *)
Local Notation II := Logic.I.

Notation pc_tag := (pc_tag t).
Notation data_tag := (data_tag t).

Definition pc_tag_compartment (L : pc_tag) : mword t :=
  match L with PC _ c => c end.

Definition data_tag_compartment (L : data_tag) : mword t :=
  match L with DATA c _ _ => c end.

Definition pc_tag_source (L : pc_tag) : where_from :=
  match L with PC F _ => F end.

Definition data_tag_incoming (L : data_tag) : {set mword t} :=
  match L with DATA _ In _ => In end.

Definition data_tag_writers (L : data_tag) : {set mword t} :=
  match L with DATA _ _ W => W end.

Definition stags (tk : Symbolic.tag_kind) : eqType :=
  match tk with
  | Symbolic.R => [eqType of unit]
  | Symbolic.M => [eqType of data_tag]
  | Symbolic.P => [eqType of pc_tag]
  end.

Import Symbolic.

Definition can_execute (Lpc : pc_tag) (LI : data_tag) : option (mword t) :=
  do! guard (data_tag_compartment LI == pc_tag_compartment Lpc) ||
            ((pc_tag_source Lpc == JUMPED) &&
             (pc_tag_compartment Lpc \in data_tag_incoming LI));
  Some (data_tag_compartment LI).

Definition compartmentalization_rvec (op : opcode)
                                     (F : where_from)
                                     (c : mword t)
                                     (tr : type_of_result stags (outputs op)) : OVec stags op :=
  mkOVec (PC F c) tr.

Definition rvec_step op
                     (rv : mword t -> option (OVec stags op))
                     (Lpc : pc_tag) (LI : data_tag)  : option (OVec stags op) :=
  do! c <- can_execute Lpc LI;
  rv c.

Definition rvec_simple op (F : where_from) (tr : type_of_result stags (outputs op)) :
                       pc_tag -> data_tag -> option (OVec stags op) :=
  rvec_step op (fun c => Some (compartmentalization_rvec op F c tr)).

Definition rvec_next op (tr : type_of_result stags (outputs op)) : pc_tag -> data_tag -> option (OVec stags op) :=
  rvec_simple op INTERNAL tr.
Definition rvec_jump op (tr : type_of_result stags (outputs op)) : pc_tag -> data_tag -> option (OVec stags op) :=
  rvec_simple op JUMPED tr.
Definition rvec_store (c : mword t) (I W : {set mword t})
                      : pc_tag -> data_tag -> option (OVec stags STORE) :=
  rvec_step STORE (fun c' =>
    do! guard (c == c') || (c' \in W);
    Some (@mkOVec stags STORE (PC INTERNAL c') (DATA c I W))).

(* The `REG's in the IVec's fields can also be _s; it's an invariant that
   registers are always tagged with `REG'. *)
Definition compartmentalization_handler (iv : IVec stags) : option (VOVec stags (op iv)) :=
  match iv with
    | mkIVec (OP NOP)       Lpc LI [hl]                       => rvec_next NOP       tt  Lpc LI
    | mkIVec (OP CONST)     Lpc LI [hl REG]                   => rvec_next CONST     REG Lpc LI
    | mkIVec (OP MOV)       Lpc LI [hl REG; REG]              => rvec_next MOV       REG Lpc LI
    | mkIVec (OP (BINOP b)) Lpc LI [hl REG; REG; REG]         => rvec_next (BINOP b) REG Lpc LI
    | mkIVec (OP LOAD)      Lpc LI [hl REG; DATA _ _ _; REG]  => rvec_next LOAD      REG Lpc LI
    | mkIVec (OP STORE)     Lpc LI [hl REG; REG; DATA c In W] => rvec_store c In W Lpc LI
    | mkIVec (OP JUMP)      Lpc LI [hl REG]                   => rvec_jump JUMP      tt  Lpc LI
    | mkIVec (OP BNZ)       Lpc LI [hl REG]                   => rvec_next BNZ       tt  Lpc LI
    | mkIVec (OP JAL)       Lpc LI [hl REG; REG]              => rvec_jump JAL       REG Lpc LI
    | mkIVec SERVICE        Lpc LI [hl]                       => Some tt
    | mkIVec _         _   _  _                               => None
  end.

Record compartmentalization_internal :=
  Internal { next_id                  : word t
           ; isolate_tag              : data_tag
           ; add_to_jump_targets_tag  : data_tag
           ; add_to_store_targets_tag : data_tag }.

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
                : option data_tag :=
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

Definition supd (s : Symbolic.state t) (p : word t) (tg : data_tag)
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

Definition fresh' (si : compartmentalization_internal)
                  : option (word t) :=
  if next_id si == max_word t
  then None
  else Some (next_id si).

Definition bump_next_id (si : compartmentalization_internal)
                        : compartmentalization_internal :=
  Internal (next_id si + 1)%w
           (isolate_tag si)
           (add_to_jump_targets_tag si)
           (add_to_store_targets_tag si).

Definition retag_one (ok : word t -> word t -> {set word t} -> {set word t} -> bool)
                     (retag : word t -> word t -> {set word t} -> {set word t} -> data_tag)
                     (s : Symbolic.state t)
                     (p : word t)
                     : option (Symbolic.state t) :=
  do!  DATA c I W <- sget s p;
  do!  guard (ok p c I W);
  supd s p (retag p c I W).

Fixpoint ofoldl {T S} (f : S -> T -> option S) (s : S) (ts : seq T) : option S :=
  match ts with
  | [::] => Some s
  | t :: ts => obind (ofoldl f ^~ ts) (f s t)
  end.

Lemma ofoldl_preserve T S (R : S -> S -> Prop) (f : S -> T -> option S) ts :
  (forall s, R s s) ->
  (forall s s' s'', R s s' -> R s' s'' -> R s s'') ->
  (forall s t s', f s t = Some s' -> R s s') ->
  forall s s', ofoldl f s ts = Some s' ->
               R s s'.
Proof.
  move=> Hrefl Htrans Hstep s s'.
  elim: ts s => /= [ ? [->] //|t' ts IH /=] s.
  case Hf: (f s t') => [s''|] //= /IH.
  by apply Htrans; eauto.
Qed.

Definition retag_set (ok : word t -> word t -> {set (word t)} -> {set (word t)} -> bool)
                     (retag : word t -> word t -> {set (word t)} -> {set (word t)}-> data_tag)
                     (ps : list (word t))
                     (s : Symbolic.state t)
                     : option (Symbolic.state t) :=
  ofoldl (retag_one ok retag) s ps.

Definition do_ok (cur : word t)
                 (A J S : {set word t})
                 (p : word t)
                 (cid : word t) (I W : {set word t})
                 : bool :=
  [&& (p \in A) ==> (cid == cur),
      (p \in J) ==> (cid == cur) || (cur \in I) &
      (p \in S) ==> (cid == cur) || (cur \in W) ].

Definition do_retag (cur new : word t)
                    (A J S : {set word t})
                    (p : word t)
                    (cid : word t) (I W : {set word t})
                    : data_tag :=
  let cid' := if p \in A then new      else cid in
  let I'   := if p \in J then new |: I else I   in
  let W'   := if p \in S then new |: W else W   in
  DATA cid' I' W'.

Definition isolate (s : Symbolic.state t) : option (Symbolic.state t) :=
  match s with
  | Symbolic.State M R (pc @ (PC F c)) si =>
    do! LI    <- sget s pc;
    do! c_sys <- can_execute (PC F c) LI;

    do! c'    <- fresh' si;

    do! pA @ _ <- get R syscall_arg1;
    do! pJ @ _ <- get R syscall_arg2;
    do! pS @ _ <- get R syscall_arg3;

    do! A' <- isolate_create_set (@val _ _) M pA;
    do! guard A' != set0;
    do! J' : {set word t} <- isolate_create_set (@val _ _) M pJ;
    do! S' : {set word t} <- isolate_create_set (@val _ _) M pS;

    do! s' <- retag_set (do_ok c A' J' S')
                        (do_retag c c' A' J' S')
                        (enum (A' :|: J' :|: S')) s;

    do! pc' @ _              <- get  R  ra;
    do! DATA c_next I_next _ <- sget s' pc';
    do! guard c == c_next;
    do! guard c_sys \in I_next;

    let: Symbolic.State M' R' _ si' := s' in
    Some (Symbolic.State M' R' (pc' @ (PC JUMPED c_sys)) (bump_next_id si'))
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
  end.

Definition syscalls : list (Symbolic.syscall t) :=
  let dummy := DATA Word.zero set0 set0 in
  [:: Symbolic.Syscall isolate_addr              dummy isolate;
      Symbolic.Syscall add_to_jump_targets_addr  dummy add_to_jump_targets;
      Symbolic.Syscall add_to_store_targets_addr dummy add_to_store_targets].

Definition step := Symbolic.step syscalls.

Definition bounded_by (s : Symbolic.state t) id : Prop :=
  forall p cid I W,
    sget s p = Some (DATA cid I W) ->
    forall cid',
      cid' \in cid |: I :|: W ->
      cid' <? id.

Definition isolated_syscalls (s : Symbolic.state t) : Prop :=
  forall p sc_addr,
    sc_addr \in syscall_addrs ->
    omap data_tag_compartment (sget s p) =
    omap data_tag_compartment (sget s sc_addr) ->
    p = sc_addr.

Definition good_internal (s : Symbolic.state t) : Prop :=
  bounded_by s (next_id (Symbolic.internal s)) /\ isolated_syscalls s.

Definition good_pc_tag (s : Symbolic.state t)
                       (pc : atom (word t) pc_tag) : Prop :=
  match pc with
    | _ @ (PC _ c) => exists p I W, sget s p ?= Sym.DATA c I W
  end.

Definition good_tags (s : Symbolic.state t) : Prop :=
  let: Symbolic.State M R pc si := s in
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

Theorem sget_supd_inv s s' p p' L :
  supd s p L ?= s' ->
  sget s' p' ->
  sget s  p'.
Proof.
  case: s => m r pc [ni it atjt atst]; case: s' => m' r' pc' [ni' it' atjt' atst'].
  rewrite /supd /= /rep /sget.
  case GET: (get m p) => [[v tg]|] /=.
  - move=> [<- _ _ _ <- <- <-].
    have [{p'} ->|NE] := (p' =P p); first by rewrite GET.
    by rewrite (get_set_neq _ _ NE).
  - do !case: (p =P _) => ? //; subst.
    + move=> [<- _ _ _ <- <- <-].
      case: (get m p') => //.
      by do !case: (p' =P _).
    + move=> [<- _ _ _ <- <- <-].
      case: (get m p') => //.
      by do !case: (p' =P _).
    + move=> [<- _ _ _ <- <- <-].
      case: (get m p') => //.
      by do !case: (p' =P _).
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

Lemma sget_lt_next s p c I W :
  good_internal s ->
  sget s p ?= DATA c I W ->
  c <? next_id (Symbolic.internal s).
Proof.
  move=> [Hbounds Hisolated] /Hbounds/(_ c).
  by rewrite in_setU in_setU1 eqxx /= => /(_ erefl).
Qed.

Lemma sget_lt_next_I s p c I W c' :
  good_internal s ->
  sget s p ?= DATA c I W ->
  c' \in I ->
  c' <? next_id (Symbolic.internal s).
Proof.
  move=> [Hbounds Hisolated] /Hbounds/(_ c') H c'_in_I.
  apply: H.
  by rewrite !in_setU c'_in_I orbT.
Qed.

Lemma sget_lt_next_W s p c I W c' :
  good_internal s ->
  sget s p ?= DATA c I W ->
  c' \in W ->
  c' <? next_id (Symbolic.internal s).
Proof.
  move=> [Hbounds Hisolated] /Hbounds/(_ c') H c'_in_W.
  apply: H.
  by rewrite !in_setU c'_in_W orbT.
Qed.

Lemma retag_one_preserves_definedness ok retag s p s' :
  retag_one ok retag s p ?= s' ->
  forall p', sget s p' = sget s' p' :> bool.
Proof.
  rewrite /retag_one.
  case GET: (sget _ _) => [[cid I W]|] //=.
  case: (ok _ _ _ _) => //=.
  case: (retag _ _ _ _) => [cid' I' W'] //= UPD p'.
  rewrite (sget_supd _ _ _ _ UPD).
  by have [{p'} ->|//] := (p' =P p); rewrite GET.
Qed.

Lemma retag_set_preserves_definedness ok retag ps s s' :
  retag_set ok retag ps s ?= s' ->
  forall p, sget s p = sget s' p :> bool.
Proof.
  move=> H.
  have := (ofoldl_preserve _ _ _ _ _ _ _ (retag_one_preserves_definedness ok retag) _ _ H).
  by apply; eauto.
Qed.

Lemma retag_one_preserves_get_definedness ok retag s p s' :
  retag_one ok retag s p ?= s' ->
  forall p, get (Symbolic.mem s) p = get (Symbolic.mem s') p :> bool.
Proof.
  rewrite /retag_one.
  case GET: (sget _ _) => [[cid I W]|] //=.
  case: (ok _ _ _ _) => //=.
  case: (retag _ _ _ _) => [cid' I' W'] //= UPD p'.
  have [{p'} ->|NEQ] := (p' =P p).
  - case GET': (get (Symbolic.mem s) p) => [[x L]|].
    + by rewrite (get_supd_eq _ _ _ _ _ _ GET' UPD).
    + by rewrite (get_supd_none _ _ _ _ _ GET' UPD).
  - by rewrite (get_supd_neq _ _ _ _ _ NEQ UPD).
Qed.

Lemma retag_set_preserves_get_definedness ok retag ps s s' :
  retag_set ok retag ps s ?= s' ->
  forall p, get (Symbolic.mem s) p = get (Symbolic.mem s') p :> bool.
Proof.
  move=> H.
  have := (ofoldl_preserve _ _ _ _ _ _ _ (retag_one_preserves_get_definedness ok retag) _ _ H).
  by apply; eauto.
Qed.

Lemma retag_one_preserves_registers ok retag s p s' :
  retag_one ok retag s p ?= s' ->
  Symbolic.regs s' = Symbolic.regs s.
Proof.
  rewrite /retag_one.
  case: (sget _ _) => [[? ? ?]|] //=.
  case: (ok _ _ _ _) => //=.
  case: (retag _ _ _ _) => ? ? ? UPD.
  by rewrite (supd_preserves_regs _ _ _ _ UPD).
Qed.

Lemma retag_set_preserves_registers ok retag ps s s' :
  retag_set ok retag ps s ?= s' ->
  Symbolic.regs s' = Symbolic.regs s.
Proof.
  move=> H.
  have := (ofoldl_preserve _ _ _ _ _ _ _ (retag_one_preserves_registers ok retag) _ _ H).
  apply; eauto; congruence.
Qed.

Lemma retag_set_forall : forall ok retag ps s s',
  uniq ps ->
  retag_set ok retag ps s ?= s' ->
  forall p,
    p \in ps ->
    exists c I W, sget s p ?= DATA c I W /\ ok p c I W.
Proof.
  rewrite /retag_set /retag_one.
  move=> ok retag ps; move: ok retag; induction ps as [|p ps];
    move=> //= ok retag s s'' NODUP RETAG_SET p' IN.
  let I := fresh "I"
  in undo1    RETAG_SET s';
     undoDATA def_s' x c I W;
     undo1    def_s' OK;
     destruct (retag p c I W) as [c' I' W'] eqn:RETAG; simpl in *; try done.
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
  rewrite /retag_set /retag_one.
  intros ok retag ps; induction ps as [|p ps]; simpl;
    intros s s' RETAG p' NIN.
  - by inversion RETAG; subst.
  - let I := fresh "I"
    in undo1 RETAG s'';
       undoDATA def_s'' x c I W; undo1 def_s'' OK;
       destruct (retag p c I W) as [c' I' W'] eqn:TAG; try discriminate.
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
                  ok p c I W /\
                  sget s' p ?= retag p c I W.
Proof.
  rewrite /retag_set /retag_one.
  intros ok retag ps; induction ps as [|p ps]; simpl;
    intros s s' NODUP RETAG p' IN.
  - inversion IN.
  - let I := fresh "I"
    in undo1 RETAG s''; undoDATA def_s'' x c I W; undo1 def_s'' OK;
       destruct (retag p c I W) as [c' I' W'] eqn:TAG; try discriminate.
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
                  sget s' p ?= retag p c I W.
Proof.
  intros until 0; intros NODUP RETAG p IN.
  eapply retag_set_in_ok in RETAG; eauto.
  repeat invh ex; repeat invh and; repeat eexists; eassumption.
Qed.

Lemma retag_set_or_ok : forall ok retag ps s s',
  uniq ps ->
  retag_set ok retag ps s ?= s' ->
  forall p,
    sget s p = sget s' p \/
    exists c I W, sget s p ?= DATA c I W /\
                  ok p c I W /\
                  sget s' p ?= retag p c I W.
Proof.
  intros ok retag ps s s' NODUP RETAG p.
  have [IN | NIN] := boolP (p \in ps).
  - by eapply retag_set_in_ok in RETAG; eauto.
  - by eapply retag_set_not_in in RETAG; eauto.
Qed.

Lemma retag_set_or : forall ok retag ps s s',
  uniq ps ->
  retag_set ok retag ps s ?= s' ->
  forall p,
    sget s p = sget s' p \/
    exists c I W, sget s p ?= DATA c I W /\ sget s' p ?= retag p c I W.
Proof.
  intros ok retag ps s s' NODUP RETAG p.
  have [IN | NIN] := boolP (p \in ps).
  - by eapply retag_set_in in RETAG; eauto.
  - by eapply retag_set_not_in in RETAG; eauto.
Qed.

Lemma retag_set_same_val ok retag ps s s' :
  retag_set ok retag ps s ?= s' ->
  omap (fun x => val x) \o get (Symbolic.mem s) =1
  omap (fun x => val x) \o get (Symbolic.mem s').
Proof.
  rewrite /retag_set /retag_one.
  elim: ps s s' => [|p ps IH] s s' /=; first by move=> [->].
  case: (sget s p) => //; move=> [c I W] //=.
  case: (ok p c I W) => //.
  case: (retag p c I W) => // c' I' W'.
  case UPD: (supd _ _ _) => [s''|] //= RETAG p'.
  rewrite (supd_same_val _ _ _ _ UPD).
  exact: (IH _ _ RETAG).
Qed.

Lemma retag_set_or_ok_get : forall ok retag ps s s',
  uniq ps ->
  retag_set ok retag ps s ?= s' ->
  forall p,
    get (Symbolic.mem s) p = get (Symbolic.mem s') p \/
    exists x c I W, get (Symbolic.mem s) p ?= x@(DATA c I W) /\
                    ok p c I W /\
                    get (Symbolic.mem s') p ?= x@(retag p c I W).
Proof.
  intros ok retag ps s s' NODUP RETAG p.
  move: (retag_set_same_val _ _ _ _ _ RETAG p) => /= GET.
  generalize (retag_set_or_ok ok retag ps s s' NODUP RETAG p)
             => [[EQ | [c [I [W [OLD [OK NEW]]]]]]].
  - move: EQ GET {RETAG NODUP}.
    rewrite /sget.
    case: s => m ? ? [? ? ? ?]; case: s' => m' ? ? [? ? ? ?] /=.
    case: (get m p)  => [[v l]|];
    case: (get m' p) => [[v' l']|] //=; last by auto.
    by move=> [<-] [<-]; left.
  - move: GET OLD OK NEW {RETAG}.
    rewrite /sget.
    case: s => m ? ? [? ? ? ?]; case: s' => m' ? ? [? ? ? ?] /=.
    case: (get m p)  => [[v l]|];
    case: (get m' p) => [[v' l']|] //=; last by auto.
    move=> [->] [->] OK [->].
    right.
    eexists v', c, I, W.
    by auto.
Qed.

Lemma retag_set_preserves_regs : forall ok retag ps s s',
  retag_set ok retag ps s ?= s' ->
  Symbolic.regs s = Symbolic.regs s'.
Proof.
  rewrite /retag_set /retag_one.
  intros ok retag ps s s' RETAG_SET; simpl.
  move: s s' RETAG_SET; induction ps as [|p ps];
    move=> /= s s' RETAG_SET.
  - by inversion RETAG_SET; subst.
  - idtac;
      undo1 RETAG_SET s'';
      undoDATA def_s'' x c I' W; rename I' into I;
      undo1 def_s'' OK;
      destruct (retag p c I W) as [c' I' W'] eqn:def_c'_I'_W'; try discriminate.
    apply supd_preserves_regs in def_s''; apply IHps in RETAG_SET; congruence.
Qed.

Lemma retag_set_preserves_pc : forall ok retag ps s s',
  retag_set ok retag ps s ?= s' ->
  Symbolic.pc s = Symbolic.pc s'.
Proof.
  rewrite /retag_set /retag_one.
  intros ok retag ps s s' RETAG_SET; simpl.
  move: s s' RETAG_SET; induction ps as [|p ps];
    move=> /= s s' RETAG_SET.
  - by inversion RETAG_SET; subst.
  - idtac;
      undo1 RETAG_SET s2;
      undoDATA def_s2 x c I' W; rename I' into I;
      undo1 def_s2 OK;
      destruct (retag p c I W) as [c' I' W'] eqn:def_c'_I'_W'; try discriminate.
    apply supd_preserves_pc in def_s2; apply IHps in RETAG_SET; congruence.
Qed.

Lemma retag_set_preserves_next_id : forall ok retag ps s s',
  retag_set ok retag ps s ?= s' ->
  next_id (Symbolic.internal s) = next_id (Symbolic.internal s').
Proof.
  rewrite /retag_set /retag_one.
  intros ok retag ps s s' RETAG_SET; simpl.
  move: s s' RETAG_SET; induction ps as [|p ps];
    move=> /= s s' RETAG_SET.
  - by inversion RETAG_SET; subst.
  - idtac;
      undo1 RETAG_SET s2;
      undoDATA def_s2 x c I' W; rename I' into I;
      undo1 def_s2 OK;
      destruct (retag p c I W) as [c' I' W'] eqn:def_c'_I'_W'; try discriminate.
    apply supd_preserves_next_id in def_s2; apply IHps in RETAG_SET; congruence.
Qed.

Lemma retag_set_preserves_bounded_by ok retag ps cnew s s' :
  cnew <> max_word t ->
  bounded_by s cnew ->
  retag_set ok retag ps s ?= s' ->
  (forall p cid I W, data_tag_compartment (retag p cid I W) \in [:: cid; cnew]) ->
  (forall p cid I W, data_tag_incoming (retag p cid I W) :|:
                     data_tag_writers  (retag p cid I W) \subset
                     cnew |: I :|: W) ->
  bounded_by s' (cnew+1)%w.
Proof.
  move=> Hnot_max Hbounds Hretag Hnew_cid Hnew_targets.
  have {Hbounds} Hbounds : bounded_by s (cnew+1)%w.
  { move=> p cid I W /Hbounds {Hbounds} H cid' /H {H}.
    by apply: succ_trans. }
  have Hsucc : cnew <? (cnew + 1)%w.
  { apply: lebw_succ; first exact: max_word t.
    apply/ltb_lt.
    move/leb_le: (lew_max cnew).
    rewrite leb_is_ltb_or_eq.
    case/orP => [//|].
    case: (SetoidDec.equiv_dec _ _) => //=. }
  elim: ps s Hbounds Hretag
        => [ s Hbounds [<-] //
           | p ps IH s Hbounds ].
  rewrite /retag_set /retag_one /=.
  case Hsget: (sget _ _) => [[cid I W]|] //=.
  case: (ok _ _ _ _) => //.
  case Hsupd: (supd _ _ _) => [s''|] //=.
  apply: IH => p' cid' I' W'.
  rewrite (sget_supd _ _ _ _ Hsupd).
  have [/= _ {p'} [Hretag] cid''|_] := p' =P p; last by apply: Hbounds.
  rewrite -setUA in_setU1=> /orP [/eqP -> {cid''}| Hcid''].
  - move: (Hnew_cid p cid I W).
    rewrite Hretag {Hretag} /= !inE=> /orP [/eqP -> | /eqP -> //] {cid'}.
    apply: {Hbounds} (Hbounds _ _ _ _ Hsget cid).
    by rewrite in_setU in_setU1 eqxx.
  - move: (Hnew_targets p cid I W).
    rewrite Hretag /= => /subsetP/(_ _ Hcid'') {Hcid''}.
    rewrite -setUA in_setU1.
    case/orP=> [/eqP -> {cid''} //|cid''_in].
    apply: (Hbounds _ _ _ _ Hsget cid'').
    by rewrite -setUA in_setU1 cid''_in orbT.
Qed.

Lemma retag_set_preserves_isolated_syscalls ok retag ps s s' cnew :
  bounded_by s cnew ->
  isolated_syscalls s ->
  retag_set ok retag ps s ?= s' ->
  (forall sc cid I W,
     sc \in syscall_addrs ->
     data_tag_compartment (retag sc cid I W) = cid) ->
  (forall p cid I W, data_tag_compartment (retag p cid I W) \in [:: cid; cnew]) ->
  isolated_syscalls s'.
Proof.
  move=> Hbounds Hisolated Hretag Hsc_cid Hnew_cid.
  have {Hbounds} Hpreserved :
    forall sc cid I W,
      sc \in syscall_addrs ->
      sget s sc = Some (DATA cid I W) ->
      cid != cnew.
  { move=> sc cid I W sc_is_sc Hsget.
    apply/negP=> /eqP ?. subst cid.
    move: (Hbounds sc cnew I W Hsget cnew).
    by rewrite -setUA in_setU1 eqxx /= ltb_irrefl => /(_ erefl). }
  elim: ps s Hpreserved Hisolated Hretag
        => [ s _ _ [<-] //
           | p ps IH ] s Hpreserved Hisolated.
  rewrite /retag_set /retag_one /=.
  case Hsget: (sget _ _) => [[cid I W]|] //=.
  case: (ok _ _ _ _) => //.
  case Hsupd: (supd _ _ _) => [s''|] //= Hretag.
  apply: (IH s'') => //.
  - move=> sc cid' I' W'.
    rewrite (sget_supd _ _ _ _ Hsupd).
    have [-> {sc} /=|_] := sc =P p.
    + move=> p_in_scs [Hretag_p].
      move: Hretag_p (Hsc_cid p cid I W p_in_scs) => -> /= -> {cid'}.
      by apply: (Hpreserved p cid I W).
    + by apply: Hpreserved.
  - move=> p' sc.
    rewrite !(sget_supd _ _ _ _ Hsupd).
    have [/= {p'} ->|_] := p' =P p;
    have [/= {sc} -> //|_] := sc =P p.
    + move=> sc_is_sc.
      move: (Hnew_cid p cid I W).
      rewrite !inE=> /orP [/eqP E' E | /eqP ->].
      * apply (Hisolated p sc sc_is_sc).
        by rewrite -E Hsget E'.
      * case Hsget': (sget _ _) => [[cid' I' W']|] //= [?].
        subst cid'.
        move: (Hpreserved sc cnew I' W' sc_is_sc Hsget').
        by rewrite eqxx.
    + move=> sc_is_sc.
      rewrite (Hsc_cid p cid I W sc_is_sc)=> E.
      apply (Hisolated p' p sc_is_sc).
      by rewrite Hsget.
    + by apply Hisolated.
Qed.

Lemma retag_set_preserves_good_internal ok retag ps s s' pc' :
  good_internal s ->
  retag_set ok retag ps s ?= s' ->
  let cnew := next_id (Symbolic.internal s) in
  cnew <> max_word t ->
  (forall sc cid I W,
     sc \in syscall_addrs ->
     data_tag_compartment (retag sc cid I W) = cid) ->
  (forall p cid I W, data_tag_compartment (retag p cid I W) \in [:: cid; cnew]) ->
  (forall p cid I W, data_tag_incoming (retag p cid I W) :|:
                     data_tag_writers  (retag p cid I W) \subset
                     cnew |: I :|: W) ->
  good_internal (Symbolic.State (Symbolic.mem s')
                                (Symbolic.regs s')
                                pc'
                                (bump_next_id (Symbolic.internal s'))).
Proof.
  move=> [Hbounded Hisolated] Hretag /= Hnot_max Hsc_cid Hnew_cid Hnew_targets.
  split.
  - move: (retag_set_preserves_bounded_by _ _ _ _ _ _
                                          Hnot_max Hbounded Hretag Hnew_cid Hnew_targets).
    rewrite (retag_set_preserves_next_id _ _ _ _ _ Hretag) {Hretag}.
    by case: s' => mem regs pc [id ? ? ?] /= {Hbounded} Hbounded p cid I W /Hbounded.
  - move: (retag_set_preserves_isolated_syscalls
             _ _ _ _ _ _
             Hbounded Hisolated Hretag Hsc_cid Hnew_cid) => {Hretag}.
    case: s' => mem regs pc [id ? ? ?] /= {Hisolated} Hisolated p sc sc_is_sc /= /Hisolated.
    by apply.
Qed.

End WithClasses.

Notation memory    t := (Symbolic.memory    t (@sym_compartmentalization t)).
Notation registers t := (Symbolic.registers t (@sym_compartmentalization t)).

End Sym.

Export Sym.Exports.
