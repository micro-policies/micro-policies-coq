From mathcomp Require Import
  ssreflect ssrfun ssrbool eqtype ssrnat seq fintype finset.

From CoqUtils Require Import ord hseq word fmap fset.

Require Import lib.utils lib.word_utils lib.ssr_set_utils common.types.
Require Import symbolic.symbolic.
Require Import compartmentalization.common.
Require Import compartmentalization.isolate_sets compartmentalization.ranges.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Module Sym.

Inductive pc_tag (mt : machine_types) :=
| PC (F : where_from) (c : mword mt).
Arguments PC [mt] F c.

Inductive data_tag (mt : machine_types) :=
| DATA (c : mword mt) (I W : {set mword mt}).
Arguments DATA [mt] c I W.

Module Exports.

Section Equality.

Context (mt : machine_types).

Definition pc_tag_eq (t1 t2 : pc_tag mt) : bool :=
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

Definition data_tag_eq (t1 t2 : data_tag mt) : bool :=
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

Context {mt           : machine_types}
        {ops          : machine_ops mt}
        {spec         : machine_ops_spec ops}
        {scr          : syscall_regs mt}
        {cmp_syscalls : compartmentalization_syscall_addrs mt}.

(* I want to use I as a variable. *)
Local Notation II := Logic.I.

Notation pc_tag := (pc_tag mt).
Notation data_tag := (data_tag mt).

Definition pc_tag_compartment (L : pc_tag) : mword mt :=
  match L with PC _ c => c end.

Definition data_tag_compartment (L : data_tag) : mword mt :=
  match L with DATA c _ _ => c end.

Definition pc_tag_source (L : pc_tag) : where_from :=
  match L with PC F _ => F end.

Definition data_tag_incoming (L : data_tag) : {set mword mt} :=
  match L with DATA _ In _ => In end.

Definition data_tag_writers (L : data_tag) : {set mword mt} :=
  match L with DATA _ _ W => W end.

Definition stags := {|
  Symbolic.pc_tag_type := [eqType of pc_tag];
  Symbolic.reg_tag_type := [eqType of unit];
  Symbolic.mem_tag_type := [eqType of data_tag];
  Symbolic.entry_tag_type := [eqType of data_tag]
|}.

Import Symbolic.

Definition can_execute (Lpc : pc_tag) (LI : data_tag) : option (mword mt) :=
  do! guard (data_tag_compartment LI == pc_tag_compartment Lpc) ||
            ((pc_tag_source Lpc == JUMPED) &&
             (pc_tag_compartment Lpc \in data_tag_incoming LI));
  Some (data_tag_compartment LI).

Definition compartmentalization_rvec (op : opcode)
                                     (F : where_from)
                                     (c : mword mt)
                                     (tr : type_of_result stags (outputs op)) : ovec stags op :=
  @OVec stags _ (PC F c) tr.

Definition rvec_step op
                     (rv : mword mt -> option (ovec stags op))
                     (Lpc : pc_tag) (LI : data_tag)  : option (ovec stags op) :=
  do! c <- can_execute Lpc LI;
  rv c.

Definition rvec_simple op (F : where_from) (tr : type_of_result stags (outputs op)) :
                       pc_tag -> data_tag -> option (ovec stags op) :=
  rvec_step (fun c => Some (compartmentalization_rvec F c tr)).

Definition rvec_next op (tr : type_of_result stags (outputs op)) : pc_tag -> data_tag -> option (ovec stags op) :=
  rvec_simple INTERNAL tr.
Definition rvec_jump op (tr : type_of_result stags (outputs op)) : pc_tag -> data_tag -> option (ovec stags op) :=
  rvec_simple JUMPED tr.
Definition rvec_store (c : mword mt) (I W : {set mword mt})
                      : pc_tag -> data_tag -> option (ovec stags STORE) :=
  rvec_step (fun c' =>
    do! guard (c == c') || (c' \in W);
    Some (@OVec stags STORE (PC INTERNAL c') (DATA c I W))).

(* The `REG's in the ivec's fields can also be _s; it's an invariant that
   registers are always tagged with `REG'. *)
Definition compartmentalization_handler (iv : ivec stags) : option (vovec stags (op iv)) :=
  match iv with
    | IVec (OP NOP)       Lpc LI [hseq]                       => @rvec_next NOP       tt  Lpc LI
    | IVec (OP CONST)     Lpc LI [hseq REG]                   => @rvec_next CONST     REG Lpc LI
    | IVec (OP MOV)       Lpc LI [hseq REG; REG]              => @rvec_next MOV       REG Lpc LI
    | IVec (OP (BINOP b)) Lpc LI [hseq REG; REG; REG]         => @rvec_next (BINOP b) REG Lpc LI
    | IVec (OP LOAD)      Lpc LI [hseq REG; DATA _ _ _; REG]  => @rvec_next LOAD      REG Lpc LI
    | IVec (OP STORE)     Lpc LI [hseq REG; REG; DATA c In W] => rvec_store c In W Lpc LI
    | IVec (OP JUMP)      Lpc LI [hseq REG]                   => @rvec_jump JUMP      tt  Lpc LI
    | IVec (OP BNZ)       Lpc LI [hseq REG]                   => @rvec_next BNZ       tt  Lpc LI
    | IVec (OP JAL)       Lpc LI [hseq REG; REG]              => @rvec_jump JAL       REG Lpc LI
    | IVec SERVICE        Lpc LI [hseq]                       => Some tt
    | IVec _         _   _  _                               => None
  end.

Record compartmentalization_internal :=
  Internal { next_id                  : mword mt
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

Local Notation memory    := (Symbolic.memory mt sym_compartmentalization).
Local Notation registers := (Symbolic.registers mt sym_compartmentalization).

Definition sget (s : Symbolic.state mt) (p : mword mt)
                : option data_tag :=
  let: Symbolic.State mem _ _ si := s in
  let sctag get_tag := Some (get_tag si) in
  match mem p with
    | Some _@tg => Some tg
    | None   =>
      if      p == isolate_addr              then sctag isolate_tag
      else if p == add_to_jump_targets_addr  then sctag add_to_jump_targets_tag
      else if p == add_to_store_targets_addr then sctag add_to_store_targets_tag
      else None
  end.
Arguments sget s p : simpl never.

Definition supd (s : Symbolic.state mt) (p : mword mt) (tg : data_tag)
                : option (Symbolic.state mt) :=
  let: Symbolic.State mem reg pc si := s in
  let: Internal next_id
                isolate_tag
                add_to_jump_targets_tag
                add_to_store_targets_tag :=
       si in
  let sctagged si' := Some (Symbolic.State mem reg pc si') in
  match repm mem p (fun v => (vala v)@tg) with
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
                 : option (mword mt * compartmentalization_internal) :=
  let 'Internal next iT ajtT asmT := si in
  if next == monew
  then None
  else Some (next, Internal (next+1)%w iT ajtT asmT).

Definition fresh' (si : compartmentalization_internal)
                  : option (mword mt) :=
  if next_id si == monew
  then None
  else Some (next_id si).

Definition bump_next_id (si : compartmentalization_internal)
                        : compartmentalization_internal :=
  Internal (next_id si + 1)%w
           (isolate_tag si)
           (add_to_jump_targets_tag si)
           (add_to_store_targets_tag si).

Definition retag_one (ok : mword mt -> mword mt -> {set mword mt} -> {set mword mt} -> bool)
                     (retag : mword mt -> mword mt -> {set mword mt} -> {set mword mt} -> data_tag)
                     (s : Symbolic.state mt)
                     (p : mword mt)
                     : option (Symbolic.state mt) :=
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

Definition retag_set (ok : mword mt -> mword mt -> {set mword mt} -> {set mword mt} -> bool)
                     (retag : mword mt -> mword mt -> {set mword mt} -> {set mword mt}-> data_tag)
                     (ps : seq (mword mt))
                     (s : Symbolic.state mt)
                     : option (Symbolic.state mt) :=
  ofoldl (retag_one ok retag) s ps.

Definition do_ok (cur : mword mt)
                 (A J S : {set mword mt})
                 (p : mword mt)
                 (cid : mword mt) (I W : {set mword mt})
                 : bool :=
  [&& (p \in A) ==> (cid == cur),
      (p \in J) ==> (cid == cur) || (cur \in I) &
      (p \in S) ==> (cid == cur) || (cur \in W) ].

Definition do_retag (cur new : mword mt)
                    (A J S : {set mword mt})
                    (p : mword mt)
                    (cid : mword mt) (I W : {set mword mt})
                    : data_tag :=
  let cid' := if p \in A then new      else cid in
  let I'   := if p \in J then new |: I else I   in
  let W'   := if p \in S then new |: W else W   in
  DATA cid' I' W'.

Definition isolate (s : Symbolic.state mt) : option (Symbolic.state mt) :=
  match s with
  | Symbolic.State MM RR (pc @ (PC F c)) si =>
    do! LI    <- sget s pc;
    do! c_sys <- can_execute (PC F c) LI;

    do! c'    <- fresh' si;

    do! pA @ _ <- RR syscall_arg1;
    do! pJ @ _ <- RR syscall_arg2;
    do! pS @ _ <- RR syscall_arg3;

    do! A' <- isolate_create_set vala MM pA;
    do! guard A' != set0;
    do! J' : {set mword mt} <- isolate_create_set vala MM pJ;
    do! S' : {set mword mt} <- isolate_create_set vala MM pS;

    do! s' <- retag_set (do_ok c A' J' S')
                        (do_retag c c' A' J' S')
                        (enum_set (A' :|: J' :|: S')) s;

    do! pc' @ _              <- RR ra;
    do! DATA c_next I_next _ <- sget s' pc';
    do! guard c == c_next;
    do! guard c_sys \in I_next;

    let: Symbolic.State M' R' _ si' := s' in
    Some (Symbolic.State M' R' (pc' @ (PC JUMPED c_sys)) (bump_next_id si'))
  end.

Definition add_to_jump_targets (s : Symbolic.state mt)
                               : option (Symbolic.state mt) :=
  match s with
    | Symbolic.State MM RR (pc @ (PC F c)) si =>
      do! LI    <- sget s pc;
      do! c_sys <- can_execute (PC F c) LI;
      do! guard c != c_sys;

      do! p @ _         <- RR syscall_arg1;
      do! DATA c' I' W' <- sget s p;

      do! guard (c' == c) || (c \in I');
      do! s' <- supd s p (DATA c' (c |: I') W');

      do! pc' @ _              <- RR ra;
      do! DATA c_next I_next _ <- sget s' pc';
      do! guard c == c_next;
      do! guard c_sys \in I_next;

      let: Symbolic.State M_next R_next _ si_next := s' in
      Some (Symbolic.State M_next R_next (pc' @ (PC JUMPED c_sys)) si_next)
  end.

Definition add_to_store_targets (s : Symbolic.state mt)
                                : option (Symbolic.state mt) :=
  match s with
    | Symbolic.State MM RR (pc @ (PC F c)) si =>
      do! LI    <- sget s pc;
      do! c_sys <- can_execute (PC F c) LI;
      do! guard c != c_sys;

      do! p @ _         <- RR syscall_arg1;
      do! DATA c' I' W' <- sget s p;

      do! guard (c' == c) || (c \in W');
      do! s' <- supd s p (DATA c' I' (c |: W'));

      do! pc' @ _              <- RR ra;
      do! DATA c_next I_next _ <- sget s' pc';
      do! guard c == c_next;
      do! guard c_sys \in I_next;

      let: Symbolic.State M_next R_next _ si_next := s' in
      Some (Symbolic.State M_next R_next (pc' @ (PC JUMPED c_sys)) si_next)
  end.

Definition syscalls : Symbolic.syscall_table mt :=
  let dummy := DATA 0%w set0 set0 in
  [fmap (isolate_addr,              Symbolic.Syscall dummy isolate);
        (add_to_jump_targets_addr,  Symbolic.Syscall dummy add_to_jump_targets);
        (add_to_store_targets_addr, Symbolic.Syscall dummy add_to_store_targets)].

Definition step := Symbolic.step syscalls.

Definition bounded_by (s : Symbolic.state mt) id : Prop :=
  forall p cid I W,
    sget s p = Some (DATA cid I W) ->
    forall cid',
      cid' \in cid |: I :|: W ->
      (cid' < id)%ord.

Definition isolated_syscalls (s : Symbolic.state mt) : Prop :=
  forall p sc_addr,
    sc_addr \in syscall_addrs ->
    omap data_tag_compartment (sget s p) =
    omap data_tag_compartment (sget s sc_addr) ->
    p = sc_addr.

Definition good_internal (s : Symbolic.state mt) : Prop :=
  bounded_by s (next_id (Symbolic.internal s)) /\ isolated_syscalls s.

Definition good_pc_tag (s : Symbolic.state mt)
                       (pc : atom (mword mt) pc_tag) : Prop :=
  match pc with
    | _ @ (PC _ c) => exists p I W, sget s p ?= Sym.DATA c I W
  end.

Definition good_tags (s : Symbolic.state mt) : Prop :=
  let: Symbolic.State MM RR pc si := s in
  good_pc_tag s pc.

Definition good_state (s : Symbolic.state mt) : Prop :=
  good_tags s /\ good_internal s.

Generalizable All Variables.

Theorem sget_supd s s' p L :
  supd s p L ?= s' ->
  forall p',
    sget s' p' = if p' == p then Some L else sget s p'.
Proof.
  case: s => m r pc [ni it atjt atst]; case: s' => m' r' pc' [ni' it' atjt' atst'].
  rewrite /supd /= /repm /sget.
  case GET: (getm m p) => [[x L']|] /=.
  - move=> {r' pc' ni'} [<- _ _ _ <- <- <-] p' /=.
    rewrite setmE.
    by have [{p'} _|NE] := (p' =P p).
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
  rewrite /supd /= /repm /sget.
  case GET: (getm m p) => [[v tg]|] /=.
  - move=> [<- _ _ _ <- <- <-].
    rewrite setmE.
    by have [{p'} ->|NE] := (p' =P p); first by rewrite GET.
  - do !case: (p =P _) => ? //; subst.
    + move=> [<- _ _ _ <- <- <-].
      case: (getm m p') => //.
      by do !case: (p' =P _).
    + move=> [<- _ _ _ <- <- <-].
      case: (getm m p') => //.
      by do !case: (p' =P _).
    + move=> [<- _ _ _ <- <- <-].
      case: (getm m p') => //.
      by do !case: (p' =P _).
Qed.

Theorem get_supd_eq s s' p x L L' :
  getm (Symbolic.mem s) p ?= x@L ->
  supd s p L' ?= s' ->
  getm (Symbolic.mem s') p ?= x@L'.
Proof.
  case: s => m r pc [ni it atjt atst]; case: s' => m' r' pc' [ni' it' atjt' atst'] /=.
  rewrite /supd /repm => -> /= [<- _ _ _ _ _ _].
  by rewrite setmE eqxx.
Qed.

Theorem get_supd_neq s s' p p' v :
  p' <> p ->
  supd s p v ?= s' ->
  Symbolic.mem s' p' = Symbolic.mem s p'.
Proof.
  case: s => m r pc [ni it atjt atst]; case: s' => m' r' pc' [ni' it' atjt' atst'] NE /=.
  rewrite /supd.
  case REP: (repm _ _ _) => [m''|].
  - move=> [<- _ _ _ _ _ _].
    by rewrite (repmE REP) (introF (_ =P _) NE).
  - repeat case: (p =P _) => _ //=; congruence.
Qed.

Theorem get_supd_none s s' p p' v :
  Symbolic.mem s p = None ->
  supd s p' v ?= s' ->
  Symbolic.mem s' p = None.
Proof.
  case: s => m r pc [ni it atjt atst]; case: s' => m' r' pc' [ni' it' atjt' atst'] /= NONE.
  rewrite /supd.
  case REP: (repm _ _ _) => [m''|].
  - move=> [<- _ _ _ _ _ _].
    rewrite (repmE REP) NONE.
    move: REP. rewrite /repm.
    have [{p'} <-|//] := (p =P p').
    by rewrite NONE.
  - repeat case: (p' =P _) => _; congruence.
Qed.

Theorem supd_same_val s p L s' :
  supd s p L ?= s' ->
  omap vala \o getm (Symbolic.mem s) =1
  omap vala \o getm (Symbolic.mem s').
Proof.
  case: s => m r pc [ni it atjt atst]; case: s' => m' r' pc' [ni' it' atjt' atst'] /=.
  rewrite /supd.
  case REP: (repm m p _) => [m''|].
  - move=> [<- _ _ _ _ _ _] p' /=.
    rewrite (repmE REP).
    have [->|_] := (p' =P p) => //.
    by case: (getm m p) => [[? ?]|].
  - repeat case: (p =P _) => _; congruence.
Qed.

Theorem supd_preserves_regs : forall s p v s',
  supd s p v ?= s' ->
  Symbolic.regs s = Symbolic.regs s'.
Proof.
  move=> [mem reg pc [next iT aJT aST]] /= p v s' SUPD;
    rewrite /supd /= in SUPD.
  move: SUPD.
  case: (repm mem p _) => [m'' [<-] //|].
  by repeat case: (p =P _) => _ //; move=> [<-].
Qed.

Theorem supd_preserves_pc : forall s p v s',
  supd s p v ?= s' ->
  Symbolic.pc s = Symbolic.pc s'.
Proof.
  move=> [mem reg pc [next iT aJT aST]] /= p v s' SUPD;
    rewrite /supd /= in SUPD.
  move: SUPD.
  case: (repm mem p _) => [m'' [<-] //|].
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
  case: (repm mem p _) => [m'' [<-] //|].
  by repeat case: (p =P _) => _ //; move=> [<-].
Qed.

Lemma succ_trans : forall x y : mword mt,
  (y <> monew -> x < y -> x < (y + 1)%w)%ord.
Proof.
move=> x y NEQ LT.
move: (leqw_mone y); rewrite Ord.leq_eqVlt (introF eqP NEQ) /= => H.
apply (@Ord.lt_trans _ y); first by [].
by apply (@leqw_succ _ y monew).
Qed.
Hint Resolve succ_trans.

Lemma sget_lt_next s p c I W :
  good_internal s ->
  sget s p ?= DATA c I W ->
  (c < next_id (Symbolic.internal s))%ord.
Proof.
  move=> [Hbounds Hisolated] /Hbounds/(_ c).
  by rewrite in_setU in_setU1 eqxx /= => /(_ erefl).
Qed.

Lemma sget_lt_next_I s p c I W c' :
  good_internal s ->
  sget s p ?= DATA c I W ->
  c' \in I ->
  (c' < next_id (Symbolic.internal s))%ord.
Proof.
  move=> [Hbounds Hisolated] /Hbounds/(_ c') H c'_in_I.
  apply: H.
  by rewrite !in_setU c'_in_I orbT.
Qed.

Lemma sget_lt_next_W s p c I W c' :
  good_internal s ->
  sget s p ?= DATA c I W ->
  c' \in W ->
  (c' < next_id (Symbolic.internal s))%ord.
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
  rewrite (sget_supd UPD).
  by have [{p'} ->|//] := (p' =P p); rewrite GET.
Qed.

Lemma retag_set_preserves_definedness ok retag ps s s' :
  retag_set ok retag ps s ?= s' ->
  forall p, sget s p = sget s' p :> bool.
Proof.
  move=> H.
  have := (@ofoldl_preserve _ _ _ _ _ _ _ (@retag_one_preserves_definedness ok retag) _ _ H).
  by apply; eauto.
Qed.

Lemma retag_one_preserves_get_definedness ok retag s p s' :
  retag_one ok retag s p ?= s' ->
  domm (Symbolic.mem s) = domm (Symbolic.mem s').
Proof.
  rewrite /retag_one.
  case GET: (sget _ _) => [[cid I W]|] //=.
  case: (ok _ _ _ _) => //=.
  case: (retag _ _ _ _) => [cid' I' W'] //= UPD; apply/eq_fset=> p'; rewrite !mem_domm.
  have [{p'} ->|NEQ] := (p' =P p).
  - case GET': (Symbolic.mem s p) => [[x L]|].
    + by rewrite (get_supd_eq GET' UPD).
    + by rewrite (get_supd_none GET' UPD).
  - by rewrite (get_supd_neq NEQ UPD).
Qed.

Lemma retag_set_preserves_get_definedness ok retag ps s s' :
  retag_set ok retag ps s ?= s' ->
  domm (Symbolic.mem s) = domm (Symbolic.mem s').
Proof.
move=> H.
have := (@ofoldl_preserve _ _ _ _ _ _ _ (@retag_one_preserves_get_definedness ok retag) _ _ H).
apply=> // *; congruence.
Qed.

Lemma retag_one_preserves_registers ok retag s p s' :
  retag_one ok retag s p ?= s' ->
  Symbolic.regs s' = Symbolic.regs s.
Proof.
  rewrite /retag_one.
  case: (sget _ _) => [[? ? ?]|] //=.
  case: (ok _ _ _ _) => //=.
  case: (retag _ _ _ _) => ? ? ? UPD.
  by rewrite (supd_preserves_regs UPD).
Qed.

Lemma retag_set_preserves_registers ok retag ps s s' :
  retag_set ok retag ps s ?= s' ->
  Symbolic.regs s' = Symbolic.regs s.
Proof.
  move=> H.
  have := (@ofoldl_preserve _ _ _ _ _ _ _ (@retag_one_preserves_registers ok retag) _ _ H).
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
  omap vala \o getm (Symbolic.mem s) =1
  omap vala \o getm (Symbolic.mem s').
Proof.
  rewrite /retag_set /retag_one.
  elim: ps s s' => [|p ps IH] s s' /=; first by move=> [->].
  case: (sget s p) => //; move=> [c I W] //=.
  case: (ok p c I W) => //.
  case: (retag p c I W) => // c' I' W'.
  case UPD: (supd _ _ _) => [s''|] //= RETAG p'.
  rewrite (supd_same_val UPD).
  exact: (IH _ _ RETAG).
Qed.

Lemma retag_set_or_ok_get : forall ok retag ps s s',
  uniq ps ->
  retag_set ok retag ps s ?= s' ->
  forall p,
    getm (Symbolic.mem s) p = getm (Symbolic.mem s') p \/
    exists x c I W, getm (Symbolic.mem s) p ?= x@(DATA c I W) /\
                    ok p c I W /\
                    getm (Symbolic.mem s') p ?= x@(retag p c I W).
Proof.
  intros ok retag ps s s' NODUP RETAG p.
  move: (retag_set_same_val RETAG p) => /= GET.
  generalize (retag_set_or_ok NODUP RETAG p)
             => [[EQ | [c [I [W [OLD [OK NEW]]]]]]].
  - move: EQ GET {RETAG NODUP}.
    rewrite /sget.
    case: s => m ? ? [? ? ? ?]; case: s' => m' ? ? [? ? ? ?] /=.
    case: (m p)  => [[v l]|];
    case: (m' p) => [[v' l']|] //=; last by auto.
    by move=> [<-] [<-]; left.
  - move: GET OLD OK NEW {RETAG}.
    rewrite /sget.
    case: s => m ? ? [? ? ? ?]; case: s' => m' ? ? [? ? ? ?] /=.
    case: (m p)  => [[v l]|];
    case: (m' p) => [[v' l']|] //=; last by auto.
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
  cnew <> monew ->
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
  have Hsucc : (cnew < (cnew + 1)%w)%ord.
  { apply: (@leqw_succ _ _ monew).
    by move: (leqw_mone cnew); rewrite Ord.leq_eqVlt (introF eqP Hnot_max). }
  elim: ps s Hbounds Hretag
        => [ s Hbounds [<-] //
           | p ps IH s Hbounds ].
  rewrite /retag_set /retag_one /=.
  case Hsget: (sget _ _) => [[cid I W]|] //=.
  case: (ok _ _ _ _) => //.
  case Hsupd: (supd _ _ _) => [s''|] //=.
  apply: IH => p' cid' I' W'.
  rewrite (sget_supd Hsupd).
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
    by rewrite -setUA in_setU1 eqxx /= Ord.ltxx => /(_ erefl). }
  elim: ps s Hpreserved Hisolated Hretag
        => [ s _ _ [<-] //
           | p ps IH ] s Hpreserved Hisolated.
  rewrite /retag_set /retag_one /=.
  case Hsget: (sget _ _) => [[cid I W]|] //=.
  case: (ok _ _ _ _) => //.
  case Hsupd: (supd _ _ _) => [s''|] //= Hretag.
  apply: (IH s'') => //.
  - move=> sc cid' I' W'.
    rewrite (sget_supd Hsupd).
    have [-> {sc} /=|_] := sc =P p.
    + move=> p_in_scs [Hretag_p].
      move: Hretag_p (Hsc_cid p cid I W p_in_scs) => -> /= -> {cid'}.
      by apply: (Hpreserved p cid I W).
    + by apply: Hpreserved.
  - move=> p' sc.
    rewrite !(sget_supd Hsupd).
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
  cnew <> monew ->
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
  - move: (retag_set_preserves_bounded_by Hnot_max Hbounded Hretag Hnew_cid Hnew_targets).
    rewrite (retag_set_preserves_next_id Hretag) {Hretag}.
    by case: s' => mem regs pc [id ? ? ?] /= {Hbounded} Hbounded p cid I W /Hbounded.
  - move: (retag_set_preserves_isolated_syscalls
             Hbounded Hisolated Hretag Hsc_cid Hnew_cid) => {Hretag}.
    case: s' => mem regs pc [id ? ? ?] /= {Hisolated} Hisolated p sc sc_is_sc /= /Hisolated.
    by apply.
Qed.

End WithClasses.

Notation memory    mt := (Symbolic.memory    mt (@sym_compartmentalization mt)).
Notation registers mt := (Symbolic.registers mt (@sym_compartmentalization mt)).

End Sym.

Export Sym.Exports.
