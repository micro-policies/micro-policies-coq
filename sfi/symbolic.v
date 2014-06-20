Require Import List. Import ListNotations.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Require Import lib.utils lib.ordered lib.partial_maps common.common.
Require Import symbolic.symbolic symbolic.rules.
Require Import sfi.classes sfi.list_utils sfi.set_utils sfi.isolate_sets.

Module Sym.

Section WithClasses.

Import PartMaps.

Context {t            : machine_types}
        {ops          : machine_ops t}
        {spec         : machine_ops_spec ops}
        {sfi_syscalls : sfi_syscall_params t}.

(* I want to use S and I as variables. *)
Let S := Datatypes.S.
Let I := Logic.I.
(* ssreflect exposes `succn' as a synonym for `S' *)
Local Notation II := Logic.I.

Inductive where_from :=
| INTERNAL : where_from
| JUMPED   : where_from.

Inductive stag :=
| PC     : forall (S : where_from) (c : word t), stag
| DATA   : forall (c : word t) (I W : list (word t)), stag
| REG    : stag.

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

Definition where_from_eq (S1 S2 : where_from) : bool :=
  match S1, S2 with
    | INTERNAL , INTERNAL | JUMPED , JUMPED => true
    | _ , _                                 => false
  end.

Lemma where_from_eqP : Equality.axiom where_from_eq.
Proof. by move=> [|] [|] /=; apply: (iffP idP). Qed.

Definition where_from_eqMixin := EqMixin where_from_eqP.
Canonical where_from_eqType := Eval hnf in EqType where_from where_from_eqMixin.

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

Context {memory : Type}
        {sm : partial_map memory (word t) (atom (word t) stag)}
        {registers : Type}
        {sr : partial_map registers (reg t) (atom (word t) stag)}.

Import DoNotation.

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
Definition rvec_store (c' : word t) (W : list (word t))
                      : stag -> stag -> option (RVec stag) :=
  rvec_step (fun c =>
    do! guard (c == c') || set_elem c W;
    Some (sfi_rvec INTERNAL c)).

(* The `REG's in the MVec's fields can also be _s; it's an invariant that
   registers are always tagged with `REG'. *)
Definition sfi_handler (mv : MVec stag) : option (RVec stag) :=
  match mv with
    | mkMVec NOP       Lpc LI []                      => rvec_next       Lpc LI
    | mkMVec CONST     Lpc LI [REG]                   => rvec_next       Lpc LI
    | mkMVec MOV       Lpc LI [REG; REG]              => rvec_next       Lpc LI
    | mkMVec (BINOP _) Lpc LI [REG; REG; REG]         => rvec_next       Lpc LI
    | mkMVec LOAD      Lpc LI [REG; DATA _ _ _; REG]  => rvec_next       Lpc LI
    | mkMVec STORE     Lpc LI [REG; REG; DATA c' _ W] => rvec_store c' W Lpc LI
    | mkMVec JUMP      Lpc LI [REG]                   => rvec_jump       Lpc LI
    | mkMVec BNZ       Lpc LI [REG]                   => rvec_next       Lpc LI
    | mkMVec JAL       Lpc LI [REG; REG]              => rvec_jump       Lpc LI
    | mkMVec _         _   _  _                       => None
  end.

End WithVectors.

Record sfi_internal := Internal { next_id : word t
                                ; set_ids : list (list (word t) * word t) }.

Instance sym_sfi : Symbolic.symbolic_params := {
  tag := stag_eqType;
  
  handler := sfi_handler;
  
  internal_state := sfi_internal;
  
  memory := memory;
  sm     := sm;
  
  registers := registers;
  sr        := sr
}.

Notation "'do!' ( X , Y ) <- A ; B" :=
  (bind (fun XY => let '(X,Y) := XY in B) A)
  (at level 200, X ident, Y ident, A at level 100, B at level 200).

Notation "'do!' X @ L <- A ; B" :=
  (bind (fun XL => let '(X @ L) := XL in B) A)
  (at level 200, X ident, L ident, A at level 100, B at level 200).

Notation "'do!' X @ 'REG' <- A ; B" :=
  (bind (fun XREG => match XREG with | X @ REG => B | _ => None end) A)
  (at level 200, X ident, A at level 100, B at level 200).

Notation "'do!' X @ 'DATA' c I W <- A ; B" :=
  (bind (fun XcIW => match XcIW with | X @ (DATA c I W) => B | _ => None end) A)
  (at level 200, X ident, c ident, I ident, W ident,
   A at level 100, B at level 200).

Notation "'do!' 'REG' <- A ; B" :=
  (bind (fun maybeREG => match maybeREG with | REG => B | _ => None end) A)
  (at level 200, A at level 100, B at level 200).

Notation "'do!' 'DATA' c I W <- A ; B" :=
  (bind (fun cIW => match cIW with | DATA c I W => B | _ => None end) A)
  (at level 200, c ident, I ident, W ident, A at level 100, B at level 200).

Notation "'do!' 'REG' <-! A ; B" :=
  (match A with | REG => B | _ => None end)
  (at level 200, A at level 100, B at level 200).

Notation "'do!' 'DATA' c I W <-! A ; B" :=
  (match A with | DATA c I W => B | _ => None end)
  (at level 200, c ident, I ident, W ident, A at level 100, B at level 200).

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
    | p :: ps' => do! x @ L          <-  get M p;
                  do! x @ DATA c I W <-  get M p;
                  do! guard (ok c I W);
                  do! DATA _ I' W'   <-! retag c I W;
                  do! si'            <-  register_set I' si;
                  do! si''           <-  register_set W' si;
                  do! M'             <-  upd M p (x @ L);
                  retag_set ok retag ps' M' si''
  end.

Definition isolate (s : Symbolic.state t) : option (Symbolic.state t) :=
  match s with
    | Symbolic.State M R (pc @ (PC _ c)) si =>
      do! (c',si') <- fresh si;
      
      do! pA @ _ <- get R rIsoA;
      do! pJ @ _ <- get R rIsoJ;
      do! pS @ _ <- get R rIsoS;
      
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
                                J' MJ siJ;

      Some (Symbolic.State MS R ((pc + 1)%w @ (PC INTERNAL c)) siS)
    | _ => None
  end.

Definition add_to_jump_targets (s : Symbolic.state t)
                               : option (Symbolic.state t) :=
  match s with
    | Symbolic.State M R (pc @ (PC _ c)) si =>
      do! p @ _           <- get R rAdd;
      do! x @ DATA c' I W <- get M p;
      let I'              := insert_unique c I in
      do! si'             <- register_set I' si;
      do! M'              <- upd M p (x @ (DATA c' I' W));
      Some (Symbolic.State M' R ((pc + 1)%w @ (PC INTERNAL c)) si')
    | _ => None
  end.

Definition add_to_shared_memory (s : Symbolic.state t)
                                : option (Symbolic.state t) :=
  match s with
    | Symbolic.State M R (pc @ (PC _ c)) si =>
      do! p @ _           <- get R rAdd;
      do! x @ DATA c' I W <- get M p;
      let W'              := insert_unique c W in
      do! si'             <- register_set W' si;
      do! M'              <- upd M p (x @ (DATA c' I W'));
      Some (Symbolic.State M' R ((pc + 1)%w @ (PC INTERNAL c)) si')
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
    | _ => true (* or false *)
  end.

(* good_internal & interned_tag -> all lists are sets *)

Definition good_tags (s : Symbolic.state t) : Prop :=
  let: Symbolic.State M R pc si := s in
  (forall p v, get M p = Some v -> stag_is_DATA (common.tag v) &&
                                   interned_tag (set_ids si) (common.tag v)) /\
  (forall r v, get R r = Some v -> stag_is_REG  (common.tag v)) /\
  stag_is_PC (common.tag pc).

Definition good_state (s : Symbolic.state t) : Prop :=
  good_tags s /\ good_internal (Symbolic.internal s).  

End WithClasses.

End Sym.
