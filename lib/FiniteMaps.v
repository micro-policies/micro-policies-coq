Require Import List.
Require Import lib.Coqlib lib.Maps lib.utils.

Set Implicit Arguments.

(* We're breaking from CompCert's convention and using Map to describe something
  without default values, because that's more intuitive.  However, I can't make
  it a TREE because the indexed type is not de-indexable.  (And making it
  round-trippable doesn't really work.) *)
Module FiniteMap (I : INDEXED_TYPE).
  Local Hint Resolve
    PTree.gempty PTree.gss PTree.gso PTree.gsspec PTree.gsident PTree.grs
      PTree.gro PTree.grspec
    PTree.beq_correct
    PTree.gmap PTree.gmap1
    PTree.gcombine PTree.combine_commut
    PTree.elements_correct PTree.elements_complete PTree.elements_keys_norepet
    PTree.fold_spec PTree.fold1_spec.

  Local Hint Resolve I.index_inj.

  Definition elt    : Type                                 := I.t.
  Definition elt_eq : forall a b : elt, {a = b} + {a <> b} := I.eq.

  Definition t     : Type -> Type         := PTree.t.
  Definition empty : forall A : Type, t A := PTree.empty.

  Definition get    (A : Type) : elt ->      t A -> option A :=
    @PTree.get    A ∘ I.index.
  Definition set    (A : Type) : elt -> A -> t A -> t A      :=
    @PTree.set    A ∘ I.index.
  Definition remove (A : Type) : elt ->      t A -> t A      :=
    @PTree.remove A ∘ I.index.

  Definition filter (A : Type) (p : A -> bool) : t A -> t A :=
    PTree.filter1 p.

  Local Ltac basic :=
    simpl in *;
    repeat unfold elt, elt_eq,
                  t, empty,
                  get, set, remove
           in *;
    simpl in *;
    try solve [eauto];
    intros;
    repeat match goal with
      |- context[I.eq ?i ?j] => destruct (I.eq i j)
    end;
    repeat subst;
    eauto.

  (* Basic tree properties: empty, get, set, and remove *)

  Theorem gempty : forall (A : Type) (i : elt),
    get i (empty A) = None.
  Proof. basic. Qed.

  Theorem gss : forall (A : Type) (i : elt) (x : A) (m : t A),
    get i (set i x m) = Some x.
  Proof. basic. Qed.

  Theorem gso : forall (A : Type) (i j : elt) (x : A) (m : t A),
    i <> j -> get i (set j x m) = get i m.
  Proof. basic. Qed.

  Theorem gsspec : forall (A : Type) (i j : elt) (x : A) (m : t A),
    get i (set j x m) = if elt_eq i j then Some x else get i m.
  Proof. basic. Qed.

  Theorem gsident : forall (A : Type) (i : elt) (m : t A) (v : A),
    get i m = Some v -> set i v m = m.
  Proof. basic. Qed.

  Theorem grs : forall (A : Type) (i : elt) (m : t A),
    get i (remove i m) = None.
  Proof. basic. Qed.

  Theorem gro : forall (A : Type) (i j : elt) (m : t A),
    i <> j -> get i (remove j m) = get i m.
  Proof. basic. Qed.

  Theorem grspec : forall (A : Type) (i j : elt) (m : t A),
    get i (remove j m) = if elt_eq i j then None else get i m.
  Proof. basic. Qed.

  Theorem gfilter {V} : forall (f : V -> bool) (m : t V) (k : elt),
                          get k (filter f m) = option_filter f (get k m).
  Proof. intros. apply PTree.gfilter1. Qed.

  (* Equality *)

  Definition beq : forall A : Type, (A -> A -> bool) -> t A -> t A -> bool :=
    PTree.beq.

  Theorem beq_sound : forall (A : Type) (eqA : A -> A -> bool) (m1 m2 : t A),
    beq eqA m1 m2 = true ->
    (forall (x : elt), match get x m1, get x m2 with
                         | None,    None    => True
                         | Some y1, Some y2 => eqA y1 y2 = true
                         | _,       _       => False
                       end).
  Proof.
    unfold beq; intros until 0; intros Hbeq.
    basic; rewrite PTree.beq_correct in Hbeq; specialize Hbeq with (I.index x).
    assumption.
  Qed.

  (* Mapping *)

  Definition map1 : forall A B : Type, (A -> B) -> t A -> t B := PTree.map1.

  Theorem gmap1 : forall (A B : Type) (f : A -> B) (i : elt) (m : t A),
    get i (map1 f m) = option_map f (get i m).
  Proof. basic. Qed.

  (* Combining *)

  Definition combine : forall A B C : Type,
                         (option A -> option B -> option C) ->
                         t A -> t B -> t C :=
    PTree.combine.

  Theorem gcombine : forall (A B C : Type)
                            (f : option A -> option B -> option C),
    f None None = None ->
    forall (m1 : t A) (m2 : t B) (i : elt),
      get i (combine f m1 m2) = f (get i m1) (get i m2).
  Proof. basic. Qed.

  Theorem combine_commut : forall (A B : Type)
                                  (f g : option A -> option A -> option B),
    (forall (i j : option A), f i j = g j i) ->
    forall (m1 m2 : t A), combine f m1 m2 = combine g m2 m1.
  Proof. basic. Qed.
End FiniteMap.

(* We don't reuse IMap because it isn't a MAP for no reason. *)
Module FiniteTotalMap (I : INDEXED_TYPE) <: MAP.
  Local Hint Resolve
    PMap.gi PMap.gss PMap.gso PMap.gsspec PMap.gsident PMap.set2 PMap.gmap.

  Local Hint Resolve I.index_inj.
  Definition elt    : Type                                 := I.t.
  Definition elt_eq : forall a b : elt, {a = b} + {a <> b} := I.eq.

  Definition t    : Type -> Type              := PMap.t.
  Definition init : forall A : Type, A -> t A := PMap.init.

  Definition get (A : Type) : elt ->      t A -> A   := @PMap.get A ∘ I.index.
  Definition set (A : Type) : elt -> A -> t A -> t A := @PMap.set A ∘ I.index.

  Local Ltac basic :=
    simpl in *;
    repeat unfold elt, elt_eq,
                  t, init,
                  get, set
           in *;
    simpl in *;
    try solve [eauto];
    intros;
    repeat match goal with
      |- context[I.eq ?i ?j] => destruct (I.eq i j)
    end;
    repeat subst;
    eauto.

  (* Basic map properties: init, get, and set *)

  Theorem gi : forall (A : Type) (i : elt) (x : A),
    get i (init x) = x.
  Proof. basic. Qed.

  Theorem gss : forall (A : Type) (i : elt) (x : A) (m : t A),
    get i (set i x m) = x.
  Proof. basic. Qed.

  Theorem gso : forall (A : Type) (i j : elt) (x : A) (m : t A),
    i <> j -> get i (set j x m) = get i m.
  Proof. basic. Qed.

  Theorem gsspec : forall (A : Type) (i j : elt) (x : A) (m : t A),
    get i (set j x m) = if I.eq i j then x else get i m.
  Proof. basic. Qed.

  Theorem gsident : forall (A : Type) (i j : elt) (m : t A),
    get j (set i (get i m) m) = get j m.
  Proof. basic. Qed.

  Theorem set2: forall (A : Type) (i : elt) (x y : A) (m : t A),
    set i y (set i x m) = set i y m.
  Proof. basic; eauto using PMap.set2. Qed.

  (* Mapping *)

  Definition map : forall A B : Type, (A -> B) -> t A -> t B := PMap.map.

  Theorem gmap : forall (A B : Type) (f : A -> B) (i : elt) (m : t A),
    get i (map f m) = f (get i m).
  Proof. basic. Qed.
End FiniteTotalMap.

(* ASZ: Is there a better way to re-export the modules themselves (_not_ their
   contents) than just defining them anew? *)

Module Type INDEXED_TYPE := INDEXED_TYPE.

Module ZIndexed := ZIndexed.
Module NIndexed := NIndexed.

Module PositiveIndexed <: INDEXED_TYPE.
  Definition t := positive.

  Definition index := @id positive.
  Arguments index /.

  Theorem index_inj : forall x y : positive, index x = index y -> x = y.
  Proof. auto. Qed.

  Definition eq := peq.
  Arguments eq /.
End PositiveIndexed.

Module NatIndexed <: INDEXED_TYPE.
  Definition t := nat.

  Definition index := Pos.of_nat ∘ S.
  Arguments index x /.
  Local Arguments Pos.of_nat n : simpl nomatch.

  Theorem index_inj : forall x y : nat, index x = index y -> x = y.
  Proof.
    simpl; intros x y Heq; apply Nat2Pos.inj in Heq;
      solve [discriminate | inversion Heq; auto].
  Qed.

  Definition eq := eq_nat_dec.
  Arguments eq_nat_dec /.
End NatIndexed.

Require Import Integers.

Module IntIndexed (WS : WORDSIZE) <: INDEXED_TYPE.
  Import WS.

  Definition t := Word.int wordsize_minus_one.

  Definition index : t -> positive := ZIndexed.index ∘ Word.unsigned.
  Arguments index x /.

  Lemma intval_inj : forall x y : t, Word.unsigned x = Word.unsigned y -> x = y.
  Proof.
    intros x y Hix; generalize (Word.eq_spec _ x y); intros Heq.
    unfold Word.eq, Word.unsigned in *.
    rewrite Hix, zeq_true in Heq.
    exact Heq.
  Qed.

  Theorem index_inj : forall x y, index x = index y -> x = y.
  Proof. auto using intval_inj, ZIndexed.index_inj. Qed.

  Definition eq : forall x y : t, {x = y} + {x <> y} := Word.eq_dec.
End IntIndexed.
