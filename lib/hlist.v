(* Heterogeneous lists. *)

Require Import Coq.Lists.List.
Import ListNotations.

Section HList.

Context {A : Type}.

Variable B : A -> Type.

Fixpoint hlist (ts : list A) : Type :=
  match ts with
  | [] => unit
  | t :: ts' => prod (B t) (hlist ts')
  end.

End HList.

Fixpoint hmap {A} {B1 B2 : A -> Type} {l : list A} (f : forall a, B1 a -> B2 a) :
  hlist B1 l -> hlist B2 l :=
  match l with
  | [] => fun _ => tt
  | x :: l' => fun h => (f x (fst h), hmap f (snd h))
  end.

Module HListNotations.
Notation "[]" := tt : hlist_scope.
Notation "h :: t" := (h, t) (at level 60, right associativity) : hlist_scope.
Notation " [ x ] " := (x :: [ ]) : hlist_scope.
Notation " [ x ; .. ; y ] " := (pair x .. (pair y tt) ..) : hlist_scope.
Open Scope hlist_scope.
End HListNotations.
