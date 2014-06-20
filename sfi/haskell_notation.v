Require Import lib.utils.

(* Monadic function composition *)
Definition opt_compose {A B C}
                       (f : B -> option C)
                       (g : A -> option B)
                       : A -> option C :=
  bind f ∘ g.
Infix "<=<" := opt_compose (at level 30).
Arguments opt_compose {A B C} f g / x.

Infix "$"   := (fun f x => f x) (at level 150, left associativity).
Infix "<$>" := option_map       (at level 130, left associativity).
Infix "=<<" := bind             (at level 130, left associativity).
