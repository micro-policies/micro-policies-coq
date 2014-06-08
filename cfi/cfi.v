Require Import List.
Require Import utils common.

Set Implicit Arguments.

Import ListNotations.

Section CFI.  
  
Context (t : machine_types).
Context {ops : machine_ops t}.

Local Notation word := (word t).
Local Notation "x .+1" := (add_word x (Z_to_word 1)) (at level 60).

Class cfi_machine := {
  state : Type;
  initial : state -> Prop;
  
  step : state -> state -> Prop;
  step_a : state -> state -> Prop;
  step_determ : forall s s' s'', step s s' -> step s s'' -> s' = s'';

  get_pc : state -> word;
  attacker_pc : forall s s', step_a s s' -> get_pc s = get_pc s';
  
  succ : state -> state -> bool                                                            
 }.

Context (cfim : cfi_machine).

(* Definitions regarding stepping relations for CFI*)
Definition cfi_step st st' := step_a st st' \/ step st st'.

Definition intermstep := interm cfi_step.

Definition intermrstep := intermr cfi_step.

Definition singlestep := single cfi_step.

Hypothesis exists_initial : exists s, initial s.

(* A violation occured *)
Variable V : state -> state ->  Prop.
(* Execution will stop *)
Variable S : list state -> Prop.

 (* Definition of CFI *)

Definition trace_has_cfi (trace : list state) := 
  forall (si sj : state)
         (INTRACE : In2 si sj trace ),
             (step_a si sj /\ get_pc si = get_pc sj) 
          \/ succ si sj = true.

Definition cfi' := 
  forall s s' xs
    (INIT : initial s)
    (INTERM : intermstep xs s s'),
      trace_has_cfi xs \/
      exists s'' s''' hs tl, xs = hs ++ s'' :: s''' :: tl
                             /\ V s'' s'''
                             /\ trace_has_cfi (hs ++ [s''])
                             /\ trace_has_cfi (s''' :: tl)
                             /\ S(s''' :: tl).

End CFI.