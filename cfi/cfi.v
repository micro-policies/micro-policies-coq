Require Import List.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Require Import lib.utils common.common.

Set Implicit Arguments.

Import ListNotations.

Section CFI.  
  
Context (t : machine_types).
Context {ops : machine_ops t}.

Local Notation word := (word t).
Local Notation "x .+1" := (add_word x (Z_to_word 1)).

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
Variable V : state -> state ->  Prop. (* TODO: Replace things with succ _ _ = false? *)
(* Execution will stop *)
Variable S : list state -> Prop.

 (* Definition of CFI *)

Definition trace_has_cfi' (trace : list state) := 
  forall (si sj : state)
         (INTRACE : In2 si sj trace ),
             (step_a si sj /\ get_pc si = get_pc sj) 
          \/ succ si sj = true.


(* New CFI definition *)
Definition trace_has_cfi (trace : list state) := 
  forall (si sj : state)
         (INTRACE : In2 si sj trace ),
             (* TODO: remove first conjunct *)
             (step_a si sj -> get_pc si = get_pc sj) /\
             (step si sj -> succ si sj = true).
(* 1. Expose attacker step refinement separately
      from normal step refinement
   2. Return to previous problems with self loops;
      maybe we don't need to expose visible steps
      after all ... :)
*)


Definition cfi := 
  forall s s' xs
    (INIT : initial s)
    (INTERM : intermstep xs s s'),
      trace_has_cfi xs \/
      (* the next part causes the most complexity in proofs *)
      exists s'' s''' hs tl, xs = hs ++ s'' :: s''' :: tl
                             /\ (step s'' s''' /\ V s'' s''')
                             /\ trace_has_cfi (hs ++ [s''])
                             /\ trace_has_cfi (s''' :: tl)
                             /\ S(s''' :: tl).

End CFI.