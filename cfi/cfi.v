Require Import List.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Require Import lib.utils common.common.

Set Implicit Arguments.

Import ListNotations.

Section CFI.  
  
Context (t : machine_types).
Context {ops : machine_ops t}.

Local Notation word := (word t).

Class cfi_machine := {
  state : Type;
  initial : state -> Prop;
  
  step : state -> state -> Prop;
  step_a : state -> state -> Prop;

  get_pc : state -> word;
  attacker_pc : forall s s', step_a s s' -> get_pc s = get_pc s';
  
  succ : state -> state -> bool       
}.

Context (cfim : cfi_machine).

(* Definitions regarding stepping relations for CFI *)
Definition cfi_step st st' := step_a st st' \/ step st st'.

Definition intermstep := interm cfi_step.

Definition intermrstep := intermr cfi_step.

Definition singlestep := single cfi_step.

Hypothesis exists_initial : exists s, initial s.

(* Execution will stop *)
Variable S : list state -> Prop.

(* Old definition of CFI (Abadi) *)
Definition trace_has_cfi' (trace : list state) := 
  forall (si sj : state)
         (INTRACE : In2 si sj trace ),
             (step_a si sj /\ get_pc si = get_pc sj) 
          \/ succ si sj = true.

(* New CFI definition *)
Definition trace_has_cfi (trace : list state) := 
  forall (si sj : state)
         (INTRACE : In2 si sj trace ),
           step si sj -> succ si sj = true.

Definition cfi := 
  forall s s' xs
    (INIT : initial s)
    (INTERM : intermstep xs s s'),
      trace_has_cfi xs \/
      (* the next part causes the most complexity in proofs *)
      exists s'' s''' hs tl, xs = hs ++ s'' :: s''' :: tl
                             /\ (step s'' s''' /\ succ s'' s''' = false)
                             /\ trace_has_cfi (hs ++ [s''])
                             /\ trace_has_cfi (s''' :: tl)
                             /\ S(s''' :: tl).

End CFI.
