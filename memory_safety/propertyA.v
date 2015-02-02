Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool.
Require Import Ssreflect.ssrnat Ssreflect.seq Ssreflect.eqtype.

Require Import CoqUtils.ord CoqUtils.word CoqUtils.partmap.

Require Import lib.utils common.types.
Require Import memory_safety.property memory_safety.abstract.
Require Import memory_safety.classes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section MemorySafety.

Variable mt : machine_types.
Variable ops : machine_ops mt.
Variable sr : syscall_regs mt.
Variable block : ordType.
Variable allocator : Abstract.allocator mt block.
Variable addrs : memory_syscall_addrs mt.

Local Notation state := (Abstract.state mt block).
Local Notation pointer := [eqType of Abstract.pointer mt block].

Definition get_events (s : state) : seq (event pointer block) :=
  match Abstract.pc s with
  | Abstract.VData _ => [::]
  | Abstract.VPtr ptr =>
    match Abstract.getv (Abstract.mem s) ptr with
    | Some (Abstract.VData i) =>
      match decode_instr i with
      | Some (Load r1 r2) =>
        match Abstract.regs s r1 with
        | Some (Abstract.VPtr ptr') => [:: MemRead ptr ptr.1; MemRead ptr' ptr'.1]
        | _ => [:: MemRead ptr ptr.1]
        end
      | Some (Store r1 r2) =>
        match Abstract.regs s r2 with
        | Some (Abstract.VPtr ptr') => [:: MemRead ptr ptr.1; MemWrite ptr' ptr'.1]
        | _ => [:: MemRead ptr ptr.1]
        end
      | _ => [:: MemRead ptr ptr.1]
      end
    | _ => [:: MemRead ptr ptr.1]
    end
  end.

Definition abstract_msm : memory_safety_machine :=
  @MSMachine [eqType of state] pointer block (fun ptr b => ptr.1 == b)
             get_events (fun s s' => Abstract.step s s').

Lemma abstract_machine_has_memory_safety : memory_safety abstract_msm.
Proof.
move=> t x y H.
elim: t x y / H=> [s|s s' s'' ss] /=.
  rewrite cats0 /get_events.
  case pcE: (Abstract.pc s) => [?|ptr] //=.
  case iE: (Abstract.getv _ _)=> [[i|?]|] //=; try by rewrite eqxx.
  case instrE: (decode_instr i)=> [[]|]; try by move => *; rewrite /= eqxx.
    case: (Abstract.regs s _)=> [[]|]; by move=> *; rewrite /= !eqxx.
  case: (Abstract.regs s _)=> [[]|]; by move=> *; rewrite /= !eqxx.
rewrite all_cat => _ _ ->.
rewrite /get_events.
case pcE: (Abstract.pc s) => [?|ptr] //=.
case iE: (Abstract.getv _ _)=> [[i|?]|] //=; try by rewrite eqxx.
case instrE: (decode_instr i)=> [[]|]; try by move => *; rewrite /= eqxx.
  case: (Abstract.regs s _)=> [[]|]; by move=> *; rewrite /= !eqxx.
case: (Abstract.regs s _)=> [[]|]; by move=> *; rewrite /= !eqxx.
Qed.

End MemorySafety.
