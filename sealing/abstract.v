Require Import List. Import ListNotations.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.SetoidDec.

Require Import utils common.

Set Implicit Arguments.

Module AbstractSealing.

Section WithClasses.

Context (t : machine_types).
Context {ops : machine_ops t}.

Class abstract_types := {
  memory : Type;
  registers : Type;
  
  key : Type;
  extra_state : Type
(* APT: It seems weird to abstract over extra_state at this machine level.
        Why not just be explicit about whatever concrete state is needed? *)
}.

Context {abt : abstract_types}.

Inductive value := 
| VWord : word t -> value
| VSealed : word t -> key -> value
| VKey : key -> value.

Class abstract_params := {
  get_mem : memory -> word t -> option value;
  upd_mem : memory -> word t -> value -> option memory;

  get_reg : registers -> reg t -> option value;
  upd_reg : registers -> reg t -> value -> option registers;

  mkkey_addr : word t;
  seal_addr : word t;
  unseal_addr : word t;

  syscall_ret : reg t;
  syscall_arg1 : reg t;
  syscall_arg2 : reg t
}.

Class params_spec (ap : abstract_params) := {
  mem_axioms :> PartMaps.axioms get_mem upd_mem;
  reg_axioms :> PartMaps.axioms get_reg upd_reg
}.

Context {ap : abstract_params}.

Open Scope word_scope.

Local Notation "x .+1" := (add_word x (Z_to_word 1)) (at level 60).

Record state := State {
  mem : memory;
  regs : registers;
  pc : word t;
  es : extra_state
}.

(* TODO BCP: At the moment, the symbolic sealing machine uses a
   concrete word for the extra state and generates keys just by
   incrementing it (and then applying a word->key function, supplied
   externally).  We need to decide what is the cleanest way to set
   this up.  (Looking at it right now, I don't see much reason for the
   extra generality.) *)
(* APT: +1 for being less general *)

Class key_generator := 
  { mkkey_f : extra_state -> option (extra_state * key) }.

Context `{key_generator}.

(* APT: mkkey_f seems badly under-specified, e.g., it might generate the same key twice.  *)
   
Definition syscall_addrs := [mkkey_addr; seal_addr; unseal_addr].

Notation "x '=?' y" := (x = Some y) (at level 99).

Definition decode_def mem pc :=
  match get_mem mem pc with
    | Some (VWord i) => decode_instr i
    | _              => None
  end.

Inductive decode_rel st mem reg pc es inst :=
| do_decode : forall i
                    (ST   : st = State mem reg pc es)
                    (PC   : get_mem mem pc =? VWord i)
                    (INST : decode_instr i =? inst),
               decode_rel st mem reg pc es inst.
           
Inductive step (st st' : state) : Prop :=
| step_nop :
  forall mem reg pc i es
         (ST : st = State mem reg pc es) (PC : get_mem mem pc =? VWord i)
    (INST : decode_instr i =? Nop _)
    (NEXT : st' = State mem reg (pc.+1) es),
         step st st'
| step_const :
  forall mem reg reg' pc i n r es
         (ST : st = State mem reg pc es) (PC : get_mem mem pc =? VWord i)
    (INST : decode_instr i =? Const _ n r)
    (UPD  : upd_reg reg r (VWord (imm_to_word n)) =? reg')
    (NEXT : st' = State mem reg' (pc.+1) es),
         step st st'
| step_mov :
  forall mem reg reg' pc i r1 v1 r2 es
         (ST : st = State mem reg pc es) (PC : get_mem mem pc =? VWord i)
    (INST : decode_instr i =? Mov _ r1 r2)
    (R1W  : get_reg reg r1 =? v1)
    (UPD  : upd_reg reg r2 v1 =? reg')
    (NEXT : st' = State mem reg' (pc.+1) es),
         step st st'
| step_binop :
  forall mem reg reg' pc i op r1 r2 r3 w1 w2 es
         (ST : st = State mem reg pc es) (PC : get_mem mem pc =? VWord i)
    (INST : decode_instr i =? Binop _ op r1 r2 r3)
    (R1W  : get_reg reg r1 =? VWord w1)
    (R2W  : get_reg reg r2 =? VWord w2)
    (UPD  : upd_reg reg r3 (VWord (binop_denote op w1 w2)) =? reg')
    (NEXT : st' = State mem reg' (pc.+1) es),
         step st st'
| step_load :
  forall mem reg reg' pc i r1 r2 w1 v2 es
         (ST : st = State mem reg pc es) (PC : get_mem mem pc =? VWord i)
    (INST : decode_instr i =? Load _ r1 r2)
    (R1W  : get_reg reg r1 =? VWord w1)
    (MEM1 : get_mem mem w1 =? v2)
    (UPD  : upd_reg reg r2 v2 =? reg')
    (NEXT : st' = State mem reg' (pc.+1) es),
         step st st'
| step_store :
  forall mem mem' reg pc i r1 r2 w1 v2 es
         (ST : st = State mem reg pc es) (PC : get_mem mem pc =? VWord i)
    (INST : decode_instr i =? Store _ r1 r2)
    (R1W  : get_reg reg r1 =? VWord w1)
    (R2W  : get_reg reg r2 =? v2)
    (UPDM : upd_mem mem w1 v2 =? mem')
    (NEXT : st' = State mem' reg (pc.+1) es),
         step st st'
| step_jump :
  forall mem reg pc i r w es
         (ST : st = State mem reg pc es) (PC : get_mem mem pc =? VWord i)
    (INST : decode_instr i =? Jump _ r)
    (RW   : get_reg reg r =? VWord w)
    (NEXT : st' = State mem reg w es),
         step st st'
| step_bnz :
  forall mem reg pc i r n w es
         (ST : st = State mem reg pc es) (PC : get_mem mem pc =? VWord i)
    (INST : decode_instr i =? Bnz _ r n)
    (RW   : get_reg reg r =? VWord w),
    let pc' := add_word pc (if w ==b Z_to_word 0
                            then Z_to_word 1 else imm_to_word n) in forall
    (NEXT : st' = State mem reg pc' es),
         step st st'
| step_jal :
  forall mem reg reg' pc i r w es
        (ST : st = State mem reg pc es) (PC : get_mem mem pc =? VWord i)
    (INST : decode_instr i =? Jal _ r)
    (RW   : get_reg reg r =? VWord w)
    (NOSC : ~In w syscall_addrs)
    (UPD  : upd_reg reg ra (VWord (pc.+1)) =? reg')
    (NEXT : st' = State mem reg' w es),
        step st st'
| step_mkkey :
  forall mem reg reg' pc i r es es' nk
         (ST : st = State mem reg pc es) (PC : get_mem mem pc =? VWord i)
    (INST : decode_instr i =? Jal _ r)
    (RW   : get_reg reg r =? VWord mkkey_addr)
    (GEN  : mkkey_f es =? (es',nk))
    (UPD  : upd_reg reg syscall_ret (VKey nk) =? reg')
    (NEXT : st' = State mem reg' pc es'),
         step st st'
| step_seal :
  forall mem reg reg' pc i r es payload key
         (ST : st = State mem reg pc es) (PC : get_mem mem pc =? VWord i)
    (INST : decode_instr i =? Jal _ r)
    (RW   : get_reg reg r =? VWord seal_addr)
    (R1   : get_reg reg syscall_arg1 =? VWord payload)
    (R2   : get_reg reg syscall_arg2 =? VKey key)
    (UPD  : upd_reg reg syscall_ret (VSealed payload key) =? reg')
    (NEXT : st' = State mem reg' pc es),
         step st st'
| step_unseal :
  forall mem reg reg' pc i r es payload key
         (ST : st = State mem reg pc es) (PC : get_mem mem pc =? VWord i)
    (INST : decode_instr i =? Jal _ r)
    (RW   : get_reg reg r =? VWord unseal_addr)
    (R1   : get_reg reg syscall_arg1 =? VSealed payload key)
    (R2   : get_reg reg syscall_arg2 =? VKey key)
    (UPD  : upd_reg reg syscall_ret (VWord payload) =? reg')
    (NEXT : st' = State mem reg' pc es),
               step st st'.

(* ASZ, BCP:
   
   (1) Why equalities (ST, NEXT) and "step st st'" instead of
       `step (State mem reg pc es) (State mem' reg' pc' es')'?  Is it to make
       the datatype have parameters instead of indices?  If so, why -- does this
       make induction easier?

       ANSWER: Yes, it makes reasoning easier.

   (2) What about using one of `decode_def' or `decode_rel' as above?  (Suitably
       renamed to just `decode'.)  This would clean up the step relation, but
       would it make proofs worse?

       ANSWER: We should do this.

   (3) Should system call steps be specified inductively in the relation (like
       here), or as functions (like in memory safety)?  What are the
       benefits/downsides (e.g., working with other system calls)?

   (4) Why type classes instead of functors?  What does this buy us, and what
       exactly will the final usage pattern look like?
*)

End WithClasses.

End AbstractSealing.
