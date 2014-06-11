Require Import utils common symbolic.
Require Import symbolic_sealing sealing.classes sealing.abstract.

Section RefinementSA.

Context {t : machine_types}
        {ops : machine_ops t}
        {opss : machine_ops_spec ops}

        {sk : sealing_key}
        {sko : sealing_key_ops}

        {scr : @syscall_regs t}
        {ssa : @sealing_syscall_addrs t}

        {smemory : Type}
        {sm : @partial_map smemory (word t) (atom (word t) SymSeal.stag)}
        {smems : partial_map_spec sm}

        {sregisters : Type}
        {sr : @partial_map sregisters (reg t) (atom (word t) SymSeal.stag)}
        {sregs : partial_map_spec sr}

        {amemory : Type}
        {am : @partial_map amemory (word t) (AbsSeal.value t)}
        {amems : partial_map_spec am}

        {aregisters : Type}
        {ar : @partial_map aregisters (reg t) (AbsSeal.value t)}
        {aregs : partial_map_spec ar}.

Definition refine_val_atom (v : AbsSeal.value t)
                           (a : atom (word t) SymSeal.stag) : Prop :=
  match v,a with
  | AbsSeal.VWord w    , w'@WORD                => w = w'
  | AbsSeal.VKey k     ,  _@(SymSeal.KEY k')    => k = k'
  | AbsSeal.VSealed w k, w'@(SymSeal.SEALED k') => w = w' /\ k = k'
  | _                  , _                      => False
  end.

Definition refine_mem (amem : amemory) (smem : smemory) : Prop :=
  forall w, is_some (get amem w) = is_some (get smem w) /\
  forall w v a,
    get amem w = Some v ->
    get smem w = Some a ->
    refine_val_atom v a.

Definition refine_reg (areg : aregisters) (sreg : sregisters) : Prop :=
  forall w, is_some (get areg w) = is_some (get sreg w) /\
  forall w v a,
    get areg w = Some v ->
    get sreg w = Some a ->
    refine_val_atom v a.

Definition refine_pc (w : word t) (a : atom (word t) SymSeal.stag) : Prop :=
  match a with
  | w'@SymSeal.WORD => w = w'
  | _               => False
  end.

Definition refine_ins (keys : list key) (next_key : key) : Prop :=
True.

Definition astate := @AbsSeal.state t sk amemory aregisters.
Definition sstate := @Symbolic.state t SymSeal.sym_sealing.

Definition refine_state (ast : astate) (sst : sstate) : Prop :=
  let '(AbsSeal.State amem areg apc akeys) := ast in
  let '(Symbolic.State smem sreg spc skey) := sst in
  refine_mem amem smem /\
  refine_reg areg sreg /\
  refine_pc apc spc /\
  refine_ins akeys skey.

(* Should instantiate mkkey_f at abstract level to something
   corresponding to what's happening at the symbolic level,
   and provide a key_generator instance (prove mkkey_fresh) *)

(* also refinement for our 3 system calls ... the abstract ones only
   have a description as step rules *)

End RefinementSA.
