Require Import List. Import ListNotations.
Require Import Coq.Classes.SetoidDec.
Require Import utils common symbolic.
Require Import symbolic_sealing sealing.classes sealing.abstract.

Section RefinementSA.

Import PartMaps.

Context {t : machine_types}
        {ops : machine_ops t}
        {opss : machine_ops_spec ops}

        {sk : sealing_key}
        {sko : sealing_key_ops}

        {scr : @syscall_regs t}
        {ssa : @sealing_syscall_addrs t}

        {smemory : Type}
        {sm : partial_map smemory (word t) (atom (word t) SymSeal.stag)}
        {smems : axioms sm}

        {sregisters : Type}
        {sr : partial_map sregisters (reg t) (atom (word t) SymSeal.stag)}
        {sregs : axioms sr}

        {amemory : Type}
        {am : partial_map amemory (word t) (AbsSeal.value t)}
        {amems : axioms am}

        {aregisters : Type}
        {ar : partial_map aregisters (reg t) (AbsSeal.value t)}
        {aregs : axioms ar}.

(* At the moment we're considering identity mapping on keys;
   we could consider relaxing this in the future, and go in
   the direction of Maxime's "memory injections" *)
(* Could consider doing this in relational style (inductive relation) *)
Definition refine_val_atom (v : AbsSeal.value t)
                           (a : atom (word t) SymSeal.stag) : Prop :=
  match v,a with
  | AbsSeal.VData w    , w'@(SymSeal.DATA)      => w = w'
  | AbsSeal.VKey k     ,  _@(SymSeal.KEY k')    => k = k'
  | AbsSeal.VSealed w k, w'@(SymSeal.SEALED k') => w = w' /\ k = k'
  | _                  , _                      => False
  end.

Definition refine_mem (amem : amemory) (smem : smemory) : Prop :=
  forall w,
    match get amem w, get smem w with
    | None  , None   => True
    | Some v, Some a => refine_val_atom v a
    | _     , _      => False
    end.

Definition refine_reg (areg : aregisters) (sreg : sregisters) : Prop :=
  forall w,
    match get areg w, get sreg w with
    | None  , None   => True
    | Some v, Some a => refine_val_atom v a
    | _     , _      => False
    end.

Definition refine_pc (w : word t) (a : atom (word t) SymSeal.stag) : Prop :=
  match a with
  | w'@SymSeal.DATA => w = w'
  | _               => False
  end.

(* Instantiating mkkey_f at abstract level to something
   corresponding to what's happening at the symbolic level. *)

Variable min_key : key. (* the initial key for the symbolic machine *)
Variable key_lt : key -> key -> bool.

Definition kmax (ks : list key) : key :=
   List.fold_left (fun kmax k => if key_lt kmax k then k else kmax) ks min_key.

Definition inc_key_opt k :=
  if k == max_key then None
                  else Some (inc_key k).

Import DoNotation.

Definition mkkey_f (ks : list key) : option (list key * key) :=
  do k <- inc_key_opt (kmax ks);
  Some (k::ks,k).

Hypothesis inc_max_not_in : forall ks,
  kmax ks =/= max_key ->
   ~ In (inc_key (kmax ks)) ks.

Program Instance gen_key_inst : AbsSeal.key_generator := {
  mkkey_f := mkkey_f
}.
Next Obligation.
  unfold mkkey_f in *. unfold bind in H.
  remember (inc_key_opt (kmax ks)) as o. destruct o as [k'|].
  - inversion H. subst. split; [|split].
    + unfold inc_key_opt in *.
      destruct (equiv_dec (kmax ks) max_key). congruence.
      inversion Heqo. eauto using inc_max_not_in.
    + left; reflexivity.
    + right; assumption.
  - inversion H.
Qed.

Definition refine_ins (keys : list key) (next_key : key) : Prop :=
  match mkkey_f keys with
  | Some (_, k) => k = next_key
  | _           => True (* ??? *)
  end.

Definition astate := @AbsSeal.state t sk amemory aregisters.
Definition sstate := @Symbolic.state t SymSeal.sym_sealing.

Definition refine_state (ast : astate) (sst : sstate) : Prop :=
  let '(AbsSeal.State amem areg apc akeys) := ast in
  let '(Symbolic.State smem sreg spc skey) := sst in
  refine_mem amem smem /\
  refine_reg areg sreg /\
  refine_pc apc spc /\
  refine_ins akeys skey.

(* also refinement for our 3 system calls ... the abstract ones only
   have a description as step rules *)

End RefinementSA.
