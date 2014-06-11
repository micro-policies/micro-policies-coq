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

Definition refine_val_atom (v : AbsSeal.value t)
                           (a : atom (word t) SymSeal.stag) : Prop :=
  match v,a with
  | AbsSeal.VData w    , w'@(SymSeal.DATA)      => w = w'
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
  | w'@SymSeal.DATA => w = w'
  | _               => False
  end.

Variable min_key : key. (* the initial key for the symbolic machine *)

(* Instantiating mkkey_f at abstract level to something
   corresponding to what's happening at the symbolic level. *)

(* Alternative 1 *)
Variable key_lt : key -> key -> bool.
Definition kmax (ks : list key) : key :=
   List.fold_left (fun kmax k => if key_lt kmax k then k else kmax) ks min_key.

Definition inc_key_opt k :=
  if k == max_key then None
                  else Some (inc_key k).

Import DoNotation.

Definition mkkey_f1 (ks : list key) : option (list key * key) :=
  do k <- inc_key_opt (kmax ks);
  Some (k::ks,k).

(* Alternative 2: assuming we start with empty list and key_min;
   doesn't seem to help so much -- ordering still needed in the
   key_generator instance proof *)

Definition mkkey_f2 (ks : list key) : option (list key * key) :=
  do k' <- (match ks with
            | []     => Some min_key
            | k :: _ => inc_key_opt k
            end);
  Some (k'::ks, k').

Variable inc_different : forall k, ~(k = inc_key k).

Program Instance gk_instance2 : AbsSeal.key_generator := {
  mkkey_f := mkkey_f2
}.
Next Obligation.
  unfold mkkey_f2 in *. destruct ks as [| k' ks].
  - simpl in *. inversion H; subst. unfold incl. simpl. tauto.
  - unfold inc_key_opt in *.
    destruct (equiv_dec k' max_key); simpl in *. discriminate H.
    inversion H; subst. unfold incl; simpl.
    split. intros [Hc | Hc]. eapply inc_different; eassumption.
    admit. (* this seems to rely on keys being _ordered_;
              we would probably need to make it part of the list key
              type (refinement) ... not much better than computing max *)
    split; tauto.
Admitted.

Definition refine_ins (keys : list key) (next_key : key) : Prop :=
  match mkkey_f2 keys with
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
