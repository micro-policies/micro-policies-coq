Require Import utils common symbolic.
Require Import symbolic_sealing sealing.classes sealing.abstract.

(* Print SymSeal. *)
(* Print AbsSeal. *)

Section RefinementSA.

Context {t : machine_types}
        {ops : machine_ops t}
        {opss : machine_ops_spec ops}
        {sk : sealing_key}
        {sko : sealing_key_ops}
        {scr : @syscall_regs t}
        {ssa : @sealing_syscall_addrs t}
        {ap : Symbolic.symbolic_params t}
        {smemory : Type}
        {sm : @partial_map smemory (word t) (atom (word t) SymSeal.stag)}
        {sregisters : Type}
        {sr : @partial_map sregisters (reg t) (atom (word t) SymSeal.stag)}
        {smems : partial_map_spec sm}
        {sregs : partial_map_spec sr}
(*        {kg : AbsSeal.key_generator} probably not an argument *)
        {amemory : Type}
        {am : @partial_map amemory (word t) (AbsSeal.value t)}
        {aregisters : Type}
        {ar : @partial_map aregisters (reg t) (AbsSeal.value t)}
        {amems : partial_map_spec am}
        {aregs : partial_map_spec ar}.

End RefinementSA.
