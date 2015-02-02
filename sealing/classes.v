Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.ssrnat.
Require Import common.types.

Class sealing_syscall_addrs mt := {
  mkkey_addr  : mword mt;
  seal_addr   : mword mt;
  unseal_addr : mword mt
}.
