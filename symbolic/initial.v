Require Import lib.utils.
Require Import concrete.common.
Require Import concrete.concrete.
Require Import kernel.symbolic.

Set Implicit Arguments.

Module InitialSymbolic.

Import Symbolic.

Section Declarations.

Context (t : machine_types).
Context {op : machine_ops t}.
Context {ap : symbolic_params t}.

Inductive initial : @state t ap -> Prop :=
  is_initial : forall mem reg, initial (State mem reg (Z_to_word 0)).

End Declarations.

End InitialSymbolic.

Module InitialConcrete.

Import Concrete.

Require kernel.rules.
Module R := kernel.rules.

Section Declarations.

Context (t : machine_types).
Context {op : machine_ops t}.
Context {cp : concrete_params t}.

Require Import ZArith.
Open Scope nat_scope.
Open Scope Z_scope.

(* ASZ: These user-level maxima aren't defined in Concrete, but they're
   mentioned in Andrew's notes on an initial state. *)
Parameter max_user_address  : word t.
Parameter max_user_register : reg t.

Definition user_then_kernel {Ix                 : Type}
                            (lt le              : Ix -> Ix -> Prop)
                            (things             : Ix -> atom (word t) (word t))
                            (max_user max_total : Ix) :=
  forall i, (le i max_user -> tag (things i) <> TKernel) /\
            (lt max_user i -> le i max_total -> tag (things i) = TKernel).

(* ASZ: Fix this:
   - The max_* have all moved.
   - `word t`s aren't orderable.

Inductive initial : @state t cp -> Prop :=
  is_initial : forall mem regs tpc epc,
    user_then_kernel Z.lt Z.le mem  max_user_address  max_address  ->
    user_then_kernel lt   le   regs max_user_register max_register ->
    tpc <> TKernel                                                 ->
    initial (mkState mem regs
                     (compile_rules compile_tag R.ground_rules)
                     (Z_to_word 0)@tpc epc).

*)

End Declarations.

End InitialConcrete.

(*

Concrete machine is parameterized by:

max_address
max_register
fault_handler_start
fault_vector_address

with the constraints:
0 <= fault_handler_start <= max_address
0 <= fault_vector_address
fault_vector_address+8 <= max_address

*)

(* Symbolic machine is parameterized by:

max_address
max_register

*)

(*  Initial states:

Concrete machine:

parameterized by:
max_user_address
max_user_register
kernel_data_start
kernel_data_end
fault_handler_start
fault_handler_end

with the following constraints:

max_user_address >= 0
max_user_register <= max_register

fault_vector_address = max_user_address+1
fault_vector_address + 8 <= kernel_data_start
kernel_data_end < fault_handler_start
fault_handler_end <= max_address

- Addresses 0 through max_user_address are tagged User
- Addresses max_user_address+1 through max_address are tagged Kernel

- Memory payloads are arbitary

- pc = (0,User)

- epc = arbitrary

- registers 0 through max_user_register are tagged User, with arbitrary contents

- register max_user_register+1 through max_register are tagged Kernel
   This tagging should be maintained as an invariant.
   This way, these registers cannot be used by user code, so they
   are always available to the kernel to use as temporaries.
   when spilling user registers immediately upon entry to
   the fault handler.

- cache contains the ground rules

Symbolic machine:

- pc = 0

- registers 0 through max_register have arbitrary contents

- memory contents are arbitrary

Relation between concrete and symbolic machines:

parameterized by:
handler instruction sequence
initial handler data

Concrete.max_user_address = Symbolic.max_address
Concrete.max_user_register = Symbolic.register

Concrete.fault_handler_address through Concrete.fault_handler_end contain the handler
instruction sequence

Concrete.kernel_data_start through kernel_data_end contain the initial handler data

Payloads for Concrete addresses 0 through Concrete.max_user_address =
contents of Symbolic addresses 0 through Symbolic.max_address

Payloads for Concrete registers 0 through Concrete.max_user_register =
contents of Symbolic registers 0 through Symbolic.max_register.

*)
