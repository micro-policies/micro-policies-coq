(*
    why is the run with the current transfer function succeeding??
    write a less silly transfer function
    write better testing stuff
    fill in the syscall implementations
*)

Require Import List. Import ListNotations.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.SetoidDec.
Require Import ssreflect ssrfun eqtype ssrnat ssrbool.
Require Import lib.utils lib.partial_maps common.common.
Require Import concrete.concrete.
Require Import concrete.int_32.
Require Import symbolic.int_32.
Require Import sealing.symbolic.
Require Import symbolic.fault_handler.
Require Import sealing.abstract.
Require Import concrete.exec.
Require Import Integers.
Require Import Omega.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import DoNotation.

Module ConcreteSealing.

Section WithClasses.

Definition t := concrete_int_32_t.
Definition ops := concrete_int_32_ops.

Instance scr : @syscall_regs t := {|
  syscall_ret  := Int32.repr 20;
  syscall_arg1 := Int32.repr 21;
  syscall_arg2 := Int32.repr 22
|}.

(* BCP/MD: There should be some proof obligations about -- at least --
   these being pairwise distinct.  Some axioms must be false
   somewhere! *)
Instance fhp : fault_handler.fault_handler_params t := {|
  rop := Int32.repr 1; 
  rtpc := Int32.repr 2; 
  rti := Int32.repr 3; rt1 := Int32.repr 4; rt2 := Int32.repr 5; 
  rt3 := Int32.repr 6; 
  rb := Int32.repr 7; 
  ri1 := Int32.repr 8; ri2 := Int32.repr 9; ri3 := Int32.repr 10; 
  ri4 := Int32.repr 11; ri5 := Int32.repr 12; 
  rtrpc := Int32.repr 13; rtr := Int32.repr 14; 
  raddr := Int32.repr 15; 
  rra := Int32.repr 16;

  load_const := fun (x : word t) (r : reg t) =>
    [Const _ (Z_to_imm (word_to_Z x)) r]
|}.

Definition keytype := [eqType of nat].

Definition max_element (l : list keytype) : keytype :=
  fold_right maxn O l.

Lemma max_element_plus_one_is_distinct :
  forall (l : list keytype),
    ~(In (1 + max_element l) l).
Proof.
  move => l.
  have MAX: forall x, In x l -> x <= max_element l.
  { elim: l => [|x' l IH] // x [-> | THERE] //=.
    - by rewrite leq_max leqnn.
    - by rewrite leq_max IH //= orb_true_r. }
  move => CONTRA.
  move: (MAX _ CONTRA).
  rewrite /addn /addn_rec.
  move/leP => LE.
  omega.
Qed.

Instance sk : Abs.sealing_key := {|
  key := keytype;
  mkkey_f := fun l => 1 + max_element l;
  mkkey_fresh := max_element_plus_one_is_distinct
|}.

(* Minor: Why do PartMaps.get and PartMaps.set take their arguments in
   a different order from Int32PMap.get and Int32PMap.set?? *)

(*
Instance ap : Abs.params t := {|
  memory    := Int32PMap.t (Abs.value t);
  registers := Int32PMap.t (Abs.value t);

  am := {|
    PartMaps.get mem i := Int32PMap.get i mem;
    PartMaps.set mem i x := Int32PMap.set i x mem;
    PartMaps.upd mem i x := match Int32PMap.get i mem with
                              | Some _ => Some (Int32PMap.set i x mem)
                              | None   => None
                            end
  |};

  ar := {|
    PartMaps.get regs r := Int32PMap.get r regs;
    PartMaps.set mem i x := Int32PMap.set i x mem;
    PartMaps.upd regs r x := match Int32PMap.get r regs with
                              | Some _ => Some (Int32PMap.set r x regs)
                              | None   => None
                            end
  |}
|}.
*)

Instance cp : Concrete.concrete_params t := {|
  memory    := Int32PMap.t atom;
  registers := Int32TMap.t atom;

  mem_class := {|
    PartMaps.get mem i := Int32PMap.get i mem;
    PartMaps.set mem i x := Int32PMap.set i x mem;
    PartMaps.upd mem i x := match Int32PMap.get i mem with
                              | Some _ => Some (Int32PMap.set i x mem)
                              | None   => None
                            end
  |};

  reg_class := {|
    TotalMaps.get regs r := Int32TMap.get r regs;
    (* BCP/MD: Why isn't this called 'set'? *)
    TotalMaps.upd regs r x := Int32TMap.set r x regs
  |}
|}.


(* Need to build...

   - encoding of tags

       DATA      --> 0
       KEY(k)    --> k*4+1
       SEALED(k) --> k*4+3

   - concrete transfer function (with combinators)

       basically we just check that things are tagged DATA (unless
       they are only being copied around)

   - three system call routines

       MKKEY: increment the extra state and return the old value (as a KEY)

       SEAL: move a tag KEY(k) from one atom to another (currently
       marked DATA, afterwards marked SEAL(k))

       UNSEAL: check that the tag of one arg is KEY(k) and the other
       is SEAL(k) and then change the latter to DATA.

   - fixpoint implementation of concrete step function
     (with proof of correctness)

*)

(* ---------------------------------------------------------------- *)
(* Code combinators... *)

Definition kernel_data {X} l : @relocatable_segment t X w := 
  (length l, fun _ _ => l).

Definition kernel_code {X} l : @relocatable_segment t X w := 
  (length l, 
   fun _ _ => map encode_instr l).

Definition user_code {X} l : @relocatable_segment t X atom := 
  (length l, 
   fun _ _ => 
     map (fun x => Atom (encode_instr x) Concrete.TKernel)  l).

(* ---------------------------------------------------------------- *)
(* Main definitions *)

(* Axiom fault_handler : @relocatable_segment t w atom.  *)

Definition transfer_function : list (instr t) :=
  []. (* TODO *)

Definition fault_handler : @relocatable_segment t w w :=
  kernel_code (handler t ops fhp transfer_function).

Definition extra_state : @relocatable_segment t w w := 
  kernel_data [nat_to_word 0].

Instance sk_defs : Sym.sealing_key := {|
  key := int_eqType;
  max_key := Int32.repr 100;
  inc_key := fun x => Int32.add x (Int32.repr 1);
  ord_key := int_ordered
|}.
admit.
Defined.

Definition encode_sealing_tag (t : Sym.stag) : w := 
  match t with
    Sym.DATA => Z_to_word 0
  | Sym.KEY k => add_word (Int32.repr 1) (Int32.shl k (Int32.repr 2))
  | Sym.SEALED k => add_word (Int32.repr 3) (Int32.shl k (Int32.repr 2))
  end.

Definition gen_syscall_code gen : @relocatable_segment t w w :=
  (length (gen (Int32.repr 0) (Int32.repr 0)), 
   fun b w => map encode_instr (gen b w)).

Definition mkkey_segment : @relocatable_segment t w w :=
  gen_syscall_code (fun _ (extra : w) => [
          (* TODO: too many numeric types! *)
          Const _ (Z_to_imm (word_to_Z extra)) (ri1 t);
          Load _ (ri1 t) (ri2 t);
          (* TODO: More here! *)
          Jump _ (rra t)
          ]).

Definition seal_segment : @relocatable_segment t w w :=
  gen_syscall_code (fun _ (extra : w) => [
          (* TODO: More here! *)
          Jump _ (rra t)
          ]).

Definition unseal_segment : @relocatable_segment t w w :=
  gen_syscall_code (fun _ (extra : w) => [
          (* TODO: More here! *)
          Jump _ (rra t)
          ]).

Definition build_concrete_sealing_machine 
     (user_mem : @relocatable_segment t unit atom) 
   : Concrete.state concrete_int_32_t :=
  let syscalls :=
    concat_relocatable_segments
      mkkey_segment
      (concat_relocatable_segments seal_segment unseal_segment) in
  let handler_and_syscalls :=
    concat_relocatable_segments fault_handler syscalls in
  initial_state
    extra_state
    handler_and_syscalls
    (@relocate_ignore_args t w atom user_mem)
    (encode_sealing_tag Sym.DATA).

Definition hello_world : @relocatable_segment t unit atom :=
  user_code [
    Const t (Z_to_imm 2) (Int32.repr 25);
    Binop t ADD (Int32.repr 25) (Int32.repr 25) (Int32.repr 26)
  ].

Definition hello_world2 : @relocatable_segment t unit atom :=
  user_code [
    Binop t ADD (Int32.repr 25) (Int32.repr 25) (Int32.repr 26)
  ].

Import Concrete.

(* BCP: Maybe these should come from rules.v? *)
Definition less_trivial_masks : Concrete.Masks :=
  let mk_mask dcm cm :=
      let '(dcm_tcp,dcm_ti,dcm_t1,dcm_t2,dcm_t3) := dcm in
      let '(cm_trpc,cm_tr) := cm in
      Concrete.Build_Mask
        (fun mvp =>
           match mvp with
             | mvp_tpc => dcm_tcp
             | mvp_ti => dcm_ti
             | mvp_t1 => dcm_t1
             | mvp_t2 => dcm_t2
             | mvp_t3 => dcm_t3
           end)
         (Concrete.mkCTMask cm_trpc cm_tr) in
  fun kernel opcode =>
    if kernel then
      match opcode with
        | NOP => mk_mask (false,false,true,true,true) (Some mvp_tpc,None)
        | CONST =>  mk_mask (false,false,true,true,true) (Some mvp_tpc,None)
        | MOV => mk_mask (false,false,true,true,true) (Some mvp_tpc,Some mvp_t1)
        | BINOP _ => mk_mask (false,false,true,true,true) (Some mvp_tpc,None)
        | LOAD =>  mk_mask (false,false,true,true,true) (Some mvp_tpc,Some mvp_t2)  (* unclear whether copy-through is useful, but seems harmless enough *)
        | STORE => mk_mask (false,false,true,true,true) (Some mvp_tpc,Some mvp_t2)
        | JUMP => mk_mask (false,false,true,true,true) (Some mvp_t1,None)
        | BNZ => mk_mask (false,false,true,true,true) (Some mvp_tpc,None)
        | JAL => mk_mask (false,false,true,true,true) (Some mvp_t1,Some mvp_tpc)
        | JUMPEPC => mk_mask (false,false,true,true,true) (Some mvp_t1,None)
        | ADDRULE => mk_mask (false,false,true,true,true) (Some mvp_tpc,None)
        | GETTAG => mk_mask (false,false,true,true,true) (Some mvp_tpc,None)
        | PUTTAG => mk_mask (false,false,true,true,true) (Some mvp_tpc,None)
        | HALT => mk_mask (false,false,false,false,false) (None,None)
        | SERVICE => mk_mask (false,false,false,false,false) (None,None)
      end
    else
      match opcode with
        | NOP => mk_mask (false,false,true,true,true) (None,None)
        | CONST =>  mk_mask (false,false,false,true,true) (None,None)
        | MOV => mk_mask (false,false,false,false,true) (None,None)
        | BINOP _ => mk_mask (false,false,false,false,false) (None,None)
        | LOAD =>  mk_mask (false,false,false,false,false) (None,None)
        | STORE => mk_mask (false,false,false,false,false) (None,None)
        | JUMP => mk_mask (false,false,false,true,true) (None,None)
        | BNZ => mk_mask (false,false,false,true,true) (None,None)
        | JAL => mk_mask (false,false,false,false,true) (None,None)
        | JUMPEPC => mk_mask (false,false,true,true,true) (None,None)
        | ADDRULE => mk_mask (false,false,true,true,true) (None,None)
        | GETTAG => mk_mask (false,false,false,false,true) (None,None)
        | PUTTAG => mk_mask (false,false,false,false,false) (None,None)
        | HALT => mk_mask (false,false,false,false,false) (None,None)
        | SERVICE => mk_mask (false,false,false,false,false) (None,None)
      end
.
End WithClasses.

Definition eval_reg n (r : reg t) init :=
  match exec.stepn less_trivial_masks t n init with
  | Some st => Some (TotalMaps.get (Concrete.regs st) r)
  | None => None
  end.

Open Scope Z_scope.

Definition init := build_concrete_sealing_machine hello_world2.

Fixpoint enum (M R S : Type) (map : M) (get : M -> Int32.int -> R) (f : R -> S) (n : nat) (i : Int32.int) :=
  match n with
  | O => []
  | S p => (Int32.intval i, f (get map i)) :: enum map get f p (Int32.add i (Int32.repr 1))
  end.

Require Import String.
Import printing.

Definition format_atom atom :=
  let: w1@w2 := atom in 
    format_word w1 +++ ss "@" +++ format_word w2 +++
    match decode_instr w1 with
      Some i => ss " (" +++ format_instr i +++ ss ")"
    | None => sempty
    end.

Definition print_instr atom :=
  let: w1@w2 := atom in (Int32.intval w1, decode_instr w1, Int32.intval w2).

Definition print_atom atom :=
  let: w1@w2 := atom in (Int32.intval w1, Int32.intval w2).

Definition format_mvec l := 
  let os := match (Z_to_op (word_to_Z (@Concrete.cop (word t) l))) with
              Some o => format_opcode o
            | None => ss "<BAD OPCODE>"
            end in
   os 
   +++ ss " " +++
   format_word (@Concrete.ctpc (word t) l)
   +++ ss " " +++
   format_word (@Concrete.cti (word t) l)
   +++ ss " " +++
   format_word (@Concrete.ct1 (word t) l)
   +++ ss " " +++
   format_word (@Concrete.ct2 (word t) l)
   +++ ss " " +++
   format_word (@Concrete.ct3 (word t) l).

Definition format_rvec l := 
   format_word (@Concrete.ctrpc (word t) l)
   +++ ss " " +++
   format_word (@Concrete.ctr (word t) l).

Definition format_cache (c : Concrete.rules (word t)) :=
  map (fun l => let: (m,r) := l in to_string (format_mvec m +++ ss " => " +++ format_rvec r)) c.

Fixpoint filter_Somes {X Y} (l : list (X * option Y)) :=
  match l with
    [] => []
  | (_, None) :: l' => filter_Somes l'
  | (x, Some y) :: l' => (x,y) :: filter_Somes l'
  end.

Definition print_state (mem_start mem_end max_reg : nat) st :=
  let mem := filter_Somes 
               (@enum _ _ _ 
                 (@Concrete.mem t cp st) 
                 (@PartMaps.get _ Int32.int _ _) 
                 (@omap atom string (fun a => to_string (format_atom a)))
                 mem_end 
                 (* BCP: Surely this is not the right way to do this... *)
                 (Int32.repr (word_to_Z (nat_to_word mem_start)))) in 
  let regs := @enum _ _ _ 
                 (@Concrete.regs t cp st) 
                 (@TotalMaps.get _ Int32.int _ _) 
                 (fun a => to_string (format_atom a))
                 max_reg 
                 (* BCP: or this... *)
                 (Int32.repr (word_to_Z (nat_to_word 0))) in 
  (to_string (ss "PC = " +++ format_atom (Concrete.pc st)),
  "Registers = ", regs,
  "Memory = ", mem,
  "Cache: ", format_cache (Concrete.cache st)).

Definition print_res_state n init :=
  omap (print_state 0 30 30) (exec.stepn less_trivial_masks t n init).

Compute (print_res_state 19 (build_concrete_sealing_machine hello_world)).

(*
Compute (print_res_state 19 (build_concrete_sealing_machine hello_world)).
*)

(* BCP: One nontrivial issue here.  How do we find out the system call
addresses to use when instantiating the sealing machine?
Answer (roughly)...

Definition build_abstract_sealing_machine :=
  fun user_memory : ...
  let ... := build_concrete_sealing_machine ...
  Instance ...
  ... 
*)

(* TODO: Refinement proof from concrete to abstract instances *)

End ConcreteSealing.
