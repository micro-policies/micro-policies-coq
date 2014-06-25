(*
    make sure user registers are tagged USER at the beginning!

    check that current behavior makes sense
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
Require Import symbolic.rules.
Require Import concrete.exec.
Require Import Integers.
Require Import Omega.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import DoNotation.

Module ConcreteSealing.

(* BCP: These belong someplace central *)
Definition Z_to_nat z := word_to_nat (Z_to_word z).
Definition word_to_imm w := Z_to_imm (word_to_Z w).

Section WithClasses.

Definition t := concrete_int_32_t.
Definition ops := concrete_int_32_ops.

(* BCP/MD: There should be some proof obligations about -- at least --
   these being pairwise distinct.  Some axioms must be false somewhere!   

   (And they should be distinct from the user registers below, though
   this should not cause axiom failures, just puzzling user program
   errors.)

   Also, it seems wrong to be making this decision here.  It should be
   made once and for all in symbolic/int_32.v, I think! *)

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

  load_const := fun (x : word t) (r : reg t) =>
    [Const _ (word_to_imm x) r]
|}.

Global Instance scr : @syscall_regs t := {|
  syscall_ret  := Int32.repr 16;
  syscall_arg1 := Int32.repr 17;
  syscall_arg2 := Int32.repr 18
|}.

Definition ruser1 := Int32.repr 19.
Definition ruser2 := Int32.repr 20.
Definition ruser3 := Int32.repr 21.
Definition ruser4 := Int32.repr 22.

Definition user_registers := 
  [ra; syscall_ret; syscall_arg1; syscall_arg2; ruser1; 
   ruser2; ruser3; ruser4].
Definition user_reg_max := last user_registers (Int32.repr 0).

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

Global Instance sk : Abs.sealing_key := {|
 key := keytype;
 mkkey_f := fun l => 1 + max_element l;
 mkkey_fresh := max_element_plus_one_is_distinct
|}.

Instance cp : Concrete.concrete_params t := {|
 memory    := Int32PMap.t atom;
 registers := Int32TMap.t atom;

 mem_class := {|
   PartMaps.get mem i := Int32PMap.get i mem;
   PartMaps.set mem i x := Int32PMap.set i x mem;
   PartMaps.filter mem p := Int32PMap.filter mem p;
   PartMaps.empty := @Int32PMap.empty _
 |};

 reg_class := {|
   TotalMaps.get regs r := Int32TMap.get r regs;
   (* BCP/MD: Why isn't this called 'set'? *)
   TotalMaps.upd regs r x := Int32TMap.set r x regs
 |}
|}.


(* ---------------------------------------------------------------- *)

(* Encoding of tags

      DATA      --> 0
      KEY(k)    --> k*4+1
      SEALED(k) --> k*4+3

 Questions:

  - How should we really deal with user-code registers
*)

Definition kernel_data {X} l : @relocatable_segment t X w := 
 (length l, fun _ _ => l).

Definition kernel_code {X} l : @relocatable_segment t X w := 
 (length l, 
  fun _ _ => map encode_instr l).

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

(* BCP: Arguably the second argument to f should be a list of immediates... *)
Definition user_code (f : w -> list w -> list (instr t))
                  : @relocatable_segment t (list w) (instr t) := 
 (* This is hideous.  Will totally break if we add more system calls. *)
 (length (f (Z_to_word 0) [Z_to_word 0; Z_to_word 0; Z_to_word 0]), 
  f).

(* ---------------------------------------------------------------- *)
(* Main definitions *)

(* TODO: THINGS TO CLEAN:
    - move code generation macros out of fault_handler.v
    - make a switch macro
    - check that there are no temp registers live across the transfer
      function call from the falut handler
    - the handling of the ut annotations on ENTRY tags
*)

Definition DATA := encode_sealing_tag Sym.DATA.

Definition transfer_function : list (instr t) :=
 let assert_DATA r := [
   Const _ (word_to_imm DATA) ri1;
   Binop _ EQ r ri1 ri1 ] ++
                          if_ ri1 [] [Halt _] 
   in
 (* entry points for system calls *)
 ([ Const _ (op_to_imm SERVICE) ri1;
    Binop _ EQ rop ri1 ri1 ] ++
  (if_ ri1 
    []
 (* NOP *)
 ([ Const _ (op_to_imm NOP) ri1;
    Binop _ EQ rop ri1 ri1 ] ++
  (if_ ri1 
    (assert_DATA rtpc ++ assert_DATA rti ++
     [Const _ (word_to_imm DATA) rtrpc;
      Const _ (word_to_imm DATA) rtr
     ])
 (* CONST *)
 ([ Const _ (op_to_imm CONST) ri1;
    Binop _ EQ rop ri1 ri1 ] ++
  (if_ ri1 
    (assert_DATA rtpc ++ assert_DATA rti ++
     [Const _ (word_to_imm DATA) rtrpc;
      Const _ (word_to_imm DATA) rtr
     ])
 (* MOV *)
 ([ Const _ (op_to_imm MOV) ri1;
    Binop _ EQ rop ri1 ri1 ] ++
  (if_ ri1 
    (assert_DATA rtpc ++ assert_DATA rti ++
     [Const _ (word_to_imm DATA) rtrpc;
      Mov _ rt1 rtr
     ])
 (* BINOPs *)
 (let binop cont b := 
        [ Const _ (op_to_imm (BINOP b)) ri1;
          Binop _ EQ rop ri1 ri1 ] ++
        (if_ ri1 
          (assert_DATA rtpc ++ assert_DATA rti ++
           assert_DATA rt1 ++ assert_DATA rt2 ++
           [Const _ (word_to_imm DATA) rtrpc;
            Const _ (word_to_imm DATA) rtr
           ]) 
          cont) in
   fold_left binop binops 
 (* LOAD *)
 ([ Const _ (op_to_imm LOAD) ri1;
    Binop _ EQ rop ri1 ri1 ] ++
  (if_ ri1 
    (assert_DATA rtpc ++ assert_DATA rti ++ assert_DATA rt1 ++
     [Const _ (word_to_imm DATA) rtrpc;
      Mov _ rt2 rtr
     ])
 (* STORE *)
 ([ Const _ (op_to_imm STORE) ri1;
    Binop _ EQ rop ri1 ri1 ] ++
  (if_ ri1 
    (assert_DATA rtpc ++ assert_DATA rti ++ assert_DATA rt1 ++
     [Const _ (word_to_imm DATA) rtrpc;
      Mov _ rt2 rtr
     ])
 (* JUMP *)
 ([ Const _ (op_to_imm JUMP) ri1;
    Binop _ EQ rop ri1 ri1 ] ++
  (if_ ri1 
    (assert_DATA rtpc ++ assert_DATA rti ++
     [Const _ (word_to_imm DATA) rtrpc])
 (* BNZ *)
 ([ Const _ (op_to_imm BNZ) ri1;
    Binop _ EQ rop ri1 ri1 ] ++
  (if_ ri1 
    (assert_DATA rtpc ++ assert_DATA rti ++ assert_DATA rt1 ++
     [Const _ (word_to_imm DATA) rtrpc])
 (* JAL *)
 ([ Const _ (op_to_imm JAL) ri1;
    Binop _ EQ rop ri1 ri1 ] ++
  (if_ ri1 
    (assert_DATA rtpc ++ assert_DATA rti ++ assert_DATA rt1 ++
     [Const _ (word_to_imm DATA) rtrpc;
      Const _ (word_to_imm DATA) rtr])
 (* Unknown opcode: Halt *)
 ([Halt _])))))))))))))))))))). 

Definition fault_handler : @relocatable_segment t w w :=
 kernel_code (fault_handler.handler t ops fhp transfer_function).

Definition extra_state : @relocatable_segment t w w := 
 kernel_data [nat_to_word 13].

Definition gen_syscall_code gen : @relocatable_segment t w w :=
 (length (gen (Int32.repr 0) (Int32.repr 0)), 
  fun b w => map encode_instr (gen b w)).

Definition mkkey_segment : @relocatable_segment t w w :=
 gen_syscall_code (fun _ (extra : w) =>
        [Const _ (word_to_imm extra) ri1; (* load next key *)
         Load _ ri1 ri5; 
         Const _ (Z_to_imm 1) ri3; (* increment and store back *)
         Binop _ ADD ri5 ri3 ri3;
         Store _ ri1 ri3; 
         Const _ (Z_to_imm 2) ri3; (* wrap k as KEY(k): SHL by 2 and add 1 *)
         Binop _ SHL ri5 ri3 ri4;
         Const _ (Z_to_imm 1) ri3;
         Binop _ ADD ri3 ri4 ri4] ++
        wrap_user_tag ri4 ri4 ++
        [Const _ (Z_to_imm 0) ri5; (* payload for new key is 0, arbitrarily *)
         PutTag _ ri5 ri4 syscall_ret; (* build the key *)
         Jump _ ra 
         ]).

Definition seal_segment : @relocatable_segment t w w :=
 gen_syscall_code (fun _ (extra : w) =>
       (* Ensure that first argument is tagged DATA, halting otherwise *)
       [GetTag _ syscall_arg1 ri3] ++
       extract_user_tag ri3 rb ri3 ++
       if_ rb [] [Halt _] ++
       [Const _ (Z_to_imm 3) ri5;
        Binop _ AND ri3 ri5 ri5] ++
       if_ ri5 [Halt _] [] ++
       (* Ensure that second argument is tagged KEY, halting otherwise *)
       [GetTag _ syscall_arg2 ri4] ++
       extract_user_tag ri4 rb ri4 ++
       if_ rb [] [Halt _] ++
       [Const _ (Z_to_imm 3) ri5;
        Binop _ AND ri4 ri5 ri2;
        Const _ (Z_to_imm 1) ri5;
        Binop _ EQ ri5 ri2 ri5] ++
       if_ ri5 [] [Halt _] ++
       (* Form SEALED(k) tag from KEY(k) in ri4 *)
       [Const _ (Z_to_imm 2) ri5;
        Binop _ OR ri5 ri4 ri4] ++
       wrap_user_tag ri4 ri4 ++
       [PutTag _ syscall_arg1 ri4 syscall_ret] ++
       (* Check that return PC is tagged DATA *)
       [GetTag _ ra ri3] ++
       extract_user_tag ri3 rb ri3 ++
       if_ rb [] [Halt _] ++
       [Const _ (Z_to_imm 0) ri5;
        Binop _ EQ ri3 ri5 ri5] ++
       if_ ri5 [Jump _ ra] [Halt _]
 ).

Definition unseal_segment : @relocatable_segment t w w :=
 gen_syscall_code (fun _ (extra : w) => 
       (* Ensure that second argument is tagged KEY, halting otherwise *)
       [GetTag _ syscall_arg2 ri4] ++
       extract_user_tag ri4 rb ri4 ++
       if_ rb [] [Halt _] ++
       [Const _ (Z_to_imm 3) ri5;
        Binop _ AND ri4 ri5 ri2;
        Const _ (Z_to_imm 1) ri5;
        Binop _ EQ ri5 ri2 ri5] ++
       if_ ri5 [] [Halt _] ++
       (* Form SEALED(k) tag from KEY(k) in ri4 *)
       [Const _ (Z_to_imm 2) ri5;
        Binop _ OR ri5 ri4 ri4] ++
       (* Ensure that first argument has a user tag (put it in ri3) *)
       [GetTag _ syscall_arg1 ri3] ++
       extract_user_tag ri3 rb ri3 ++
       if_ rb [] [Halt _] ++
       (* Check that the two tags are equal (i.e. both SEALED(k)) *)
       [Binop _ EQ ri3 ri4 ri4] ++
       if_ ri5 [] [Halt _] ++
       (* Retag the payload with DATA *)
       [Const _ (Z_to_imm 0) ri5] ++
       wrap_user_tag ri5 ri5 ++
       [PutTag _ syscall_arg1 ri5 syscall_ret] ++
       (* Check that return PC is tagged DATA *)
       (* (not certain this is needed, but keeping it here and above
           to make sure we satisfy refinement hypotheses...) *)
       [GetTag _ ra ri3] ++
       extract_user_tag ri3 rb ri3 ++
       if_ rb [] [Halt _] ++
       [Const _ (Z_to_imm 0) ri5;
        Binop _ EQ ri3 ri5 ri5] ++
       if_ ri5 [Jump _ ra] [Halt _]
).

Definition build_concrete_sealing_machine 
    (user_program : @relocatable_segment t (list w) (instr t))
  : Concrete.state concrete_int_32_t * (* Initial machine state *)
     w *                               (* Base addr for user code *)
     list w                            (* Syscall addrs *)
     :=
 (* This list should be defined at the same place as the decoding
    function that splits out the addresses for use when generating
    user code *)
 let user_mem := 
       map_relocatable_segment 
         (fun x => Atom (encode_instr x) (encode_sealing_tag Sym.DATA)) 
         user_program in
 let syscalls := [mkkey_segment; seal_segment; unseal_segment] in
 concrete_initial_state
   extra_state
   fault_handler
   syscalls
   user_mem
   (encode_sealing_tag Sym.DATA)
   user_registers
   (encode_sealing_tag Sym.DATA).

End WithClasses.

(* ------------------------------------------------------------------------- *)
(* Abstract machine *)

(* Minor: Why do PartMaps.get and PartMaps.set take their arguments in
  a different order from Int32PMap.get and Int32PMap.set?? *)

Instance ap : Abs.params t := {|
 memory    := Int32PMap.t (Abs.value t);
 registers := Int32PMap.t (Abs.value t);

 am := {|
   PartMaps.get mem i := Int32PMap.get i mem;
   PartMaps.set mem i x := Int32PMap.set i x mem;
   PartMaps.filter mem p := Int32PMap.filter mem p;
   PartMaps.empty := Int32PMap.empty _ 
 |};

 ar := {|
   PartMaps.get regs r := Int32PMap.get r regs;
   PartMaps.set mem i x := Int32PMap.set i x mem;
   PartMaps.filter mem p := Int32PMap.filter mem p;
   PartMaps.empty := Int32PMap.empty _ 
 |}
|}.

Definition build_abstract_sealing_machine 
    (user_program : @relocatable_segment t (list w) (instr t))
  : @Abs.state concrete_int_32_t sk ap * classes.sealing_syscall_addrs :=
 (* This list should be defined at the same place as the decoding
    function that splits out the addresses for use when generating
    user code *)
 let: (_,base_addr,syscall_addrs) := build_concrete_sealing_machine user_program in
 let user_mem := 
       map_relocatable_segment 
         ((@Abs.VData _ _) ∘ encode_instr)
         user_program in
  let syscall_addr_rcd := 
      {| 
        classes.mkkey_addr  := nth 0 syscall_addrs (Int32.repr 0);
        classes.seal_addr   := nth 1 syscall_addrs (Int32.repr 0);
        classes.unseal_addr := nth 2 syscall_addrs (Int32.repr 0)
      |} in
  (Abs.abstract_initial_state
    user_mem
    base_addr
    syscall_addrs
    user_registers,
   syscall_addr_rcd).

(* ------------------------------------------------------------------------- *)

Open Scope Z_scope.

Fixpoint enum (M R S : Type) (map : M) (get : M -> Int32.int -> R) (f : R -> S) (n : nat) (i : Int32.int) :=
  match n with
  | O => []
  | S p => (Int32.intval i, f (get map i)) :: enum map get f p (Int32.add i (Int32.repr 1))
  end.

Require Import String.
Import printing.

Definition format_atom atom :=
  let: w1@w2 := atom in 
    match decode_instr w1 with
      Some i => ss "(" +++ format_instr i +++ ss ")@" +++ format_word w2
    | None => format_word w1 +++ ss "@" +++ format_word w2
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
   +++ sspace +++
   format_word (@Concrete.ctpc (word t) l)
   +++ sspace +++
   format_word (@Concrete.cti (word t) l)
   +++ sspace +++
   format_word (@Concrete.ct1 (word t) l)
   +++ sspace +++
   format_word (@Concrete.ct2 (word t) l)
   +++ sspace +++
   format_word (@Concrete.ct3 (word t) l).

Definition format_rvec l := 
   format_word (@Concrete.ctrpc (word t) l)
   +++ sspace +++
   format_word (@Concrete.ctr (word t) l).

Definition format_whole_cache (c : Concrete.rules (word t)) :=
  map (fun l => let: (m,r) := l in (format_mvec m +++ ss " => " +++ format_rvec r)) c.

Definition format_cache (c : Concrete.rules (word t)) :=
  format_whole_cache (take 3 c).

Fixpoint filter_Somes {X Y} (l : list (X * option Y)) :=
  match l with
    [] => []
  | (_, None) :: l' => filter_Somes l'
  | (x, Some y) :: l' => (x,y) :: filter_Somes l'
  end.

Require Import Coqlib. (* Needed?? *)

Definition summarize_state mem_count cache_count st :=
  let mem' := filter_Somes 
               (@enum _ _ _ 
                 (@Concrete.mem t cp st) 
                 (@PartMaps.get _ Int32.int _ _) 
                 (@omap atom sstring format_atom)
                 mem_count
                 (Int32.repr 0)) in 
  let mem := ssconcat sspace (map (fun x => let: (addr,con) := x in format_Z addr +++ ss ":" +++ con) mem') in
  let regs' := @enum _ _ _ 
                 (@Concrete.regs t cp st) 
                 (@TotalMaps.get _ Int32.int _ _) 
                 (fun a => format_atom a)
                 (word_to_nat user_reg_max)
                 (Int32.repr (word_to_Z (nat_to_word 0))) in 
  let regs := map (fun r => 
                     let: (x,a) := r in 
                     ss "r" +++ format_nat (nat_of_Z x) +++ ss "=" +++ a) 
               regs' in
  let current_instr := 
    let: addr@_ := Concrete.pc st in
    match @PartMaps.get _ Int32.int _ _
                    (@Concrete.mem t cp st)
                    addr with
      None => ss "(BAD ADDR)"
    | Some i => format_atom i 
    end in
  (to_string 
     (ss "PC=" +++ format_atom (Concrete.pc st) +++ ss "  "
               +++ current_instr +++ 
      ss " | " +++ 
      ssconcat sspace regs +++
      ss " | " +++ 
      mem +++ 
      ss " | " +++ 
      ssconcat sspace (format_whole_cache 
                         (take cache_count (Concrete.cache st))))).

Definition runn n p := 
  let: (init,_,_) := build_concrete_sealing_machine p in
  let tr := utils.runn (step masks t) n init in
  (
   summarize_state 3000 1000 init ::
   map (summarize_state 8 1) tr
  ).

Definition run := runn 10000.

Definition run_abs n p := 
  let: (init,syscall_addrs) := build_abstract_sealing_machine p in
  let tr := utils.runn (fun x => Abs.stepf x) n init in
  (
(*
   summarize_state 3000 1000 init ::
   map (summarize_state 8 1) tr
*)
  init, tr
  ).


(* ---------------------------------------------------------------------- *)
(* Tests... *)

Definition hello_world0 : @relocatable_segment t (list w) (instr concrete_int_32_t) :=
  user_code (fun _ _ => [ 
     Const t (Z_to_imm 2) ruser1
  ]).

Definition hello_world1 : @relocatable_segment t (list w) (instr concrete_int_32_t) :=
  user_code (fun _ _ => [
    Const t (Z_to_imm 2) ruser1;
    Binop t ADD ruser1 ruser1 ruser2
  ]).

Definition hello_world2 : @relocatable_segment t (list w) (instr concrete_int_32_t) :=
  user_code (fun _ syscall_addresses =>
    match syscall_addresses with 
      [mkkey; seal; unseal] => 
        [
          Const _ (word_to_imm mkkey) ruser1;
          Jal t ruser1;
          Const _ (word_to_imm seal) ruser1;
          Const _ (Z_to_imm 17) syscall_arg1;
          Mov _ syscall_ret syscall_arg2;
          Jal t ruser1
        ]
    | _ => []
    end).

(* double seal: should fail *)
Definition hello_world3 : @relocatable_segment t (list w) (instr concrete_int_32_t) :=
  user_code (fun _ syscall_addresses =>
    match syscall_addresses with 
      [mkkey; seal; unseal] => 
        [
          Const _ (word_to_imm mkkey) ruser1;
          Jal t ruser1;
          Const _ (word_to_imm seal) ruser1;
          Const _ (Z_to_imm 17) syscall_arg1;
          Mov _ syscall_ret syscall_arg2;
          Jal t ruser1;
          Mov _ syscall_ret syscall_arg1;
          Jal t ruser1
        ]
    | _ => []
    end).

(* Test seal-then-unseal *)
Definition hello_world4 : @relocatable_segment t (list w) (instr concrete_int_32_t) :=
  user_code (fun _ syscall_addresses =>
    match syscall_addresses with 
      [mkkey; seal; unseal] => 
        [
          Const _ (word_to_imm mkkey) ruser1;
          Jal t ruser1;
          Mov _ syscall_ret syscall_arg2;
          Const _ (word_to_imm seal) ruser1;
          Const _ (Z_to_imm 17) syscall_arg1;
          Jal t ruser1;
          Mov _ syscall_ret syscall_arg1;
          Const _ (word_to_imm unseal) ruser1;
          Jal t ruser1
        ]
    | _ => []
    end).

(* Test store and load *)
Definition hello_world5 : @relocatable_segment t (list w) (instr concrete_int_32_t) :=
  user_code (fun base syscall_addresses =>
    let data := word_to_imm (add_word base (Int32.repr 0)) in
    match syscall_addresses with 
      [mkkey; seal; unseal] => 
        [
          (* DATA BLOCK *)
          Nop _;
          (* As before, make up a key and seal 17 with it *)
          Const _ (word_to_imm mkkey) ruser1;
          Jal t ruser1;
          Mov _ syscall_ret syscall_arg2;
          Const _ (word_to_imm seal) ruser1;
          Const _ (Z_to_imm 17) syscall_arg1;
          Jal t ruser1;
          (* Store it in the data block and read it back *)
          Const _ data ruser1;
          Store t ruser1 syscall_ret;
          Load t ruser1 ruser2
        ]
    | _ => []
    end).

(* Compute (runn 2000 hello_world5). *)

(* Compute (run_abs 2000 hello_world5). *)

(* TODO: Refinement proof from concrete to abstract instances *)

End ConcreteSealing.

