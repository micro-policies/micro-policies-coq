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
    [Const _ (Z_to_imm (word_to_Z x)) r]
|}.

(* BCP: These have to be included in the range of user registers.
   There should be a proof obligation to this effect somewhere. *)
Global Instance scr : @syscall_regs t := {|
  syscall_ret  := Int32.repr 20;
  syscall_arg1 := Int32.repr 21;
  syscall_arg2 := Int32.repr 22
|}.

(* BCP: This is not the right place to define these: But it should be
   someplace "user accessible", since user code (or at least the
   compiler) is going to need to know which registers it is allowed to
   use. *)
Definition user_reg_min : reg concrete_int_32_t := Int32.repr 16. (* First user register *)
Definition user_reg_max : reg concrete_int_32_t := Int32.repr 31. (* Last user register *)

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
    PartMaps.filter mem p := Int32PMap.filter mem p
  |};

  reg_class := {|
    TotalMaps.get regs r := Int32TMap.get r regs;
    (* BCP/MD: Why isn't this called 'set'? *)
    TotalMaps.upd regs r x := Int32TMap.set r x regs
  |}
|}.


(* Notes:

   - encoding of tags

       DATA      --> 0
       KEY(k)    --> k*4+1
       SEALED(k) --> k*4+3

  Questions:

   - How should we really deal with user-code registers

  Need to build...

   - concrete transfer function (with combinators)

       basically we just check that things are tagged DATA (unless
       they are only being copied around)

   - three system call routines

       MKKEY: increment the extra state and return the old value (as a KEY)

       SEAL: move a tag KEY(k) from one atom to another (currently
       marked DATA, afterwards marked SEAL(k))

       UNSEAL: check that the tag of one arg is KEY(k) and the other
       is SEAL(k) and then change the latter to DATA.

*)

(* ---------------------------------------------------------------- *)
(* Code combinators... *)

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

Definition user_code (f : w -> list w -> list (instr t))
                   : @relocatable_segment t (list w) atom := 
  (* This is hideous.  Will totally break if we add more system calls. *)
  (length (f (Z_to_word 0) [Z_to_word 0; Z_to_word 0; Z_to_word 0]), 
   fun base syscall_addresses => 
     map (fun x => Atom (encode_instr x) (encode_sealing_tag Sym.DATA)) 
         (f base syscall_addresses)).

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
    Const _ (Z_to_imm (word_to_Z DATA)) ri1;
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
      [Const _ (Z_to_imm (word_to_Z DATA)) rtrpc;
       Const _ (Z_to_imm (word_to_Z DATA)) rtr
      ])
  (* CONST *)
  ([ Const _ (op_to_imm CONST) ri1;
     Binop _ EQ rop ri1 ri1 ] ++
   (if_ ri1 
     (assert_DATA rtpc ++ assert_DATA rti ++
      [Const _ (Z_to_imm (word_to_Z DATA)) rtrpc;
       Const _ (Z_to_imm (word_to_Z DATA)) rtr
      ])
  (* MOV *)
  ([ Const _ (op_to_imm MOV) ri1;
     Binop _ EQ rop ri1 ri1 ] ++
   (if_ ri1 
     (assert_DATA rtpc ++ assert_DATA rti ++
      [Const _ (Z_to_imm (word_to_Z DATA)) rtrpc;
       Mov _ rt1 rtr
      ])
  (* BINOPs *)
  (let binop cont b := 
         [ Const _ (op_to_imm (BINOP b)) ri1;
           Binop _ EQ rop ri1 ri1 ] ++
         (if_ ri1 
           (assert_DATA rtpc ++ assert_DATA rti ++
            assert_DATA rt1 ++ assert_DATA rt2 ++
            [Const _ (Z_to_imm (word_to_Z DATA)) rtrpc;
             Const _ (Z_to_imm (word_to_Z DATA)) rtr
            ]) 
           cont) in
    fold_left binop binops 
  (* LOAD *)
  ([ Const _ (op_to_imm LOAD) ri1;
     Binop _ EQ rop ri1 ri1 ] ++
   (if_ ri1 
     (assert_DATA rtpc ++ assert_DATA rti ++ assert_DATA rt1 ++
      [Const _ (Z_to_imm (word_to_Z DATA)) rtrpc;
       Mov _ rt2 rtr
      ])
  (* STORE *)
  ([ Const _ (op_to_imm STORE) ri1;
     Binop _ EQ rop ri1 ri1 ] ++
   (if_ ri1 
     (assert_DATA rtpc ++ assert_DATA rti ++ assert_DATA rt1 ++
      [Const _ (Z_to_imm (word_to_Z DATA)) rtrpc;
       Mov _ rt2 rtr
      ])
  (* Unknown opcode: Halt *)
  ([Halt _])))))))))))))). 

Definition fault_handler : @relocatable_segment t w w :=
  kernel_code (handler t ops fhp transfer_function).

Definition extra_state : @relocatable_segment t w w := 
  kernel_data [nat_to_word 13].

Definition gen_syscall_code gen : @relocatable_segment t w w :=
  (length (gen (Int32.repr 0) (Int32.repr 0)), 
   fun b w => map encode_instr (gen b w)).

Definition mkkey_segment : @relocatable_segment t w w :=
  gen_syscall_code (fun _ (extra : w) =>
         [Const _ (Z_to_imm (word_to_Z extra)) ri1; (* load next key *)
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
     (user_mem : @relocatable_segment t (list w) atom) 
   : Concrete.state concrete_int_32_t :=
  (* This list should be defined at the same place as the decoding
     function that splits out the addresses for use when generating
     user code *)
  let syscalls := [mkkey_segment; seal_segment; unseal_segment] in
  initial_state
    extra_state
    fault_handler
    syscalls
    user_mem
    (encode_sealing_tag Sym.DATA)
    user_reg_min user_reg_max
    (encode_sealing_tag Sym.DATA).

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

Definition format_whole_cache (c : Concrete.rules (word t)) :=
  map (fun l => let: (m,r) := l in to_string (format_mvec m +++ ss " => " +++ format_rvec r)) c.

Definition format_cache (c : Concrete.rules (word t)) :=
  format_whole_cache (take 3 c).

Fixpoint filter_Somes {X Y} (l : list (X * option Y)) :=
  match l with
    [] => []
  | (_, None) :: l' => filter_Somes l'
  | (x, Some y) :: l' => (x,y) :: filter_Somes l'
  end.

Require Import Coqlib.
Definition print_state (mem_start mem_end max_reg : nat) st :=
  let mem := filter_Somes 
               (@enum _ _ _ 
                 (@Concrete.mem t cp st) 
                 (@PartMaps.get _ Int32.int _ _) 
                 (@omap atom string (fun a => to_string (format_atom a)))
                 mem_end 
                 (* BCP: Surely this is not the right way to do this... *)
                 (Int32.repr (word_to_Z (nat_to_word mem_start)))) in 
  let regs' := @enum _ _ _ 
                 (@Concrete.regs t cp st) 
                 (@TotalMaps.get _ Int32.int _ _) 
                 (fun a => format_atom a)
                 max_reg 
                 (Int32.repr 0) in 
  let regs := map (fun r => 
               let: (x,a) := r in 
               to_string (ss "r" +++ format_nat (nat_of_Z x) 
                          +++ ss ": " +++ a)) regs' in
  (to_string (ss "PC: " +++ format_atom (Concrete.pc st)),
  "REGISTERS: ", regs,
  "MEMORY: ", mem,
  "CACHE: ... ", format_cache (Concrete.cache st)).

Definition summarize_state st :=
  let mem := filter_Somes 
               (@enum _ _ _ 
                 (@Concrete.mem t cp st) 
                 (@PartMaps.get _ Int32.int _ _) 
                 (@omap atom string (fun a => to_string (format_atom a)))
                 8
                 (Int32.repr 0)) in 
  let regs' := @enum _ _ _ 
                 (@Concrete.regs t cp st) 
                 (@TotalMaps.get _ Int32.int _ _) 
                 (fun a => format_atom a)
                 32
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
  (to_string (ss "PC=" +++ format_atom (Concrete.pc st) +++ ss " "
              +++ current_instr
              +++ (ss "  ") +++ ssconcat (ss " ") regs),
  "  ", mem,
  "  ", format_whole_cache (take 1 (Concrete.cache st))).

Definition tracen n p := 
  let init := build_concrete_sealing_machine p in
  let tr := exec.tracen less_trivial_masks t n init in
  (
   print_state 0 3000 32 init,
   map summarize_state tr
  ).

Definition trace := tracen 10000.

(* ---------------------------------------------------------------------- *)
(* Tests... *)

Definition hello_world0 : @relocatable_segment t (list w) atom :=
  user_code (fun _ _ => [ 
     Const t (Z_to_imm 2) (Int32.repr 25)
  ]).

Definition hello_world1 : @relocatable_segment t (list w) atom :=
  user_code (fun _ _ => [
    Const t (Z_to_imm 2) (Int32.repr 25);
    Binop t ADD (Int32.repr 25) (Int32.repr 25) (Int32.repr 26)
  ]).

Definition hello_world2 : @relocatable_segment t (list w) atom :=
  user_code (fun _ syscall_addresses =>
    match syscall_addresses with 
      [mkkey; seal; unseal] => 
        [
          Const _ (Z_to_imm (word_to_Z mkkey)) (Int32.repr 25);
          Jal t (Int32.repr 25);
          Const _ (Z_to_imm (word_to_Z seal)) (Int32.repr 25);
          Const _ (Z_to_imm 17) syscall_arg1;
          Mov _ syscall_ret syscall_arg2;
          Jal t (Int32.repr 25)
        ]
    | _ => []
    end).

(* double seal: should fail *)
Definition hello_world3 : @relocatable_segment t (list w) atom :=
  user_code (fun _ syscall_addresses =>
    match syscall_addresses with 
      [mkkey; seal; unseal] => 
        [
          Const _ (Z_to_imm (word_to_Z mkkey)) (Int32.repr 25);
          Jal t (Int32.repr 25);
          Const _ (Z_to_imm (word_to_Z seal)) (Int32.repr 25);
          Const _ (Z_to_imm 17) syscall_arg1;
          Mov _ syscall_ret syscall_arg2;
          Jal t (Int32.repr 25);
          Mov _ syscall_ret syscall_arg1;
          Jal t (Int32.repr 25)
        ]
    | _ => []
    end).

(* Test seal-then-unseal *)
Definition hello_world4 : @relocatable_segment t (list w) atom :=
  user_code (fun _ syscall_addresses =>
    match syscall_addresses with 
      [mkkey; seal; unseal] => 
        [
          Const _ (Z_to_imm (word_to_Z mkkey)) (Int32.repr 25);
          Jal t (Int32.repr 25);
          Mov _ syscall_ret syscall_arg2;
          Const _ (Z_to_imm (word_to_Z seal)) (Int32.repr 25);
          Const _ (Z_to_imm 17) syscall_arg1;
          Jal t (Int32.repr 25);
          Mov _ syscall_ret syscall_arg1;
          Const _ (Z_to_imm (word_to_Z unseal)) (Int32.repr 25);
          Jal t (Int32.repr 25)
        ]
    | _ => []
    end).

(* Test store and load *)
Definition hello_world5 : @relocatable_segment t (list w) atom :=
  user_code (fun base syscall_addresses =>
    let data := Z_to_imm (word_to_Z (add_word base (Int32.repr 0))) in
    match syscall_addresses with 
      [mkkey; seal; unseal] => 
        [
          (* DATA BLOCK *)
          Nop _;
          (* As before, make up a key and seal 17 with it *)
          Const _ (Z_to_imm (word_to_Z mkkey)) (Int32.repr 25);
          Jal t (Int32.repr 25);
          Mov _ syscall_ret syscall_arg2;
          Const _ (Z_to_imm (word_to_Z seal)) (Int32.repr 25);
          Const _ (Z_to_imm 17) syscall_arg1;
          Jal t (Int32.repr 25);
          (* Store it in the data block *)
          Const _ data (Int32.repr 25);
          Store t (Int32.repr 25) syscall_ret
        ]
    | _ => []
    end).

Compute (tracen 2000 hello_world5). 

(*
Definition print_res_state n init :=
  omap (print_state 801 807 27) init.

Compute (print_res_state 140
 (build_concrete_sealing_machine hello_world)). 
*)

(*
Compute (print_res_state 19 (build_concrete_sealing_machine hello_world)).
*)

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

