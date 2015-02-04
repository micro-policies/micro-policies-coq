Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.eqtype Ssreflect.ssrnat Ssreflect.ssrbool Ssreflect.seq Ssreflect.choice Ssreflect.fintype.
Require Import MathComp.ssrint.
Require Import CoqUtils.ord CoqUtils.word CoqUtils.partmap CoqUtils.hseq.
Require Import lib.utils lib.word_utils common.types common.segment.
Require Import concrete.concrete.
Require Import concrete.int_32.
Require Import concrete.exec.
Require Import symbolic.int_32.
Require Import symbolic.symbolic.
Require Import symbolic.exec.
Require Import symbolic.refinement_common.
Require Import symbolic.backward.
Require Import symbolic.rules.
Require Import symbolic.fault_handler.
Require Import sealing.symbolic.
Require Import sealing.abstract.
Require Import sealing.refinementSA.
Require Import Omega.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import DoNotation.

Module SealingInstances.

Section WithClasses.

(* ---------------------------------------------------------------- *)
(* int32 instance *)

Definition mt := concrete_int_32_mt.
Instance ops : machine_ops mt := concrete_int_32_ops.
Instance fhp : fault_handler_params mt := concrete_int_32_fh.

(* ---------------------------------------------------------------- *)
(* Generic definitions for building concrete machine instances *)

Definition ruser1 : reg mt := as_word 20.
Definition ruser2 : reg mt := as_word 21.
Definition ruser3 : reg mt := as_word 22.
Definition ruser4 : reg mt := as_word 23.
Definition user_registers :=
  [:: ra; syscall_ret; syscall_arg1; syscall_arg2; syscall_arg3; ruser1;
      ruser2; ruser3; ruser4].
Definition user_reg_max := last 0%w user_registers.

Definition monitor_data {X} l : @relocatable_segment mt X w :=
 (length l, fun _ _ => l).

Definition monitor_code {X} l : @relocatable_segment mt X w :=
 (length l,
  fun _ _ => map encode_instr l).

(* ---------------------------------------------------------------- *)
(* ---------------------------------------------------------------- *)
(* ---------------------------------------------------------------- *)
(* Main definitions for concrete sealing machine *)

(* TODO: THINGS TO CLEAN:
    - move code generation macros out of fault_handler.v
      (into a new separate file?)
    - make a switch macro
    - check that there are no temp registers live across the transfer
      function call from the fault handler
    - the handling of the ut annotations on ENTRY tags
*)

(* Encoding of tags:
      DATA      --> 0
      KEY(k)    --> k*4+1
      SEALED(k) --> k*4+3
*)

Instance sk_defs : Sym.sealing_key := {
 key := [ordType of word 28];
 max_key := monew;
 inc_key x := (x + 1)%w;
 ltb_inc sk := @leqw_succ _ sk monew
}.

Instance sp : Symbolic.params := @Sym.sym_sealing sk_defs.

Definition encode_sealing_tag (t : Sym.stag) : word 30 :=
 match t with
   Sym.DATA => @wpack [:: 28; 2] [hseq 0; 0]%w
 | Sym.KEY k => @wpack [:: 28; 2] [hseq k; 1]%w
 | Sym.SEALED k => @wpack [:: 28; 2] [hseq k; as_word 3]%w
 end.

Definition decode_sealing_tag (t : word 30) : option Sym.stag :=
  let: [hseq k; t] := @wunpack [:: 28; 2] t in
  if t == 0%w then
    if k == 0%w then Some Sym.DATA
    else None
  else if t == 1%w then
    Some (Sym.KEY k)
  else if t == as_word 3 then
    Some (Sym.SEALED k)
  else None.

Lemma encode_sealing_tagK t : decode_sealing_tag (encode_sealing_tag t) = Some t.
Proof.
  case: t => [|k|k];
  by rewrite /decode_sealing_tag /encode_sealing_tag wpackK /=.
Qed.

Lemma decode_sealing_tagK w t : decode_sealing_tag w = Some t ->
                                encode_sealing_tag t = w.
Proof.
  rewrite /decode_sealing_tag /encode_sealing_tag.
  case E: (wunpack _) => [k [w' []]].
  move: (@wunpackK [:: 28; 2] w). rewrite E.
  have [?|?] := altP (w' =P _); try subst w'.
  { have [?|?] := altP (k =P _); try subst k; last by [].
    by move => H [<-]. }
  have [?|?] := altP (w' =P _); try subst w'.
  { by move => H [<-]. }
  have [?|?] := altP (w' =P _); try subst w'; last by [].
  by move => H [<-].
Qed.

Instance encodable_tag : @encodable mt Sym.stags := {|
  decode k mem := fun (w : mword mt) =>
    let: [hseq ut; w'] := @wunpack [:: 30; 2] w in
    if w' == 0%w then None
    else
      match k return option (wtag Sym.stags k) with
      | Symbolic.P => Some tt
      | Symbolic.M =>
        if w' == 1%w then
            do! ut <- decode_sealing_tag ut;
            Some (@User Symbolic.ttypes ut)
        else if w' == as_word 2 then
          do! ut <- decode_sealing_tag ut;
          Some (@Entry Symbolic.ttypes ut)
        else None
      | Symbolic.R =>
        if w' == 1%w then
            do! ut <- decode_sealing_tag ut;
            Some ut
        else None
      end
|}.
Proof.
  by eauto.
by move=> tk _; rewrite 2!wunpackS /=.
Qed.

Definition DATA : mword mt := 0%w.

Definition transfer_function : seq (instr mt) :=
 let assert_DATA r := [::
   Const (swcast DATA) ri1;
   Binop EQ r ri1 ri1 ] ++
                        if_ ri1 [::] [:: Halt _]
   in
 (* entry points for system calls *)
 ([:: Const (as_word (pickle SERVICE)) ri1;
      Binop EQ rop ri1 ri1 ] ++
  (if_ ri1
    [::]
 (* NOP *)
 ([:: Const (as_word (pickle NOP)) ri1;
      Binop EQ rop ri1 ri1 ] ++
  (if_ ri1
    (assert_DATA rtpc ++ assert_DATA rti ++
     [:: Const (swcast DATA) rtrpc;
         Const (swcast DATA) rtr
     ])
 (* CONST *)
 ([:: Const (as_word (pickle CONST)) ri1;
      Binop EQ rop ri1 ri1 ] ++
  (if_ ri1
    (assert_DATA rtpc ++ assert_DATA rti ++
     [:: Const (swcast DATA) rtrpc;
         Const (swcast DATA) rtr
     ])
 (* MOV *)
 ([:: Const (as_word (pickle MOV)) ri1;
      Binop EQ rop ri1 ri1 ] ++
  (if_ ri1
    (assert_DATA rtpc ++ assert_DATA rti ++
     [:: Const (swcast DATA) rtrpc;
      Mov rt1 rtr
     ])
 (* BINOPs *)
 (let do_binop cont b :=
        [:: Const (as_word (pickle (BINOP b))) ri1;
            Binop EQ rop ri1 ri1 ] ++
        (if_ ri1
          (assert_DATA rtpc ++ assert_DATA rti ++
           assert_DATA rt1 ++ assert_DATA rt2 ++
           [:: Const (swcast DATA) rtrpc;
               Const (swcast DATA) rtr
           ])
          cont) in
   foldl do_binop [::] (enum binop) ++
 (* LOAD *)
 ([:: Const (as_word (pickle LOAD)) ri1;
      Binop EQ rop ri1 ri1 ] ++
  (if_ ri1
    (assert_DATA rtpc ++ assert_DATA rti ++ assert_DATA rt1 ++
     [:: Const (swcast DATA) rtrpc;
      Mov rt2 rtr
     ])
 (* STORE *)
 ([:: Const (as_word (pickle STORE)) ri1;
      Binop EQ rop ri1 ri1 ] ++
  (if_ ri1
    (assert_DATA rtpc ++ assert_DATA rti ++ assert_DATA rt1 ++
     [:: Const (swcast DATA) rtrpc;
         Mov rt2 rtr
     ])
 (* JUMP *)
 ([:: Const (as_word (pickle JUMP)) ri1;
      Binop EQ rop ri1 ri1 ] ++
  (if_ ri1
    (assert_DATA rtpc ++ assert_DATA rti ++
     [:: Const (swcast DATA) rtrpc])
 (* BNZ *)
 ([:: Const (as_word (pickle BNZ)) ri1;
      Binop EQ rop ri1 ri1 ] ++
  (if_ ri1
    (assert_DATA rtpc ++ assert_DATA rti ++ assert_DATA rt1 ++
     [:: Const (swcast DATA) rtrpc])
 (* JAL *)
 ([:: Const (as_word (pickle JAL)) ri1;
      Binop EQ rop ri1 ri1 ] ++
  (if_ ri1
    (assert_DATA rtpc ++ assert_DATA rti ++ assert_DATA rt1 ++
     [:: Const (swcast DATA) rtrpc;
         Const (swcast DATA) rtr])
 (* Unknown opcode: Halt *)
 ([:: Halt _])))))))))))))))))))).

Definition fault_handler : @relocatable_segment mt w w :=
 monitor_code (fault_handler.handler fhp transfer_function).

Definition extra_state : @relocatable_segment mt w w :=
 monitor_data [:: as_word 13].

Definition gen_syscall_code gen : @relocatable_segment mt w w :=
 (length (gen (as_word 0) (as_word 0)),
  fun b w => map encode_instr (gen b w)).

Definition mkkey_segment : @relocatable_segment mt w w :=
 gen_syscall_code (fun _ (extra : w) =>
        [:: Const (swcast extra) ri1; (* load next key *)
            Load ri1 ri5;
            Const (as_word 1) ri3; (* increment and store back *)
            Binop ADD ri5 ri3 ri3;
            Store ri1 ri3;
            Const (as_word 2) ri3; (* wrap k as KEY(k): SHL by 2 and add 1 *)
            Binop SHL ri5 ri3 ri4;
            Const 1%w ri3;
            Binop ADD ri3 ri4 ri4] ++
        wrap_user_tag ri4 ri4 ++
        [:: Const 0%w ri5; (* payload for new key is 0, arbitrarily *)
            PutTag ri5 ri4 syscall_ret; (* build the key *)
            Jump ra
         ]).

Definition seal_segment : @relocatable_segment mt w w :=
 gen_syscall_code (fun _ (extra : w) =>
       (* Ensure that first argument is tagged DATA, halting otherwise *)
       [:: GetTag syscall_arg1 ri3] ++
       extract_user_tag ri3 rb ri3 ++
       if_ rb [::] [:: Halt _] ++
       [:: Const (as_word 3) ri5;
           Binop AND ri3 ri5 ri5] ++
       if_ ri5 [:: Halt _] [::] ++
       (* Ensure that second argument is tagged KEY, halting otherwise *)
       [:: GetTag syscall_arg2 ri4] ++
       extract_user_tag ri4 rb ri4 ++
       if_ rb [::] [:: Halt _] ++
       [:: Const (as_word 3) ri5;
           Binop AND ri4 ri5 ri2;
           Const (as_word 1) ri5;
           Binop EQ ri5 ri2 ri5] ++
       if_ ri5 [::] [:: Halt _] ++
       (* Form SEALED(k) tag from KEY(k) in ri4 *)
       [:: Const (as_word 2) ri5;
           Binop OR ri5 ri4 ri4] ++
       wrap_user_tag ri4 ri4 ++
       [:: PutTag syscall_arg1 ri4 syscall_ret] ++
       (* Check that return PC is tagged DATA *)
       [:: GetTag ra ri3] ++
       extract_user_tag ri3 rb ri3 ++
       if_ rb [::] [:: Halt _] ++
       [:: Const (as_word 0) ri5;
           Binop EQ ri3 ri5 ri5] ++
       if_ ri5 [:: Jump ra] [:: Halt _]
 ).

Definition unseal_segment : @relocatable_segment mt w w :=
 gen_syscall_code (fun _ (extra : w) =>
       (* Ensure that second argument is tagged KEY, halting otherwise *)
       [:: GetTag syscall_arg2 ri4] ++
       extract_user_tag ri4 rb ri4 ++
       if_ rb [::] [:: Halt _] ++
       [:: Const (as_word 3) ri5;
           Binop AND ri4 ri5 ri2;
           Const (as_word 1) ri5;
           Binop EQ ri5 ri2 ri5] ++
       if_ ri5 [::] [:: Halt _] ++
       (* Form SEALED(k) tag from KEY(k) in ri4 *)
       [:: Const (as_word 2) ri5;
           Binop OR ri5 ri4 ri4] ++
       (* Ensure that first argument has a user tag (put it in ri3) *)
       [:: GetTag syscall_arg1 ri3] ++
       extract_user_tag ri3 rb ri3 ++
       if_ rb [::] [:: Halt _] ++
       (* Check that the two tags are equal (i.e. both SEALED(k)) *)
       [:: Binop EQ ri3 ri4 ri4] ++
       if_ ri5 [::] [:: Halt _] ++
       (* Retag the payload with DATA *)
       [:: Const (as_word 0) ri5] ++
       wrap_user_tag ri5 ri5 ++
       [:: PutTag syscall_arg1 ri5 syscall_ret] ++
       (* Check that return PC is tagged DATA *)
       (* (not certain this is needed, but keeping it here and above
           to make sure we satisfy refinement hypotheses...) *)
       [:: GetTag ra ri3] ++
       extract_user_tag ri3 rb ri3 ++
       if_ rb [::] [:: Halt _] ++
       [:: Const (as_word 0) ri5;
           Binop EQ ri3 ri5 ri5] ++
       if_ ri5 [:: Jump ra] [:: Halt _]
).

Definition concrete_sealing_monitor :
  Concrete.memory mt * w * @classes.sealing_syscall_addrs mt :=
  let syscalls := [:: mkkey_segment; seal_segment; unseal_segment] in
  let res := build_monitor_memory extra_state fault_handler syscalls in
  let monitor_memory := fst (fst res) in
  let user_memory_addr := snd (fst res) in
  let syscall_addrs := Vector.of_list (snd res) in
  let syscall_addrs := {|
                          classes.mkkey_addr := Vector.nth syscall_addrs Fin.F1;
                          classes.seal_addr := Vector.nth syscall_addrs (Fin.FS Fin.F1);
                          classes.unseal_addr := Vector.nth syscall_addrs (Fin.FS (Fin.FS Fin.F1))
                       |} in
  (monitor_memory, user_memory_addr, syscall_addrs).

Definition concrete_sealing_monitor_memory :=
  fst (fst concrete_sealing_monitor).

Definition user_memory_addr :=
  snd (fst concrete_sealing_monitor).

Instance ssa : @classes.sealing_syscall_addrs mt :=
  snd concrete_sealing_monitor.

Definition build_concrete_sealing_machine
    (user_program : @relocatable_segment mt (@classes.sealing_syscall_addrs mt) (instr mt))
  : Concrete.state concrete_int_32_mt
     :=
 (* This list should be defined at the same place as the decoding
    function that splits out the addresses for use when generating
    user code *)
 let user_mem :=
       map_relocatable_segment
         (fun x => Atom (encode_instr x) DATA)
         user_program in
 concrete_initial_state
   concrete_sealing_monitor_memory
   user_memory_addr
   ssa
   user_mem
   DATA
   user_registers
   DATA.

(* ---------------------------------------------------------------- *)
(* ---------------------------------------------------------------- *)
(* ---------------------------------------------------------------- *)
(* Symbolic machine *)

Definition build_symbolic_sealing_machine
    (user_program : @relocatable_segment mt (@classes.sealing_syscall_addrs mt) (instr mt))
  : @Symbolic.state concrete_int_32_mt (@Sym.sym_sealing sk_defs) :=
 (* This list should be defined at the same place as the decoding
    function that splits out the addresses for use when generating
    user code *)
 let user_mem : @relocatable_segment mt _ _ :=
       map_relocatable_segment
         ((fun v => types.Atom v Sym.DATA) ∘ encode_instr)
         user_program in
 @symbolic_initial_state (@Sym.sym_sealing sk_defs) _
                         user_mem
                         user_memory_addr@tt
                         ssa
                         user_registers
                         (types.Atom (as_word 0) Sym.DATA)
                         (as_word 0).

(* ---------------------------------------------------------------- *)
(* ---------------------------------------------------------------- *)
(* ---------------------------------------------------------------- *)
(* Abstract machine *)

Definition keytype := [ordType of nat].

Definition max_element (l : seq keytype) : keytype :=
 foldr maxn O l.

Lemma max_element_plus_one_is_distinct :
 forall (l : seq keytype),
   1 + max_element l \notin l.
Proof.
 move => l.
 have MAX: forall x, x \in l -> x <= max_element l.
 { elim: l => [|x' l IH] // x /orP [/eqP -> | THERE] //=.
   - by rewrite leq_max leqnn.
   - by rewrite leq_max IH //= orbT. }
 apply/negP => CONTRA.
 move: (MAX _ CONTRA).
 rewrite /addn /addn_rec.
 move/leP => LE.
 omega.
Qed.

Global Instance sk : Abs.sealing_key := {
 key := keytype;
 mkkey_f := fun l => 1 + max_element l;
 mkkey_fresh := max_element_plus_one_is_distinct
}.

(* Minor: Why do PartMaps.get and PartMaps.set take their arguments in
  a different order from Int32PMap.get and Int32PMap.set?? *)

Definition build_abstract_sealing_machine
    (user_program : @relocatable_segment mt (@classes.sealing_syscall_addrs mt) (instr mt))
  : @Abs.state concrete_int_32_mt sk :=
 (* This list should be defined at the same place as the decoding
    function that splits out the addresses for use when generating
    user code *)
 (* NB: syscall_addrs gets passed via typeclass resolution *)
 let: (_,base_addr,syscall_addrs) := concrete_sealing_monitor in
 let user_mem :=
       map_relocatable_segment
         ((@Abs.VData _ _) ∘ encode_instr)
         user_program in
  Abs.abstract_initial_state
    user_mem
    base_addr
    user_registers.

Definition user_code (f : w -> @classes.sealing_syscall_addrs mt -> seq (instr mt))
                  : @relocatable_segment mt (@classes.sealing_syscall_addrs mt) (instr mt) :=
 (size (f user_memory_addr ssa), f).

Definition hello_world0 : @relocatable_segment mt (@classes.sealing_syscall_addrs mt) (instr mt) :=
  user_code (fun _ _ => [::
     Const (as_word 2) ruser1
  ]).

Definition hello_world1 : @relocatable_segment mt (@classes.sealing_syscall_addrs mt) (instr mt) :=
  user_code (fun _ _ => [::
    Const (as_word 2) ruser1;
    Binop ADD ruser1 ruser1 ruser2
  ]).

Definition hello_world2 : @relocatable_segment mt (@classes.sealing_syscall_addrs mt) (instr mt) :=
  user_code (fun _ _ =>
        [::
          Const (swcast classes.mkkey_addr) ruser1;
          Jal ruser1;
          Const (swcast classes.seal_addr) ruser1;
          Const (as_word 17) syscall_arg1;
          Mov syscall_ret syscall_arg2;
          Jal ruser1
        ]
      ).

(* double seal: should fail *)
Definition hello_world3 : @relocatable_segment mt (@classes.sealing_syscall_addrs mt) (instr mt) :=
  user_code (fun _ _ =>
        [::
          Const (swcast classes.mkkey_addr) ruser1;
          Jal ruser1;
          Const (swcast classes.seal_addr) ruser1;
          Const (as_word 17) syscall_arg1;
          Mov syscall_ret syscall_arg2;
          Jal ruser1;
          Mov syscall_ret syscall_arg1;
          Jal ruser1
        ]
  ).

(* Test seal-then-unseal *)
Definition hello_world4 : @relocatable_segment mt (@classes.sealing_syscall_addrs mt) (instr mt) :=
  user_code (fun _ _ =>
        [::
          Const (swcast classes.mkkey_addr) ruser1;
          Jal ruser1;
          Mov syscall_ret syscall_arg2;
          Const (swcast classes.seal_addr) ruser1;
          Const (as_word 17) syscall_arg1;
          Jal ruser1;
          Mov syscall_ret syscall_arg1;
          Const (swcast classes.unseal_addr) ruser1;
          Jal ruser1
        ]
  ).

(* Test store and load *)
Definition hello_world5 : @relocatable_segment mt (@classes.sealing_syscall_addrs mt) (instr mt) :=
  user_code (fun base _ =>
    let data := swcast (base + 0)%w in
        [::
          (* DATA BLOCK *)
          Nop _;
          (* As before, make up a key and seal 17 with it *)
          Const (swcast classes.mkkey_addr) ruser1;
          Jal ruser1;
          Mov syscall_ret syscall_arg2;
          Const (swcast classes.seal_addr) ruser1;
          Const (as_word 17) syscall_arg1;
          Jal ruser1;
          (* Store it in the data block and read it back *)
          Const data ruser1;
          Store ruser1 syscall_ret;
          Load ruser1 ruser2
        ]
  ).

Section Refinement.

Context {sealing_invariant : @policy_invariant mt _ _}.

Let monitor_invariant := fault_handler_invariant ops fhp transfer_function sealing_invariant.

Context {implementation_correct : monitor_code_bwd_correctness monitor_invariant Sym.sealing_syscalls}.

Inductive refine_state (ast : Abs.state mt) (cst : Concrete.state mt) : Prop :=
| rs_intro : forall sst m,
               refinement_common.refine_state monitor_invariant Sym.sealing_syscalls sst cst ->
               @refinementSA.refine_state mt sk_defs sk m ast sst ->
               refine_state ast cst.
Hint Constructors refine_state.

Lemma backwards_refinement_as ast sst sst' m :
  @refinementSA.refine_state mt sk_defs sk m ast sst ->
  exec (Symbolic.step Sym.sealing_syscalls) sst sst' ->
  exists ast' m',
    exec (fun ast ast' => Abs.step ast ast') ast ast' /\
    refinementSA.refine_state m' ast' sst'.
Proof.
  move => REF EXEC.
  elim: EXEC ast m REF => {sst sst'} [sst _ |sst sst' sst'' _ STEPS EXEC IH] ast m REF; first by eauto 7.
  generalize (refinementSA.backward_simulation REF STEPS).
  intros (ast' & m' & STEPA & REF').
  have := IH _ _ REF'.
  intros (ast'' & m'' & EXECA & REF''). by eauto 7.
Qed.

Lemma backwards_refinement ast cst cst' :
  refine_state ast cst ->
  exec (Concrete.step _ masks) cst cst' ->
  in_user cst' = true ->
  exists ast',
    exec (fun ast ast' => Abs.step ast ast') ast ast' /\
    refine_state ast' cst'.
Proof.
  move => [sst m SC AS] EXECC INUSER.
  generalize (backwards_refinement SC EXECC INUSER) => - [sst' EXECS SC'].
  have := backwards_refinement_as AS EXECS.
  intros (ast' & m' & EXECA & AS'). by eauto 7.
Qed.

End Refinement.

End WithClasses.

End SealingInstances.
