(*
TODO: write better testing support -- e.g. comparing final states
*)

Require Import List. Import ListNotations.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.SetoidDec.
Require Import ssreflect ssrfun eqtype ssrnat ssrbool seq.
Require Import lib.utils lib.partial_maps common.common.
Require Import lib.FiniteMaps lib.ordered.
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
Require Import Integers.
Require Import Omega.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import DoNotation.

Module SealingInstances.

Section WithClasses.

(* ---------------------------------------------------------------- *)
(* int32 instance *)

Definition t := concrete_int_32_t.
Instance ops : machine_ops t := concrete_int_32_ops.
Instance fhp : fault_handler_params t := concrete_int_32_fh.

(* ---------------------------------------------------------------- *)
(* Generic definitions for building concrete machine instances *)

Definition ruser1 : reg t := Word.repr 20.
Definition ruser2 : reg t := Word.repr 21.
Definition ruser3 : reg t := Word.repr 22.
Definition ruser4 : reg t := Word.repr 23.
Definition user_registers :=
  [:: ra; syscall_ret; syscall_arg1; syscall_arg2; syscall_arg3; ruser1;
      ruser2; ruser3; ruser4].
Definition user_reg_max := last (Word.repr 0) user_registers.

Definition kernel_data {X} l : @relocatable_segment t X w :=
 (length l, fun _ _ => l).

Definition kernel_code {X} l : @relocatable_segment t X w :=
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

Instance sk_defs : Sym.sealing_key := {|
 key := [eqType of Word.int 27];
 max_key := Word.repr (Word.max_unsigned 27);
 inc_key := fun x => Word.add x Word.one;
 ord_key := IntOrdered.int_ordered 27
|}.
Proof.
  rewrite /ordered.ltb /IntOrdered.int_ordered -(lock (IntOrdered.int_ordered_def _))
          /= /IntOrdered.int_compare /Word.unsigned.
  intros sk.
  destruct (equiv_dec sk (Word.repr (Word.max_unsigned 27))) as [H7 | H7]; first by [].
  rewrite {1 2 3}/Word.ltu.
  rewrite Word.unsigned_repr //.
  case: (Coqlib.zlt (Word.unsigned sk) (Word.max_unsigned 27)) => [H6 _ | H6]; last by [].
  case: (equiv_dec sk (sk + 1)%w) => [|NEQ].
  { rewrite /= -{1}(Word.add_zero _ sk) => /addwI contra.
    discriminate. }
  move: (Word.unsigned_range sk) => [H1' H2'].
  rewrite addwC -{1 3 5}(add0w sk) Word.translate_ltu //.
  - rewrite /= /Word.max_unsigned. omega.
  - have {H7} H7 := H7 : sk <> Word.repr (Word.max_unsigned 27).
    rewrite [_ 1%w]/=. omega.
Defined.

Import Word.Notations.

Definition encode_sealing_tag (t : Sym.stag) : Word.int 29 :=
 match t with
   Sym.DATA => Word.pack [27; 1] [Word.zero; Word.zero]%wp
 | Sym.KEY k => Word.pack [27; 1] [k; Word.one]%wp
 | Sym.SEALED k => Word.pack [27; 1] [k; Word.repr 3]%wp
 end.

Definition decode_sealing_tag (t : Word.int 29) : option Sym.stag :=
  let: [k; t]%wu := Word.unpack [27; 1] t in
  if t == Word.zero then
    if k == Word.zero then Some Sym.DATA
    else None
  else if t == Word.one then
    Some (Sym.KEY k)
  else if t == Word.repr 3 then
    Some (Sym.SEALED k)
  else None.

Lemma encode_sealing_tagK t : decode_sealing_tag (encode_sealing_tag t) = Some t.
Proof.
  case: t => [|k|k];
  by rewrite /decode_sealing_tag /encode_sealing_tag Word.packK /=.
Qed.

Lemma decode_sealing_tagK w t : decode_sealing_tag w = Some t ->
                                encode_sealing_tag t = w.
Proof.
  rewrite /decode_sealing_tag /encode_sealing_tag.
  case E: (Word.unpack [27; 1] w) => [k [w' []]].
  move: (Word.unpackK [27; 1] w). rewrite E.
  have [?|?] := altP (w' =P Word.zero); try subst w'.
  { have [?|?] := altP (k =P Word.zero); try subst k; last by [].
    by move => H [<-]. }
  have [?|?] := altP (w' =P Word.one); try subst w'.
  { by move => H [<-]. }
  have [?|?] := altP (w' =P Word.repr 3); try subst w'; last by [].
  by move => H [<-].
Qed.

Instance encodable_tag : @encodable t Sym.stags := {|
  decode k mem w :=
    let: [ut; w']%wu := Word.unpack [29; 1] w in
    if w' == Word.zero then None
    else if w' == Word.one then
      do! ut <- decode_sealing_tag ut;
      Some (@USER Sym.stag_eqType ut)
    else if w' == Word.repr 2 then
      do! ut <- decode_sealing_tag ut;
      Some (@ENTRY Sym.stag_eqType ut)
    else None
|}.
Proof.
  - by eauto.
  - by [].
Qed.

Definition DATA : word t := Word.repr 0.

Definition transfer_function : list (instr t) :=
 let assert_DATA r := [
   Const (Word.casts DATA) ri1;
   Binop EQ r ri1 ri1 ] ++
                        if_ ri1 [] [Halt _]
   in
 (* entry points for system calls *)
 ([ Const (Word.repr (vop_to_Z SERVICE)) ri1;
    Binop EQ rop ri1 ri1 ] ++
  (if_ ri1
    []
 (* NOP *)
 ([ Const (Word.repr (op_to_Z NOP)) ri1;
    Binop EQ rop ri1 ri1 ] ++
  (if_ ri1
    (assert_DATA rtpc ++ assert_DATA rti ++
     [Const (Word.casts DATA) rtrpc;
      Const (Word.casts DATA) rtr
     ])
 (* CONST *)
 ([ Const (Word.repr (op_to_Z CONST)) ri1;
    Binop EQ rop ri1 ri1 ] ++
  (if_ ri1
    (assert_DATA rtpc ++ assert_DATA rti ++
     [Const (Word.casts DATA) rtrpc;
      Const (Word.casts DATA) rtr
     ])
 (* MOV *)
 ([ Const (Word.repr (op_to_Z MOV)) ri1;
    Binop EQ rop ri1 ri1 ] ++
  (if_ ri1
    (assert_DATA rtpc ++ assert_DATA rti ++
     [Const (Word.casts DATA) rtrpc;
      Mov rt1 rtr
     ])
 (* BINOPs *)
 (let binop cont b :=
        [ Const (Word.repr (op_to_Z (BINOP b))) ri1;
          Binop EQ rop ri1 ri1 ] ++
        (if_ ri1
          (assert_DATA rtpc ++ assert_DATA rti ++
           assert_DATA rt1 ++ assert_DATA rt2 ++
           [Const (Word.casts DATA) rtrpc;
            Const (Word.casts DATA) rtr
           ])
          cont) in
   fold_left binop binops
 (* LOAD *)
 ([ Const (Word.repr (op_to_Z LOAD)) ri1;
    Binop EQ rop ri1 ri1 ] ++
  (if_ ri1
    (assert_DATA rtpc ++ assert_DATA rti ++ assert_DATA rt1 ++
     [Const (Word.casts DATA) rtrpc;
      Mov rt2 rtr
     ])
 (* STORE *)
 ([ Const (Word.repr (op_to_Z STORE)) ri1;
    Binop EQ rop ri1 ri1 ] ++
  (if_ ri1
    (assert_DATA rtpc ++ assert_DATA rti ++ assert_DATA rt1 ++
     [Const (Word.casts DATA) rtrpc;
      Mov rt2 rtr
     ])
 (* JUMP *)
 ([ Const (Word.repr (op_to_Z JUMP)) ri1;
    Binop EQ rop ri1 ri1 ] ++
  (if_ ri1
    (assert_DATA rtpc ++ assert_DATA rti ++
     [Const (Word.casts DATA) rtrpc])
 (* BNZ *)
 ([ Const (Word.repr (op_to_Z BNZ)) ri1;
    Binop EQ rop ri1 ri1 ] ++
  (if_ ri1
    (assert_DATA rtpc ++ assert_DATA rti ++ assert_DATA rt1 ++
     [Const (Word.casts DATA) rtrpc])
 (* JAL *)
 ([ Const (Word.repr (op_to_Z JAL)) ri1;
    Binop EQ rop ri1 ri1 ] ++
  (if_ ri1
    (assert_DATA rtpc ++ assert_DATA rti ++ assert_DATA rt1 ++
     [Const (Word.casts DATA) rtrpc;
      Const (Word.casts DATA) rtr])
 (* Unknown opcode: Halt *)
 ([Halt _])))))))))))))))))))).

Definition fault_handler : @relocatable_segment t w w :=
 kernel_code (fault_handler.handler t fhp transfer_function).

Definition extra_state : @relocatable_segment t w w :=
 kernel_data [Word.reprn 13].

Definition gen_syscall_code gen : @relocatable_segment t w w :=
 (length (gen (Word.repr 0) (Word.repr 0)),
  fun b w => map encode_instr (gen b w)).

Definition mkkey_segment : @relocatable_segment t w w :=
 gen_syscall_code (fun _ (extra : w) =>
        [Const (Word.casts extra) ri1; (* load next key *)
         Load ri1 ri5;
         Const (Word.repr 1) ri3; (* increment and store back *)
         Binop ADD ri5 ri3 ri3;
         Store ri1 ri3;
         Const (Word.repr 2) ri3; (* wrap k as KEY(k): SHL by 2 and add 1 *)
         Binop SHL ri5 ri3 ri4;
         Const Word.one ri3;
         Binop ADD ri3 ri4 ri4] ++
        wrap_user_tag ri4 ri4 ++
        [Const Word.zero ri5; (* payload for new key is 0, arbitrarily *)
         PutTag ri5 ri4 syscall_ret; (* build the key *)
         Jump ra
         ]).

Definition seal_segment : @relocatable_segment t w w :=
 gen_syscall_code (fun _ (extra : w) =>
       (* Ensure that first argument is tagged DATA, halting otherwise *)
       [GetTag syscall_arg1 ri3] ++
       extract_user_tag ri3 rb ri3 ++
       if_ rb [] [Halt _] ++
       [Const (Word.repr 3) ri5;
        Binop AND ri3 ri5 ri5] ++
       if_ ri5 [Halt _] [] ++
       (* Ensure that second argument is tagged KEY, halting otherwise *)
       [GetTag syscall_arg2 ri4] ++
       extract_user_tag ri4 rb ri4 ++
       if_ rb [] [Halt _] ++
       [Const (Word.repr 3) ri5;
        Binop AND ri4 ri5 ri2;
        Const (Word.repr 1) ri5;
        Binop EQ ri5 ri2 ri5] ++
       if_ ri5 [] [Halt _] ++
       (* Form SEALED(k) tag from KEY(k) in ri4 *)
       [Const (Word.repr 2) ri5;
        Binop OR ri5 ri4 ri4] ++
       wrap_user_tag ri4 ri4 ++
       [PutTag syscall_arg1 ri4 syscall_ret] ++
       (* Check that return PC is tagged DATA *)
       [GetTag ra ri3] ++
       extract_user_tag ri3 rb ri3 ++
       if_ rb [] [Halt _] ++
       [Const (Word.repr 0) ri5;
        Binop EQ ri3 ri5 ri5] ++
       if_ ri5 [Jump ra] [Halt _]
 ).

Definition unseal_segment : @relocatable_segment t w w :=
 gen_syscall_code (fun _ (extra : w) =>
       (* Ensure that second argument is tagged KEY, halting otherwise *)
       [GetTag syscall_arg2 ri4] ++
       extract_user_tag ri4 rb ri4 ++
       if_ rb [] [Halt _] ++
       [Const (Word.repr 3) ri5;
        Binop AND ri4 ri5 ri2;
        Const (Word.repr 1) ri5;
        Binop EQ ri5 ri2 ri5] ++
       if_ ri5 [] [Halt _] ++
       (* Form SEALED(k) tag from KEY(k) in ri4 *)
       [Const (Word.repr 2) ri5;
        Binop OR ri5 ri4 ri4] ++
       (* Ensure that first argument has a user tag (put it in ri3) *)
       [GetTag syscall_arg1 ri3] ++
       extract_user_tag ri3 rb ri3 ++
       if_ rb [] [Halt _] ++
       (* Check that the two tags are equal (i.e. both SEALED(k)) *)
       [Binop EQ ri3 ri4 ri4] ++
       if_ ri5 [] [Halt _] ++
       (* Retag the payload with DATA *)
       [Const (Word.repr 0) ri5] ++
       wrap_user_tag ri5 ri5 ++
       [PutTag syscall_arg1 ri5 syscall_ret] ++
       (* Check that return PC is tagged DATA *)
       (* (not certain this is needed, but keeping it here and above
           to make sure we satisfy refinement hypotheses...) *)
       [GetTag ra ri3] ++
       extract_user_tag ri3 rb ri3 ++
       if_ rb [] [Halt _] ++
       [Const (Word.repr 0) ri5;
        Binop EQ ri3 ri5 ri5] ++
       if_ ri5 [Jump ra] [Halt _]
).

Definition concrete_sealing_monitor :
  Concrete.memory t * w * @classes.sealing_syscall_addrs t :=
  let syscalls := [mkkey_segment; seal_segment; unseal_segment] in
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

Instance ssa : @classes.sealing_syscall_addrs t :=
  snd concrete_sealing_monitor.

Definition build_concrete_sealing_machine
    (user_program : @relocatable_segment t (@classes.sealing_syscall_addrs t) (instr t))
  : Concrete.state concrete_int_32_t
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
    (user_program : @relocatable_segment t (@classes.sealing_syscall_addrs t) (instr t))
  : @Symbolic.state concrete_int_32_t (@Sym.sym_sealing sk_defs) :=
 (* This list should be defined at the same place as the decoding
    function that splits out the addresses for use when generating
    user code *)
 let user_mem : @relocatable_segment t _ _ :=
       map_relocatable_segment
         ((fun v => common.Atom v Sym.DATA) ∘ encode_instr)
         user_program in
 @symbolic_initial_state (@Sym.sym_sealing sk_defs) _
                         user_mem
                         user_memory_addr@Sym.DATA
                         ssa
                         user_registers
                         (common.Atom (Word.repr 0) Sym.DATA)
                         (Word.repr 0).

(* ---------------------------------------------------------------- *)
(* ---------------------------------------------------------------- *)
(* ---------------------------------------------------------------- *)
(* Abstract machine *)

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

(* Minor: Why do PartMaps.get and PartMaps.set take their arguments in
  a different order from Int32PMap.get and Int32PMap.set?? *)

Definition build_abstract_sealing_machine
    (user_program : @relocatable_segment t (@classes.sealing_syscall_addrs t) (instr t))
  : @Abs.state concrete_int_32_t sk :=
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

(* ---------------------------------------------------------------- *)
(* ---------------------------------------------------------------- *)
(* --------------------------------------------------------------- *)
(* Printing, mostly ... *)

(* TODO: Some of this belongs elsewhere, like in concrete/int_32 *)

Open Scope Z_scope.

Require Import String.
Import printing.

Definition format_atom atom :=
  let: w1@w2 := atom in
    match decode_instr w1 with
      Some i => ss "(" +++ format_instr i +++ ss ")@" +++ format_word w2
    | None => format_word w1 +++ ss "@" +++ format_word w2
    end.

Definition print_instr (a : atom) :=
  let: w1@w2 := a in (Word.unsigned w1, decode_instr w1, Word.unsigned w2).

Definition print_atom (a : atom) :=
  let: w1@w2 := a in (Word.unsigned w1, Word.unsigned w2).

Definition format_mvec l :=
  let os := match word_to_op (@Concrete.cop (word t) l) with
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

Require Import Coqlib.

Fixpoint enum (M R S : Type) s (map : M) (get : M -> Word.int s -> R) (f : R -> S) (n : nat) (i : Word.int s) :=
  match n with
  | O => []
  | S p => (Word.unsigned i, f (get map i)) :: enum map get f p (Word.add i (Word.repr 1))
  end.

Definition summarize_concrete_state mem_count cache_count st :=
  let mem' := just_somes
               (@enum _ _ _ _
                 (@Concrete.mem t st)
                 (@PartMaps.get _ (word t) (@word_map_class _) _)
                 (@omap atom sstring format_atom)
                 mem_count
                 (Word.repr 0)) in
  let mem := ssconcat sspace (map (fun x => let: (addr,con) := x in format_Z addr +++ ss ":" +++ con) mem') in
  let regs' := @enum _ _ _ _
                 (@Concrete.regs t st)
                 (@PartMaps.get _ (reg t) (@reg_map_class _) _)
                 (@omap atom sstring format_atom)
                 (Z.to_nat (Word.unsigned user_reg_max))
                 (Word.repr 0) in
  let regs := map (fun r =>
                     let: (x,a) := r in
                     ss "r" +++ format_nat (nat_of_Z x) +++ ss "=" +++
                        match a with
                        | Some a => a
                        | None => ss "_"
                        end)
               regs' in
  let current_instr :=
    let: addr@_ := Concrete.pc st in
    match @PartMaps.get _ (word t) _ _
                    (@Concrete.mem t st)
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

(* ---------------------------------------------------------------- *)
(* Printing symbolic states *)

Definition format_symbolic_atom k (pr_tag : @Symbolic.ttypes (@Sym.sym_sealing sk_defs) k -> sstring) a :=
  let: w1@t2 := a in
    match decode_instr w1 with
      Some i => ss "(" +++ format_instr i +++ ss ")@" +++ pr_tag t2
    | None => format_word w1 +++ ss "@" +++ pr_tag t2
    end.

Definition summarize_symbolic_state mem_count st pr_tag :=
  let mem' := just_somes
               (@enum _ _ _ _
                 (@Symbolic.mem t Sym.sym_sealing st)
                 (@PartMaps.get _ (word t) (@word_map_class _) _)
                 (@omap _ sstring (format_symbolic_atom pr_tag))
                 mem_count
                 (Word.repr 0)) in
  let mem := ssconcat sspace (map (fun x => let: (addr,con) := x in format_Z addr +++ ss ":" +++ con) mem') in
  let regs' := just_somes
                 (@enum _ _ _ _
                    (@Symbolic.regs t Sym.sym_sealing st)
                    (@PartMaps.get _ (reg t) _ _)
                    (@omap _ sstring (format_symbolic_atom pr_tag))
                    (Z.to_nat (Word.unsigned user_reg_max))
                    (Word.repr 0)) in
  let regs := map (fun r =>
                     let: (x,a) := r in
                     ss "r" +++ format_nat (nat_of_Z x) +++ ss "=" +++ a)
               regs' in
  let current_instr :=
    let: addr := Symbolic.pc st in
    match @PartMaps.get _ (word t) _ _
                    (@Symbolic.mem t Sym.sym_sealing st)
                    (val addr) with
      None => ss "(BAD ADDR)"
    | Some i => format_symbolic_atom pr_tag i
    end in
  (to_string
     (ss "PC=" +++ format_symbolic_atom pr_tag (Symbolic.pc st) +++ ss "  "
               +++ current_instr +++
      ss " | " +++
      ssconcat sspace regs +++
      ss " | " +++
      mem)).

Definition format_int {n} (i : Word.int n) :=
  format_Z (Word.unsigned i).

Definition format_sealing_tag k (t : @Symbolic.ttypes (@Sym.sym_sealing sk_defs) k):=
  match t with
    Sym.DATA => ss "DATA"
  | Sym.KEY k => ss "KEY(" +++ format_int k +++ ss ")"
  | Sym.SEALED k => ss "SEALED(" +++ format_int k +++ ss ")"
  end.

Definition summarize_symbolic_sealing_state mem_count st :=
  summarize_symbolic_state mem_count st (@format_sealing_tag Symbolic.M).

(* ---------------------------------------------------------------- *)
(* Printing abstract states *)

Definition format_value v :=
  match v with
  | Abs.VData w =>
      match decode_instr w with
        Some i => ss "(" +++ format_instr i +++ ss ")"
      | None => format_word w
      end
  | Abs.VKey k =>
      ss "KEY(" +++ format_nat k +++ ss ")"
  | Abs.VSealed w k =>
      ss "SEALED(" +++ format_word w +++ ss "," +++ format_nat k +++ ss ")"
  end.

Definition summarize_abstract_state mem_count st :=
  let mem' := just_somes
               (@enum _ _ _ _
                 (@Abs.mem t sk st)
                 (@PartMaps.get _ (word t) _ _)
                 (@omap (@Abs.value t sk) sstring format_value)
                 mem_count
                 (Word.repr 0)) in
  let mem := ssconcat sspace (map (fun x => let: (addr,con) := x in format_Z addr +++ ss ":" +++ con) mem') in
  let regs' := just_somes
                 (@enum _ _ _ _
                    (@Abs.regs t sk st)
                    (@PartMaps.get _ (reg t) _ _)
                    (@omap (@Abs.value t sk) sstring format_value)
                    (Z.to_nat (Word.unsigned user_reg_max))
                    (Word.repr 0)) in
  let regs := map (fun r =>
                     let: (x,a) := r in
                     ss "r" +++ format_nat (nat_of_Z x) +++ ss "=" +++ a)
               regs' in
  let current_instr :=
    let: addr := Abs.pc st in
    match @PartMaps.get _ (word t) _ _
                    (@Abs.mem t sk st)
                    addr with
      None => ss "(BAD ADDR)"
    | Some i => format_value i
    end in
  (to_string
     (ss "PC=" +++ format_word (Abs.pc st) +++ ss "  "
               +++ current_instr +++
      ss " | " +++
      ssconcat sspace regs +++
      ss " | " +++
      mem)).

(* ---------------------------------------------------------------- *)
(* Tests... *)

Definition runn n p :=
  let init := build_concrete_sealing_machine p in
  let tr := utils.runn (@step masks t _) n init in
  (
   summarize_concrete_state 3000 1000 init ::
   map (summarize_concrete_state 8 1) tr
  ).

Definition run := runn 10000.

Definition run_abs n p :=
  let init := build_abstract_sealing_machine p in
  let '(_,_,syscall_addrs) := concrete_sealing_monitor in
  let tr := utils.runn (fun x => Abs.stepf x) n init in
  (
   summarize_abstract_state 3000 init ::
   map (summarize_abstract_state 8) tr
  ).


Definition run_sym n p :=
  let init := build_symbolic_sealing_machine p in
  let '(_,_,syscall_addrs) := concrete_sealing_monitor in
  let tr := utils.runn (fun x => @stepf concrete_int_32_t concrete_int_32_ops
                                 (@Sym.sym_sealing sk_defs)
                                 Sym.sealing_syscalls
                                 x) n init in
  (
   summarize_symbolic_sealing_state 3000 init ::
   map (summarize_symbolic_sealing_state 8) tr
  ).

(* BCP: TODO: Arguably the second argument to f should be a list of
   imm'ediates, not words... *)
(* AAA: TODO: Do we still need user code to take system call address
   as its parameters? After all, we now know all of them. *)
Definition user_code (f : w -> @classes.sealing_syscall_addrs t -> list (instr t))
                  : @relocatable_segment t (@classes.sealing_syscall_addrs t) (instr t) :=
 (List.length (f user_memory_addr ssa),
  f).

Definition hello_world0 : @relocatable_segment t (@classes.sealing_syscall_addrs t) (instr concrete_int_32_t) :=
  user_code (fun _ _ => [
     Const (Word.repr 2) ruser1
  ]).

Definition hello_world1 : @relocatable_segment t (@classes.sealing_syscall_addrs t) (instr concrete_int_32_t) :=
  user_code (fun _ _ => [
    Const (Word.repr 2) ruser1;
    Binop ADD ruser1 ruser1 ruser2
  ]).

Definition hello_world2 : @relocatable_segment t (@classes.sealing_syscall_addrs t) (instr t) :=
  user_code (fun _ _ =>
        [
          Const (Word.casts classes.mkkey_addr) ruser1;
          Jal ruser1;
          Const (Word.casts classes.seal_addr) ruser1;
          Const (Word.repr 17) syscall_arg1;
          Mov syscall_ret syscall_arg2;
          Jal ruser1
        ]
      ).

(* double seal: should fail *)
Definition hello_world3 : @relocatable_segment t (@classes.sealing_syscall_addrs t) (instr concrete_int_32_t) :=
  user_code (fun _ _ =>
        [
          Const (Word.casts classes.mkkey_addr) ruser1;
          Jal ruser1;
          Const (Word.casts classes.seal_addr) ruser1;
          Const (Word.repr 17) syscall_arg1;
          Mov syscall_ret syscall_arg2;
          Jal ruser1;
          Mov syscall_ret syscall_arg1;
          Jal ruser1
        ]
  ).

(* Test seal-then-unseal *)
Definition hello_world4 : @relocatable_segment t (@classes.sealing_syscall_addrs t) (instr concrete_int_32_t) :=
  user_code (fun _ _ =>
        [
          Const (Word.casts classes.mkkey_addr) ruser1;
          Jal ruser1;
          Mov syscall_ret syscall_arg2;
          Const (Word.casts classes.seal_addr) ruser1;
          Const (Word.repr 17) syscall_arg1;
          Jal ruser1;
          Mov syscall_ret syscall_arg1;
          Const (Word.casts classes.unseal_addr) ruser1;
          Jal ruser1
        ]
  ).

(* Test store and load *)
Definition hello_world5 : @relocatable_segment t (@classes.sealing_syscall_addrs t) (instr concrete_int_32_t) :=
  user_code (fun base _ =>
    let data := Word.casts (Word.add base (Word.repr 0)) in
        [
          (* DATA BLOCK *)
          Nop _;
          (* As before, make up a key and seal 17 with it *)
          Const (Word.casts classes.mkkey_addr) ruser1;
          Jal ruser1;
          Mov syscall_ret syscall_arg2;
          Const (Word.casts classes.seal_addr) ruser1;
          Const (Word.repr 17) syscall_arg1;
          Jal ruser1;
          (* Store it in the data block and read it back *)
          Const data ruser1;
          Store ruser1 syscall_ret;
          Load ruser1 ruser2
        ]
  ).

(* Run tests like this:

Concrete Machine: Compute (runn 2000 hello_world5).

Symbolic Machine: Compute (run_sym 2000 hello_world5).

Abstract Machine: Compute (run_abs 2000 hello_world5). *)

Section Refinement.

Instance sp : Symbolic.params := @Sym.sym_sealing sk_defs.

Context {sealing_invariant : policy_invariant t}.

Let monitor_invariant := fault_handler_invariant t ops fhp transfer_function sealing_invariant.

Context {implementation_correct : kernel_code_correctness monitor_invariant Sym.sealing_syscalls}.

Inductive refine_state (ast : Abs.state t) (cst : Concrete.state t) : Prop :=
| rs_intro : forall sst m,
               refinement_common.refine_state monitor_invariant Sym.sealing_syscalls sst cst ->
               @refinementSA.refine_state t sk_defs sk _ nat_partial_map m ast sst ->
               refine_state ast cst.
Hint Constructors refine_state.

Lemma backwards_refinement_as ast sst sst' (m : NatPMap.t _) :
  @refinementSA.refine_state t sk_defs sk _ nat_partial_map m ast sst ->
  exec (Symbolic.step Sym.sealing_syscalls) sst sst' ->
  exists ast' m',
    exec (fun ast ast' => Abs.step ast ast') ast ast' /\
    refinementSA.refine_state m' ast' sst'.
Proof.
  move => REF EXEC.
  elim: EXEC ast m REF => {sst sst'} [sst _ |sst sst' sst'' _ STEPS EXEC IH] ast m REF; first by eauto 7.
  exploit refinementSA.backward_simulation; eauto.
  intros (ast' & m' & STEPA & REF').
  exploit IH; eauto.
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
  generalize (backwards_refinement SC EXECC INUSER).
  move => [sst' [EXECS SC']].
  exploit backwards_refinement_as; eauto.
  intros (ast' & m' & EXECA & AS'). by eauto 7.
Qed.

End Refinement.

End WithClasses.

End SealingInstances.
