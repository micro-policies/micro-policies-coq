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
Require Import trivial.symbolic.
Require Import Integers.
Require Import Omega.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import DoNotation.

Module TrivialInstances.

Section WithClasses.

(* ---------------------------------------------------------------- *)
(* int32 instance *)

Definition t := concrete_int_32_t.
Instance ops : machine_ops t := concrete_int_32_ops.
Instance fhp : fault_handler_params t := concrete_int_32_fh.
Instance symtriv : Symbolic.params := Sym.sym_trivial. 

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
(* Main definitions for concrete trivial machine *)

Import Word.Notations.

Ltac inv H := (inversion H; subst; clear H).

Definition encode_trivial_tag (t : Sym.ttag) : Word.int 29 :=
  Word.zero.

Definition decode_trivial_tag (t : Word.int 29) : option Sym.ttag :=
  if t == Word.zero then
    Some (Sym.DUMMY)
  else 
    None.

Lemma encode_trivial_tagK t : decode_trivial_tag (encode_trivial_tag t) = Some t.
Proof.
  unfold decode_trivial_tag, encode_trivial_tag. destruct t;auto.
Qed.

Lemma decode_trivial_tagK w t : decode_trivial_tag w = Some t ->
                                encode_trivial_tag t = w.
Proof.
  unfold decode_trivial_tag, encode_trivial_tag. 
  have [?|?] := altP (w =P Word.zero); try subst w'. auto.
  intro X; inv X. 
Qed.

Instance encodable_tag : @encodable t Sym.ttag_eqType := {|
  encode t :=
    match t with
    | USER ut => Word.pack [29; 1] [encode_trivial_tag ut; Word.one]%wp
    | ENTRY ut => Word.pack [29; 1] [encode_trivial_tag ut; Word.repr 2]%wp
    | KERNEL => Word.pack [29; 1] [Word.zero; Word.zero]%wp
    end;

  decode w :=
    let: [ut; w']%wu := Word.unpack [29; 1] w in
    if w' == Word.zero then
      if ut == Word.zero then Some KERNEL
      else None
    else if w' == Word.one then
      do! ut <- decode_trivial_tag ut;
      Some (@USER Sym.ttag_eqType ut)
    else if w' == Word.repr 2 then
      do! ut <- decode_trivial_tag ut;
      Some (@ENTRY Sym.ttag_eqType ut)
    else None;

  encode_kernel_tag := erefl
|}.
Proof.
  - case => [ut| |ut].
    rewrite Word.packK;  simpl; destruct ut; auto. 
    rewrite Word.packK;  simpl;  auto. 
    rewrite Word.packK;  simpl; destruct ut; auto. 
  - intros t w.
    case E: (Word.unpack [29; 1] w) => [ut [w' []]].
    move: (Word.unpackK [29; 1] w). rewrite E.
    have [?|?] := altP (w' =P Word.zero); try subst w'.
    { have [?|?] := altP (ut =P Word.zero); try subst ut; last by [].
      by move => H [<-]. }
    have [?|?] := altP (w' =P Word.one); try subst w'.
    { case DEC: (decode_trivial_tag ut) => [ut'|] //=.
      apply decode_trivial_tagK in DEC. subst ut.
      by move => H [<-]. }
    have [?|?] := altP (w' =P Word.repr 2); try subst w'; last by [].
    case DEC: (decode_trivial_tag ut) => [ut'|] //=.
    apply decode_trivial_tagK in DEC. subst ut.
    by move => H [<-].
Qed.

Definition DUMMY : word t := Word.repr 0.

Definition transfer_function : list (instr t) :=
 [Const (Word.casts DUMMY) rtrpc;
  Const (Word.casts DUMMY) rtr].

Definition fault_handler : @relocatable_segment t w w :=
 kernel_code (fault_handler.handler t fhp transfer_function).

(*
(* Printing out the handler code *)

Require Import String.
Import printing.
Compute (to_string (snd (foldl 
            (fun (ns:nat * sstring) i => let (n,s) := ns in 
               (S n, s +++ format_nat n +++ schar " " +++ format_instr i +++ schar "010" ))
            (1,ssempty) 
            (fault_handler.handler t fhp transfer_function)))). 
*)

Definition extra_state : @relocatable_segment t w w :=
 kernel_data [].

Definition gen_syscall_code gen : @relocatable_segment t w w :=
 (length (gen (Word.repr 0) (Word.repr 0)),
  fun b w => map encode_instr (gen b w)).

Definition concrete_trivial_monitor :
  Concrete.memory t * w :=
  let syscalls := [] in
  let res := build_monitor_memory extra_state fault_handler syscalls in
  let monitor_memory := fst (fst res) in
  let user_memory_addr := snd (fst res) in
  (monitor_memory, user_memory_addr).

Definition concrete_trivial_monitor_memory :=
  fst concrete_trivial_monitor.

Definition user_memory_addr :=
  snd concrete_trivial_monitor.

Definition build_concrete_trivial_machine
    (user_program : @relocatable_segment t unit (instr t))
  : Concrete.state concrete_int_32_t
     :=
 (* This list should be defined at the same place as the decoding
    function that splits out the addresses for use when generating
    user code *)
 let user_mem :=
       map_relocatable_segment
         (fun x => Atom (encode_instr x) DUMMY)
         user_program in
 concrete_initial_state
   concrete_trivial_monitor_memory
   user_memory_addr
   tt
   user_mem
   DUMMY
   user_registers
   DUMMY.

(* Based on the definitions in fault_handler,.... *)

Definition invariant_statement 
           (_:Concrete.memory t)
           (_:Symbolic.internal_state) := True.

Lemma invariant_upd_mem :
    forall mem mem' addr w1 ut  w2 int
           (PINV : invariant_statement mem int)
           (GET : PartMaps.get mem addr = Some w1@(encode (USER ut))) 
                      (* @encode _ _ (Symbolic.ttypes Symbolic.M) ((fun _ => encodable_tag) Symbolic.M) (USER ut))) *)
           (UPD : PartMaps.upd mem addr w2 = Some mem'),
      invariant_statement mem' int.
Proof.
  intros; auto.
Qed.

Lemma invariant_store_mvec :
    forall mem mem' mvec int
           (KINV : invariant_statement mem int)
           (MVEC : Concrete.store_mvec mem mvec = Some mem'),
    invariant_statement mem' int.
Proof.
  intros; auto.
Qed.

Definition trivial_policy_invariant : policy_invariant t := {|
  policy_invariant_statement := invariant_statement;  
  policy_invariant_upd_mem := invariant_upd_mem; 
  policy_invariant_store_mvec := invariant_store_mvec
|}.


Definition ki := fault_handler_invariant t ops fhp transfer_function trivial_policy_invariant. 

(* Based on the definitions in refinement_common,.... *)

Definition handler := @rules.handler t _ _ (fun x => @Symbolic.transfer symtriv x).



Definition handler_correct_allowed : Prop :=
  forall mem mem' cmvec crvec reg cache old_pc int,
    (* If kernel invariant holds... *)
    ki mem reg cache int -> 
    (* and calling the handler on the current m-vector succeeds and returns rvec... *)
    handler cmvec = Some crvec ->
    (* and storing the concrete representation of the m-vector yields new memory mem'... *)
    Concrete.store_mvec mem cmvec = Some mem' ->
    (* and the concrete rule cache is correct (in the sense that every
       rule it holds is exactly the concrete representations of
       some (mvec,rvec) pair in the relation defined by the [handler]
       function) ... *)
    cache_correct cache ->
    (* THEN if we start the concrete machine in kernel mode (i.e.,
       with the PC tagged TKernel) at the beginning of the fault
       handler (and with the current memory, and with the current PC
       in the return-addr register epc)) and let it run until it
       reaches a user-mode state st'... *)
    exists st',
      kernel_user_exec
        (Concrete.mkState mem' reg cache
                          (Concrete.fault_handler_start _)@Concrete.TKernel
                          old_pc)
        st' /\
      (* then the new cache is still correct... *)
      cache_correct (Concrete.cache st') /\
      (* and the new cache now contains a rule mapping mvec to rvec... *)
      Concrete.cache_lookup (Concrete.cache st') masks cmvec = Some crvec /\
      (* and the mvec has been tagged as kernel data (BCP: why is this important??) *)
      mvec_in_kernel (Concrete.mem st') /\
      (* and we've arrived at the return address that was in epc with
         unchanged user memory and registers... *)
      user_mem_unchanged mem (Concrete.mem st') /\
      user_regs_unchanged reg (Concrete.regs st') /\
      Concrete.pc st' = old_pc /\
      (* and the system call entry points are all tagged ENTRY (BCP:
         Why do we care, and if we do then why isn't this part of the
         kernel invariant?  Could user code possibly change it?) *)
      wf_entry_points Sym.trivial_syscalls (Concrete.mem st')  /\ 
      (* and the kernel invariant still holds. *)
      ki (Concrete.mem st') (Concrete.regs st') (Concrete.cache st') int 
.

Require Import concrete.eval.

Let patom := common.atom (pvalue t) (pvalue t).

(* Setting up initial state of parametric machine, specifially at
entry to the fault handler.  We can try to generalize this later. *)

Definition pkernelize (seg : @relocatable_segment concrete_int_32_t w w)
                   : relocatable_segment w patom :=
  let (l,gen) := seg in
  (l, fun b rest => map (fun x => (C t x)@(C t Concrete.TKernel)) (gen b rest)).


(* Kludge: temporarily treat epc as having a real register number. *)
Definition epc_reg : reg t := Word.repr 1000.

Fixpoint pmem_from (i : Word.int 31) (n : nat) x 
                        (mem : word_map t patom) : word_map t patom :=
  match n with
    | O    => mem
    | S n' => pmem_from (Word.add i Word.one) n' x 
                              (PartMaps.set mem i (V t (MP t i))@x)
  end.

Definition preg_at x (regs : reg_map t patom) (r: reg t) : reg_map t patom :=
  PartMaps.set regs r (V t (RP t r))@x.

Definition parametric_initial_state: pstate concrete_int_32_t :=
  let gen_cache := pmem_from Word.zero 8 (C t Concrete.TKernel) in
  let base_addr := Concrete.fault_handler_start _ in
  let (handler_length,handler_segment) := pkernelize fault_handler in
  let kernel_code := handler_segment base_addr (Word.reprn handler_length) in
  let gen_kernel_code := insert_from base_addr kernel_code in
  let extra_state_addr := Word.add base_addr
                                     (Word.reprn handler_length) in
  let user_code_addr := extra_state_addr (* since there is no exta state *) in 
  let user_code_length := 1%nat in (* very arbitrary ! *)
  let gen_user_code := pmem_from user_code_addr user_code_length 
                                 (C t (kernelize_user_tag DUMMY)) in
  let mem := 
       ( gen_cache 
       ∘ gen_kernel_code
       ∘ gen_user_code )
       (PartMaps.empty) in
  let kregs :=
      fold_left (preg_at (C t Concrete.TKernel)) 
        (kernel_regs t concrete_int_32_fh)
        PartMaps.empty in
  let regs :=    (* all the "standard" user regs: a bit arbitrary! *)
         fold_left (preg_at (C t (kernelize_user_tag DUMMY)))
          user_registers
          kregs in
  {| pmem := mem;
     pregs  := regs;
     pcache := []; (* too simple? *)
     ppc  := (C t (Concrete.fault_handler_start _))@(C t Concrete.TKernel);
     pepc := (V t (RP t epc_reg))@(C t (kernelize_user_tag DUMMY))
  |}
.

Set Printing Depth 20. 


(* teval is much faster than pkue *)

Fixpoint extract_pcs (ts: tstate t) : list patom :=
match ts with
| Halted => []
| St ps => [ppc t ps]
| Ch _ s1 s2 => extract_pcs s1 ++ extract_pcs s2
end. 

(* Compute (match (teval t masks 40 (St _ parametric_initial_state))
         with Some ts => extract_pcs ts | None => [] end).  *)
  

(* REDEFINE some things from concrete/eval.v *)

(* This version is unsound, but it lets us investigate behavior with much
smaller step counts.  *)
Fixpoint tdistr (f: pstate t -> option (tstate t)) (ts: (tstate t)) : option (tstate t) :=
  match ts with
  | Halted => Some (Halted _)
  | St s => f s
  | Ch z s1 s2 =>
      match tdistr f s1,tdistr f s2 with
      | Some l,Some r => Some (Ch _ z l r)
      | Some l,None  => Some l
      | None,Some r => Some r
      | None, None => None
      end
   end.

(* Hack to distinguish initial not-in-kernel failures from running out of steps. *)
Definition marker: pstate t := 
  mkPState _ PartMaps.empty PartMaps.empty [] ((C t (Word.repr 777))@(C t (Word.repr 888))) ((C t (Word.repr 999))@(C t (Word.repr 666))). 

Fixpoint pkuer (max_steps:nat) (k:pstate t -> option (tstate t)) (ps:(pstate t)) : option (tstate t) :=
  do! u <- known _ (common.tag (ppc t ps));
  if Concrete.is_kernel_tag u then
    match max_steps with
    | O => None 
    | S max_steps' =>
      do! ts <- pstep _ masks ps;
      tdistr (pkuer max_steps' (fun ps => Some(St _ ps))) ts
    end
  else k ps.

Definition pkue (max_steps:nat) (ps:pstate t) : option (tstate t) :=
   pkuer max_steps (fun _ => Some (St _ marker)) ps.  

(* Compute (match (pkue 40  parametric_initial_state)
         with Some ts => extract_pcs ts | None => [] end).    *)

Definition mvec_stored (mem : Concrete.memory t) (mv : Concrete.MVec w) : Prop := 
  PartMaps.get mem (Concrete.Mop t) = Some (Concrete.cop mv)@Concrete.TKernel /\ 
  PartMaps.get mem (Concrete.Mtpc t) = Some (Concrete.ctpc mv)@Concrete.TKernel /\ 
  PartMaps.get mem (Concrete.Mti t) = Some (Concrete.cti mv)@Concrete.TKernel /\ 
  PartMaps.get mem (Concrete.Mt1 t) = Some (Concrete.ct1 mv)@Concrete.TKernel /\ 
  PartMaps.get mem (Concrete.Mt2 t) = Some (Concrete.ct2 mv)@Concrete.TKernel /\ 
  PartMaps.get mem (Concrete.Mt3 t) = Some (Concrete.ct3 mv)@Concrete.TKernel. 

Lemma phandler_correct_allowed :
  forall env cmvec crvec,
    let st := concretize_pstate _ env parametric_initial_state in
    (* If kernel invariant holds... *)
    ki (Concrete.mem st) (Concrete.regs st) (Concrete.cache st) tt ->
    (* and calling the handler on the current m-vector succeeds and returns rvec... *)
    handler cmvec = Some crvec ->
    (* and memory contains the the concrete representation of the m-vector ...
       NB This differs from the existing correctness condition, which builds
       the memory description in two stages. I don't quite see how to do that in parametric world... *)
    mvec_stored (Concrete.mem st) cmvec -> 
    (* and the concrete rule cache is correct (in the sense that every
       rule it holds is exactly the concrete representations of
       some (mvec,rvec) pair in the relation defined by the [handler]
       function) ... *)
    cache_correct (Concrete.cache st) ->
    (* THEN if we start the concrete machine in kernel mode (i.e.,
       with the PC tagged TKernel) at the beginning of the fault
       handler (and with the current memory, and with the current PC
       in the return-addr register epc)) and let it run until it
       reaches a user-mode state st'... *)
  exists ts', pkue 40 parametric_initial_state = Some ts' /\
   exists st', Some st' = concretize_tstate t env ts' /\
       cache_correct (Concrete.cache st') /\
      (* and the new cache now contains a rule mapping mvec to rvec... *)
      Concrete.cache_lookup (Concrete.cache st') masks cmvec = Some crvec /\
      (* and the mvec has been tagged as kernel data (BCP: why is this important??) *)
      mvec_in_kernel (Concrete.mem st') /\
      (* and we've arrived at the return address that was in epc with
         unchanged user memory and registers... *)
      user_mem_unchanged (Concrete.mem st) (Concrete.mem st') /\
      user_regs_unchanged (Concrete.regs st) (Concrete.regs st') /\
      Concrete.pc st' = Concrete.epc st /\
      (* and the system call entry points are all tagged ENTRY (BCP:
         Why do we care, and if we do then why isn't this part of the
         kernel invariant?  Could user code possibly change it?) *)
      wf_entry_points Sym.trivial_syscalls (Concrete.mem st')  /\ 
      (* and the kernel invariant still holds. *)
      ki (Concrete.mem st') (Concrete.regs st') (Concrete.cache st') tt.
Proof.
  intros. 
  vm_compute in st. subst st. 
  unfold Concrete.mem in *.  unfold Concrete.regs in *.
  unfold Concrete.cache in *.  unfold Concrete.pc in *. 
  unfold Concrete.epc in *. 
  (* that was overkill, but simpl runs forever *)
  destruct H1 as [? [? [? [? [? ?]]]]].
  unfold Concrete.Mtpc, Concrete.cache_line_addr in H3.
  change (0 + Word.repr 1)%w with ((Word.repr 1):w) in H3.
  simpl in H3. vm_compute in H3. 
  destruct cmvec. vm_compute in H3. injection H3. clear H3; intro H3. 
  clear H1 H4 H5 H6 H7. (* temporarily, for printing speed *)
  clear H. (* ditto *)
  idtac. 
  unfold handler in H0. unfold rules.handler in H0. 
  undo. unfold decode_ivec in Heqo. simpl in Heqo. 
  (* undo is too slow so we're screwed here *)

  eexists. split.
  match goal with |- ?A = ?B => set z := A end. 
  vm_compute in z; reflexivity.
  unfold concretize_tstate, concretize_pvalue.

  (* factoid we will want first is that ctpc = user. how do
     we establish that?  via uivec_of_ivec, I believe. *)
Admitted.

End WithClasses.

End TrivialInstances.
