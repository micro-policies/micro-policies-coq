Require Import List. Import ListNotations.

(* simple machine, 12 opcodes *)
Inductive Op : Set :=
  | NOP
  | CONST
  | BINOP
  | LOAD
  | STORE
  | JUMP
  | BNZ
  | CALL
  | RETURN
  | ADDRULE
  | GETTAG
  | PUTTAG.

(* T, tdef, and xhandler are modeling the higher-level tags and fault
   handler, built on top of the stack and kernel protection machine *)
Variable T : Set.
Variable tdef : T.

Record XMVec : Set := mkXMVec {
  xop  : Op;
  xtpc : T;
  xti  : T;
  xt1  : T;
  xt2  : T;
  xt3  : T
}.

Record XRVec : Set := mkXRVec {
  xtrpc : T;
  xtr   : T
}.

Variable xhandler : XMVec -> option XRVec.

(* Here are the various kinds of tags we use *)

Inductive PcTag : Set :=
  | KMODE :      PcTag
  | UMODE : T -> PcTag.

(* Initially all stack is tagged STACK KMODE *)
Inductive MemTag : Set :=
  | STACK  : PcTag -> MemTag
  | KERNEL :          MemTag
  | KENTRY :          MemTag
  | UMEM   :     T -> MemTag.

(* This is now the same as PcTag; XXX: consider merging *)
(* BCP: I think merging would make the policy easier to read *)
(* TODO: I'll give it a try *)
Inductive RegTag : Set :=
  | KREG :      RegTag
  | UREG : T -> RegTag.

(* All this could probably be smashed together in one large datatype,
   but I find it much easier to understand this way. Strong types also
   helped a lot when writing the code. *)
Inductive Tag : Set :=
  | TP    : PcTag  -> Tag
  | TM    : MemTag -> Tag
  | TR    : RegTag -> Tag
  | TNONE :           Tag (* TMU doesn't have this argument / result
                             -- this tag can be replaced by dependent types *)
  | TANY  :           Tag.

(* TANY would need to be treated as wildcard by TMU hardware (for us 
   that's part of the semantics of an mvector against the cache).
   Arthur claims that the SAFE TMU can do this kind of wildcards.
   As opposed to TNONE, TANY can be used instead of tags in places
   where also real tags are passed in. Can the HW support this?
   Otherwise how to do ground rules?
   Replacing TANY by dependent types seems much harder than for TNONE
   -- it would make the whole MVec and RVec types dependent not just
   on the instruction, but also on the tag of the pc, in a rather
   nasty way. *)
(* Anyway, using TNONE and TANY seems closer to the way actual HW
   would do things *)

Record MVec : Set := mkMVec {
  op  : Op;
  tpc : Tag;
  ti  : Tag;
  t1  : Tag;
  t2  : Tag;
  t3  : Tag
}.

Record RVec : Set := mkRVec {
  trpc : Tag;
  tr   : Tag
}.

Definition bind (A B:Type) (f:A->option B) (a:option A) : option B :=
    match a with
      | None => None
      | Some a => f a 
    end.
Notation "'do' X <- A ; B" :=
  (bind _ _ (fun X => B) A)
  (at level 200, X ident, A at level 100, B at level 200).
Notation "'do' X : T <- A ; B" :=
  (bind _ _ (fun X : T => B) A)
  (at level 200, X ident, A at level 100, B at level 200).

Definition error {A} : option A := None.

Definition handler (i : MVec) : option RVec :=
  match tpc i with
  | TP KMODE =>
    (* On this machine the kernel (tpc = KMODE) does use the TMU, but
       hopefully it always hits in the cache because of the ground
       rules. This part of the function needs to be compiled to those
       ground rules. See below how this could look like; it's not as
       easy as I first thought. *)
    match ti i with
    | TM KERNEL => (* seems like an invariant;
                      if we can prove it, we don't need to check it *)(* BCP: agree *)
      match op i with
      | STORE => 
        match t1 i, t2 i, t3 i with
        | TR _, TR _ , TM KERNEL => (* kernel only writes to kernel memory (XXX: really?) *)
                                    (* BCP: Hard to imagine why the kernel would want
                                       to write umem, given the jobs we have in mind
                                       right now for the kernel, but... *)
                                    (* XXX: Reading from user mode would cause additional traps *)
          Some (mkRVec (TP KMODE) (TM KERNEL))
        | _, _, _ => error
        end
      | CALL =>
        match t1 i, t2 i with
        | TR _, TM (STACK _) => (* prevents stack from overflowing *)
          Some (mkRVec (TP KMODE) (TM (STACK KMODE))) (* call from kernel mode *)
        | _, _ => error
        end
      | RETURN =>
      (* XXX: Can this really be turned into ground rules? The tag STACK t
         seems to prevent that (we can't enumerate all elements in T).
         This means that the fault handler can itself fault when returning
         to user code, however, only a couple of times:
         - if TM (STACK pc_tag) is not in the cache the return faults,
           which adds a new return address tagged TM (STACK KMODE)
         - the fault handler is called again, and when it returns it
           can fault again, but this 3rd fault can only happen once in
           the whole execution with an infinite cache (or 0 times if
           we add "RETURN ... (TM (STACK KMODE)) ..." as a ground rule)
         While this doesn't seem to lead to an infinite loop, it does seem
         rather inefficient (could double the cost of some faults). *)
        match t1 i with
        | TM (STACK t) => (* this also prevents stack from underflowing *)
          Some (mkRVec (TP t) TNONE)
          (* this allows returns from kernel to user and kernel *)
        | _ => error
        end        
      | _ => (* allows all other instructions in kernel mode *)
             Some (mkRVec (TP KMODE) (TR KREG))
             (* XXX: this mixes TR KREG and TNONE a bit ... it's shorter though :) *)
      end
    | _ => error
    end
  | TP (UMODE ytpc) =>
    match ti i with
    | TM (UMEM yti) =>
      let xhandler' y1 y2 y3 := xhandler (mkXMVec (op i) ytpc yti y1 y2 y3) in
      let ret r t := Some (mkRVec (TP (UMODE (xtrpc r))) t) in
      match op i with
      | NOP =>
        do r <- xhandler' tdef tdef tdef;
        ret r TNONE
      | CONST =>
        do r <- xhandler' tdef tdef tdef;
        ret r (TR (UREG (xtr r)))
      | BINOP =>
        match t1 i, t2 i with
        | TR (UREG yt1), TR (UREG yt2) =>
          do r <- xhandler' yt1 yt2 tdef;
          ret r (TR (UREG (xtr r)))
        | _, _ => error
        end
      | LOAD =>
        match t1 i, t2 i with
        | TR (UREG yt1), TM (UMEM yt2) =>
          do r <- xhandler' yt1 yt2 tdef;
          ret r (TR (UREG (xtr r)))
        | _, _ => error
        end
      | STORE =>
        match t1 i, t2 i, t3 i with
        | TR (UREG yt1), TR(UREG yt2), TM (UMEM yt3) =>
            (* user mode only writes to user memory;
               this protects stack and kernel integrity*)
          do r <- xhandler' yt1 yt2 yt3;
          ret r (TM (UMEM (xtr r)))
        | _, _, _ => error
        end
      | JUMP =>
        match t1 i with
        | TR (UREG yt1) =>
          do r <- xhandler' yt1 tdef tdef;
          ret r TNONE
          (* jump to kernel entry point is also allowed; the change
             from user to kernel happens on the next instruction *)
        | _ => error
        end
      | BNZ => (* exactly the same as for JUMP *)
        match t1 i with
        | TR (UREG yt1) =>
          do r <- xhandler' yt1 tdef tdef;
          ret r TNONE
        | _ => error
        end
      | CALL =>
        match t1 i, t2 i with
        | TR (UREG yt1), TM (STACK _) => (* prevents stack from overflowing *)
          do r <- xhandler' yt1 tdef tdef;
          ret r (TM (STACK (UMODE (xtr r)))) (* call from user mode *)
        | _, _ => error
        end
      | RETURN =>
        match t1 i with
        | TM (STACK _) => (* prevents stack from underflowing *)
          do r <- xhandler' tdef tdef tdef;
          ret r TNONE (* we could change this if we wanted to
                         allow returns from user to kernel *)
        | _ => error
        end        
      | ADDRULE => error (* privileged *)
      | GETTAG  => error (* privileged *)
      | PUTTAG  => error (* privileged *)
      end
    | TM KENTRY => (* system call *)
      match op i with
      | NOP => (* assumming kernel entry points are NOPs *)
        Some (mkRVec (TP KMODE) TNONE)
      | _ => error
      end
    | _ => error
    end
  | _ => error
  end.

Definition ground_rules : list (MVec * RVec) :=
  [(mkMVec NOP (TP KMODE) (TM KERNEL) TNONE TNONE TNONE,
      mkRVec (TP KMODE) TNONE);
   (mkMVec BINOP (TP KMODE) (TM KERNEL) TANY TANY TNONE,
      mkRVec (TP KMODE) (TR KREG));
   (mkMVec LOAD (TP KMODE) (TM KERNEL) TANY TANY TNONE,
      mkRVec (TP KMODE) (TR KREG));
   (mkMVec STORE (TP KMODE) (TM KERNEL) TANY TANY (TM KERNEL),
      mkRVec (TP KMODE) (TM KERNEL));
   (mkMVec JUMP (TP KMODE) (TM KERNEL) TANY TNONE TNONE,
      mkRVec (TP KMODE) TNONE);
   (mkMVec BNZ (TP KMODE) (TM KERNEL) TANY TNONE TNONE,
      mkRVec (TP KMODE) TNONE);
                     (* XXX (STACK KMODE) not general enough below!
                            and partial wildcards like (STACK PCANY)
                            seem quite complicated for the HW.
                            Could clean stack on returns
                            (overwrite it with STACK KMODE)?
                            Or get even more kernel faults. *)
   (mkMVec CALL (TP KMODE) (TM KERNEL) TANY (TM (STACK KMODE)) TNONE,
      mkRVec (TP KMODE) (TM (STACK KMODE)));
                      (* XXX (STACK KMODE) also not general enough below!
                             This leads to kernel faults (discussed above) *)
   (mkMVec RETURN (TP KMODE) (TM KERNEL) (TM (STACK KMODE)) TNONE TNONE,
      mkRVec (TP KMODE) TNONE);
   (mkMVec ADDRULE (TP KMODE) (TM KERNEL) TNONE TNONE TNONE,
      mkRVec (TP KMODE) TNONE);
   (mkMVec GETTAG (TP KMODE) (TM KERNEL) TANY TNONE TNONE,
      mkRVec (TP KMODE) (TR KREG));
   (mkMVec PUTTAG (TP KMODE) (TM KERNEL) TANY TANY TNONE,
      mkRVec (TP KMODE) TNONE)
  ].

(* XXX The problem is that with the new stack protection micro-policy
   in which each stack cell also remembers the high-level tag
   (e.g. memory protection, IFC, etc), the number of ground rules
   needed to make sure that the kernel never faults on call and
   returns is not bounded. There are more ways to go about dealing
   with this described in the file, including letting the kernel fault
   and handle it's own faults, and this idea of requiring the kernel
   to use AddRule explicitly before calls and returns to add the rules
   it needs in order to prevent itself from faulting.

   XXX Another way to solve the kernel trapping because of stack
   problem would be for the kernel (fault handler and system calls) to
   add all rules it needs for itself before it does a call or a
   return. This would require that we also add a way for the kernel to
   read from the stack, so that it knows which rule(s) to add.

   In a finite rule cache (of size >= 2) scenario this solution would
   preclude certain (dumb) cache replacement strategies, which evict
   newly introduced entries (LRU would work though, if addition counts
   as an use). This is not a problem with an infinite cache.

   Alternatively, can we _prove_ that the kernel doesn't cause a stack
   overflow? I guess that wouldn't be so easy in an open/compositional
   world. Also, this would only address the Call problem, not the
   Return problem, where a tag needs to be propagated.

   XXX Another solution to the Kernel return to user mode problem would
   be to add a privileged instruction for doing exactly this. Just that
   the semantics of this instruction would need to take the stack model
   into account? *)



(* Some other discussions *)

(* Q: Does the kernel ever return to user mode with things tagged KREG
   in the registers? That would be strange, but can it be prevented? *)
(* BCP: It could certainly happen if the kernel were miscoded, but I
   don't think it can lead to a bad flow. *)
(* CH: I think that as long as the things marked KREG are not
   accessible from user mode, this won't be a problem. It might make
   the abstract machine on top of this a bit more complicated, but on
   the other hand maintaining a strict registry discipline in the
   kernel might be less efficient. Both seem reasonable though. *)

(* BCP: I find one thing a little confusing: The way it's written
   suggests that TNONE is a possible tag, rather than the absence of a
   tag. *)
(* CH: I just didn't want to get wild with dependent types *)
(* BCP: Agree with that!  But I wonder whether removing TNONE here and 
   adding an option below might be a good alternative? *)
(* CH: Replacing Tag with option Tag in both MVec and RVec seems like
   a pain. I expect some of the ground rules to use TNONE in MVec,
   so we'll see soon. *)
(* CH: probably won't be able to use KREG for that(?) *)
(* BCP: OK  (BTW, go ahead and trim these comments whenever you want.) *)

(* Some pattern match in kernel mode also prevents stack from underflowing *)
(* BCP: Don't follow this bit *)
(* CH: This pattern match is checking that we return to a stack
   element, not somewhere outside the stack if the stack is already
   empty.  Another way to achieve this would be to start the stack at
   the highest address, then some HW mechanism could trap if trying to
   access out of memory. *)
(* BCP: Or just let the machine get stuck / halt... *)
(* CH: yes, just that nothing would change here, since we need the
   pattern-match anyway for getting the new tag on the pc *)
(* CH: or maybe we can just prove that the kernel never underflows the
   stack; that would actually be easier than for overflows; just that
   again we'll have problems in an open/compositional world *)

(* About call to xhandler *)
(* BCP: Ah, this will be a call from kernel code to user code, yes?  In which
   case you were right that the stack protection needs to be built into 
   the kernel protection policy!  But wait... doesn't this also show that
   we need the kernel to be able to write into user memory, so that it can
   construct the user-level MVec?? *)
(* CH: It depends how we set things up. I was thinking of having
   the higher-level fault handler and system calls also in
   kernel mode; similarly to the POPL pico machine. *)
(* BCP: I see.  Then I still think it would be interesting to see whether
   we can move the stack protection to another fault handler that this one
   calls (and that, in turn, calls the one that this one is currently 
   calling). *)
(* CH: I'm skeptical that this would work (please see 2.1 in PDF),
   but we could try it later on. *)
(* BCP: OK, I see your reasons for scepticism.  OK with me to leave 
   it as-is for now. *)

(* assumming kernel entry points are NOPs *)
(* BCP: That's OK if it makes things a lot easier, but we'll
   save a cycle if we let it be an arbitrary instruction. *)
(* CH: we could basically treat tpc=UMODE and ti=KENTRY
   as also being kernel mode. TODO: try this out *)
(* BCP: Yes, we discussed this yesterday.  Seems cleaner to
   have just one kernel-mode tag instead of two. *)
