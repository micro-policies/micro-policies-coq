Require Import List. Import ListNotations.

(* simple machine, 13 lucky opcodes *)
Inductive Op : Set :=
  | NOP (* XXX nop is now gone! try to get rid of it*)
  | CONST
  | BINOP
  | LOAD
  | STORE
  | JUMP
  | BNZ
  | JAL
  | WRITEEPC
  | JUMPEPC
  | ADDRULE
  | GETTAG
  | PUTTAG.

(* T, tdef, and xhandler are modeling the higher-level tags and fault
   handler, built on top of the kernel protection machine (but still
   living in kernel space) *)
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

(* Here are the various kinds of tags we use.
   For the PC:
   - KERNEL : for kernel mode
   - USER t : for user mode
   For registers:
   - KERNEL : for data only used in the kernel
   - USER t : for data only used in user mode
   For memory: 
   - KERNEL : for most of the kernel
   - KENTRY : for kernel entry points
   - USER t : for user space
*)

(* All this is now smashed together in one large datatype,
   although stronger types helped a lot when writing the code. *)
Inductive Tag : Set :=
  | USER   :  T -> Tag
  | KERNEL :       Tag
  | KENTRY :       Tag
  | TNONE  :       Tag (* TMU doesn't have this argument / result
                          -- this tag can be replaced by dependent types *)
  | TANY   :       Tag.

(* TANY would need to be treated as wildcard by TMU hardware (for us 
   that's part of the semantics of an mvector against the cache).
   As opposed to TNONE, TANY can be used instead of tags in places
   where also real tags are passed in.
   Arthur claims that the SAFE TMU can do this kind of wildcards.
   Otherwise how to do ground rules?
   Replacing TANY by dependent types seems much harder than for TNONE
   -- it would make the whole MVec and RVec types dependent not just
   on the instruction, but also on the tag of the pc, in a rather
   nasty way. *)
(* Anyway, using TNONE and TANY seems closer to the way actual HW
   would do things *)
(* CH (2014-01-15): It seems we were wrong about some of this. The HW
   has a mechanism based on don't care bits that seems more
   constrained than what we use here (one care mask per instruction
   set or per label model). *)

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
  | KERNEL => error (* we can't handle faults in kernel mode;
                         but we have ground rules for this *)
  | USER ytpc =>
    match ti i with
    | USER yti =>
      let xhandler' y1 y2 y3 := xhandler (mkXMVec (op i) ytpc yti y1 y2 y3) in
      let ret r t := Some (mkRVec (USER (xtrpc r)) t) in
      match op i with
      | NOP =>
        do r <- xhandler' tdef tdef tdef;
        ret r TNONE
      | CONST =>
        do r <- xhandler' tdef tdef tdef;
        ret r (USER (xtr r))
      | BINOP =>
        match t1 i, t2 i with
        | USER yt1, USER yt2 =>
          do r <- xhandler' yt1 yt2 tdef;
          ret r (USER (xtr r))
        | _, _ => error
        end
      | LOAD =>
        match t1 i, t2 i with
        | USER yt1, USER yt2 =>
          do r <- xhandler' yt1 yt2 tdef;
          ret r (USER (xtr r))
        | _, _ => error
        end
      | STORE =>
        match t1 i, t2 i, t3 i with
        | USER yt1, USER yt2, USER yt3 =>
            (* user mode only writes to user memory;
               this protects kernel's integrity *)
          do r <- xhandler' yt1 yt2 yt3;
          ret r (USER (xtr r))
        | _, _, _ => error
        end
      | JUMP =>
        match t1 i with
        | USER yt1 =>
          do r <- xhandler' yt1 tdef tdef;
          ret r TNONE
          (* jump to kernel entry point is also allowed (not just
             JAL); the change from user to kernel happens on the next
             instruction; the kernel will jump back to whatever is in
             ra at the moment of the jump -- so not extremely useful *)
        | _ => error
        end
      | BNZ => (* exactly the same as for JUMP *)
        match t1 i with
        | USER yt1 =>
          do r <- xhandler' yt1 tdef tdef;
          ret r TNONE
        | _ => error
        end
      | JAL => 
        match t1 i with
        | USER yt1 =>
          do r <- xhandler' yt1 tdef tdef;
          ret r (USER (xtr r))
        | _ => error
        end
      | WRITEEPC => error (* privileged *)
      | JUMPEPC  => error (* privileged *)
      | ADDRULE  => error (* privileged *)
      | GETTAG   => error (* privileged *)
      | PUTTAG   => error (* privileged *)
      end
    | KENTRY => (* system call *)
      match op i with
      | NOP => (* assumming kernel entry points are NOPs *)
        Some (mkRVec KERNEL TNONE)
      | _ => error
      end
    | _ => error
    end
  | _ => error
  end.

Definition ground_rules : list (MVec * RVec) :=
  [(mkMVec NOP KERNEL KERNEL TNONE TNONE TNONE,
      mkRVec KERNEL TNONE);
   (mkMVec BINOP KERNEL KERNEL TANY TANY TNONE,
      mkRVec KERNEL KERNEL);
   (mkMVec LOAD KERNEL KERNEL TANY TANY TNONE,
      mkRVec KERNEL KERNEL);
   (mkMVec STORE KERNEL KERNEL TANY TANY KERNEL,
      mkRVec KERNEL KERNEL);
   (* kernel only writes to kernel memory (XXX: really?) *)
   (* BCP: Hard to imagine why the kernel would want to write umem,
      given the jobs we have in mind right now for the kernel,
      but... *)
   (* XXX: Reading from user mode would cause kernel faults;
      and writing might fault too because of reading old tag *)
   (mkMVec JUMP KERNEL KERNEL TANY TNONE TNONE,
      mkRVec KERNEL TNONE);
   (mkMVec BNZ KERNEL KERNEL TANY TNONE TNONE,
      mkRVec KERNEL TNONE);
   (mkMVec JAL KERNEL KERNEL TANY TNONE TNONE,
      mkRVec KERNEL KERNEL);
   (mkMVec WRITEEPC KERNEL KERNEL TANY TNONE TNONE,
      mkRVec KERNEL TNONE);
   (mkMVec JUMPEPC KERNEL KERNEL TNONE TNONE TNONE,
      mkRVec TNONE TNONE);
   (mkMVec ADDRULE KERNEL KERNEL TNONE TNONE TNONE,
      mkRVec KERNEL TNONE);
   (mkMVec GETTAG KERNEL KERNEL TANY TNONE TNONE,
      mkRVec KERNEL KERNEL);
   (mkMVec PUTTAG KERNEL KERNEL TANY TANY TNONE,
      mkRVec KERNEL TNONE)
  ].

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
(* CH: The fault handler needs to restore all registers; so only the
   system calls can leave registers dirty (whether that's allowed
   should be a matter of calling convention) *)

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
(* BCP: OK *)
(* CH (2014-01-15): Should consider reverting this decision after
   discussion with Andre. *)

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
(* CH: I'm skeptical that this would work (please see 2.1 in stackful PDF),
   but we could try it later on. *)
(* BCP: OK, I see your reasons for scepticism.  OK with me to leave 
   it as-is for now. *)

(* assumming kernel entry points are NOPs *)
(* BCP: That's OK if it makes things a lot easier, but we'll
   save a cycle if we let it be an arbitrary instruction. *)
(* CH: we could basically treat tpc=UMODE t and ti=KENTRY
   as also being kernel mode -- just that we would have
   problems writing ground rules for this case!! *)
(* BCP: Yes, we discussed this yesterday.  Seems cleaner to
   have just one kernel-mode tag instead of two. *)
