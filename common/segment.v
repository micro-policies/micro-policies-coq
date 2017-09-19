From mathcomp Require Import
  ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype div ssrint ssralg
  intdiv.
From CoqUtils Require Import ord word fmap.

Require Import lib.utils common.types.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Relocation.

Context {mt : machine_types}
        {ops : machine_ops mt}.

(* The type of relocatable memory segments.  The first nat specifies
   the segment's size.  The argument type specifies what kind of
   relocation information is needed (e.g., nothing for constant
   segments; just one word for relocatable code; a pair of words for
   relocatable code that also needs access to a shared data area).

   TODO: One issue is that we need the resulting list to always be of
   the specified size, but the type does not demand this at the
   moment.  One way to deal with this is to add a proof component that
   certifies that the resulting list always has the specified length.
   Is there a better way?  (This seems not too bad: our structured
   code combinators can build these certificates pretty easily.) *)

Definition relocatable_segment :=
  fun Args => fun Cell => (nat * (mword mt -> Args -> seq Cell))%type.

Definition empty_relocatable_segment (Args Cell : Type) : relocatable_segment Args Cell :=
  (0, fun (base : mword mt) (rest : Args) => [::]).

(* Concatenates list of relocatable segments into one, returning a
   list of offsets (relative to the base address). *)
Definition concat_and_measure_relocatable_segments
             (Args Cell : Type)
             (segs : seq (relocatable_segment Args Cell))
           : relocatable_segment Args Cell * seq nat :=
  foldl
    (fun (p : relocatable_segment Args Cell * seq nat)
         (seg : relocatable_segment Args Cell) =>
       let: (acc,addrs) := p in
       let (l1,gen1) := acc in
       let (l2,gen2) := seg in
       let gen := fun (base : mword mt) (rest : Args) =>
                       gen1 base rest
                    ++ gen2 (addw base (as_word l1)) rest in
       let newseg := (l1+l2, gen) in
       (newseg, addrs ++ [:: l1]))
    (empty_relocatable_segment _ _, [::])
    segs.

Definition concat_relocatable_segments
             (Args Cell : Type)
             (segs : seq (relocatable_segment Args Cell))
           : relocatable_segment Args Cell :=
  fst (concat_and_measure_relocatable_segments segs).

Definition map_relocatable_segment
             (Args Cell Cell' : Type)
             (f : Cell -> Cell')
             (seg : relocatable_segment Args Cell)
           : relocatable_segment Args Cell' :=
  let (l,gen) := seg in
  let gen' := fun (base : mword mt) (rest : Args) => map f (gen base rest) in
  (l, gen').

Definition relocate_ignore_args
             (Args Cell : Type)
             (seg : relocatable_segment unit Cell)
           : relocatable_segment Args Cell :=
  let (l,gen) := seg in
  let gen' := fun (base : mword mt) (rest : Args) => gen base tt in
  (l, gen').

End Relocation.

Ltac current_instr_opcode :=
  match goal with
  | H : decode_instr _ = Some ?instr |- _ =>
    let op := (eval compute in (opcode_of instr)) in
    op
  end.
