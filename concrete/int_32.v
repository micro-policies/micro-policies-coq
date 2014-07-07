(* Instantiate the concrete machine with 32-bit integers *)

Require Import ZArith.
Require Import Integers.
Require Import List.
Require Import Bool.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Import ListNotations.

Require Import lib.Coqlib.
Require Import lib.FiniteMaps.
Require Import lib.utils.
Require Import lib.partial_maps.
Require Import lib.ordered.
Require Import common.common common.printing.
Require Import concrete.concrete.

Import DoNotation.

(* We have to use the same Int module that the maps use. *)

Module Wordsize_32 <: WORDSIZE.

Definition wordsize_minus_one := 31.

End Wordsize_32.

Module Wordsize_5 <: WORDSIZE.

Definition wordsize_minus_one := 4.

End Wordsize_5.

Module Int32Ordered := IntOrdered Wordsize_32.
Module Int32Indexed := Int32Ordered.IntIndexed.
Module Int5Ordered := IntOrdered Wordsize_5.
Module Int5Indexed := Int5Ordered.IntIndexed.

Import Word.

Definition int32 := int 31.

Lemma int32_eqP : Equality.axiom (@eq 31).
Proof.
move=> x y; apply: (iffP idP) => [|->].
  by have := Word.eq_spec _ x y; case: (Word.eq x y).
by rewrite Word.eq_true.
Qed.

Definition int32_eqMixin := EqMixin int32_eqP.
Canonical int32_eqType := Eval hnf in EqType int32 int32_eqMixin.

Definition regt := int 4. (* 5 bits *)

Lemma regt_eqP : Equality.axiom (@eq 4).
Proof.
move=> x y; apply: (iffP idP) => [|->].
  by have := Word.eq_spec _ x y; case: (Word.eq x y).
by rewrite Word.eq_true.
Qed.

Definition regt_eqMixin := EqMixin regt_eqP.
Canonical regt_eqType := Eval hnf in EqType regt regt_eqMixin.

Definition immt := int 14. (* 15 bits *)

Lemma immt_eqP : Equality.axiom (@eq 14).
Proof.
move=> x y; apply: (iffP idP) => [|->].
  by have := Word.eq_spec _ x y; case: (Word.eq x y).
by rewrite Word.eq_true.
Qed.

Definition immt_eqMixin := EqMixin immt_eqP.
Canonical immt_eqType := Eval hnf in EqType immt immt_eqMixin.

Module Int32PMap := FiniteMap      Int32Indexed.
Module RegtPMap  := FiniteMap      Int5Indexed.
Module RegtTMap  := FiniteTotalMap Int5Indexed.

(* These types will yield an incorrect (but still executable/useful) encoding *)
(* CH: What's incorrect about it?  Is it the fact that you're
   abusing int instead of using a more precise type? *)
Definition concrete_int_32_t : machine_types := {|
  word := int32_eqType;
  reg := regt_eqType;
  imm := immt_eqType;
  word_map := Int32PMap.t;
  reg_map := RegtPMap.t;
  reg_tmap := RegtTMap.t
|}.

Instance int_ordered : @Ordered (word concrete_int_32_t) (eqType_EqDec (word concrete_int_32_t)) :=
  {| compare := compare;
     compare_refl := compare_refl;
     compare_asym :=compare_asym;
     compare_eq :=compare_eq;
     compare_lt_trans :=compare_lt_trans;
     compare_gt_trans := compare_gt_trans
|}.

Import Word.Notations.
Import ListNotations.

Definition encode_opcode (o : opcode) : int 4 :=
  repr (op_to_Z o).

Definition decode_opcode (o : int 4) : option opcode :=
  Z_to_op (unsigned o).

Lemma encode_opcodeK o : decode_opcode (encode_opcode o) = Some o.
Proof.
  case o; try case; reflexivity.
Qed.

Instance concrete_int_32_ops : machine_ops concrete_int_32_t := {|
  encode_instr i :=
    let op := encode_opcode (opcode_of i) in
    match i with
    | Nop => pack [4; 26] [op; zero]%wp
    | Const i r => pack [4; 14; 4; 6] [op; i; r; zero]%wp
    | Mov r1 r2 => pack [4; 4; 4; 16] [op; r1; r2; zero]%wp
    | Binop _ r1 r2 r3 => pack [4; 4; 4; 4; 11] [op; r1; r2; r3; zero]%wp
    | Load r1 r2 => pack [4; 4; 4; 16] [op; r1; r2; zero]%wp
    | Store r1 r2 => pack [4; 4; 4; 16] [op; r1; r2; zero]%wp
    | Jump r => pack [4; 4; 21] [op; r; zero]%wp
    | Bnz r i => pack [4; 4; 14; 6] [op; r; i; zero]%wp
    | Jal r => pack [4; 4; 21] [op; r; zero]%wp
    | JumpEpc => pack [4; 26] [op; zero]%wp
    | AddRule => pack [4; 26] [op; zero]%wp
    | GetTag r1 r2 => pack [4; 4; 4; 16] [op; r1; r2; zero]%wp
    | PutTag r1 r2 r3 => pack [4; 4; 4; 4; 11] [op; r1; r2; r3; zero]%wp
    | Halt => pack [4; 26] [op; zero]%wp
    end;

  decode_instr i :=
    let: (op, rest) := @unpack2 4 26 i in
    let t := concrete_int_32_t in
    do! op <- decode_opcode op;
    match op : let int := reg concrete_int_32_t in opcode with
    | NOP => Some (Nop t)
    | CONST => let: [i; r; _]%wu := unpack [14; 4; 6] rest in
               Some (Const t i r)
    | MOV => let: [r1; r2; _]%wu := unpack [4; 4; 16] rest in
             Some (Mov t r1 r2)
    | BINOP op => let: [r1; r2; r3; _]%wu := unpack [4; 4; 4; 11] rest in
                  Some (Binop t op r1 r2 r3)
    | LOAD => let: [r1; r2; _]%wu := unpack [4; 4; 16] rest in
              Some (Load t r1 r2)
    | STORE => let: [r1; r2; _]%wu := unpack [4; 4; 16] rest in
               Some (Store t r1 r2)
    | JUMP => let : [r; _]%wu := unpack [4; 21] rest in
              Some (Jump t r)
    | BNZ => let: [r; i; _]%wu := unpack [4; 14; 6] rest in
             Some (Bnz t r i)
    | JAL => let: [r; _]%wu := unpack [4; 21] rest in
             Some (Jal t r)
    | JUMPEPC => Some (JumpEpc t)
    | ADDRULE => Some (AddRule t)
    | GETTAG => let: [r1; r2; _]%wu := unpack [4; 4; 16] rest in
                Some (GetTag t r1 r2)
    | PUTTAG => let: [r1; r2; r3; _]%wu := unpack [4; 4; 4; 11] rest in
                Some (PutTag t r1 r2 r3)
    | HALT => Some (Halt t)
    | SERVICE => None (* Not a real instruction *)
    end;

  Z_to_imm := repr;

  imm_to_word i := repr (unsigned i);

  min_word := repr (min_signed 31);
  (* ASZ: If this is `max_unsigned`, then `word_to_Z` needs to be `unsigned`,
     but then `opp_word` breaks. *)
  max_word := repr (max_signed 31);

  Z_to_word := repr;

  word_to_Z := signed;

  add_word := add;

  mul_word := mul;

  and_word := and;

  or_word := or;

  xor_word := xor;

  shru_word := shru;

  shl_word := shl;

  opp_word := neg;

  ord_word := int_ordered;

  ra := repr 0;

  word_map_class := {|
    PartMaps.get V mem i := Int32PMap.get i mem;
    PartMaps.set V mem i x := Int32PMap.set i x mem;
    PartMaps.filter V mem p := Int32PMap.filter mem p;
    PartMaps.map V1 V2 f mem := Int32PMap.map1 f mem;
    PartMaps.empty V := @Int32PMap.empty _
  |};

  reg_map_class := {|
    PartMaps.get V regs i := RegtPMap.get i regs;
    PartMaps.set V regs i x := RegtPMap.set i x regs;
    PartMaps.filter V regs p := RegtPMap.filter regs p;
    PartMaps.map V1 V2 f regs := RegtPMap.map1 f regs;
    PartMaps.empty V := @RegtPMap.empty _
  |};

  reg_tmap_class := {|
    TotalMaps.get V regs r := RegtTMap.get r regs;
    (* BCP/MD: Why isn't this called 'set'? *)
    TotalMaps.upd V regs r x := RegtTMap.set r x regs
  |}


|}.

Lemma compare_signed : forall x y : int32, (x <=> y) = (signed x ?= signed y)%Z.
Proof.
  simpl; intros. unfold Int32Ordered.int_compare,lt.
  destruct (@SetoidDec.equiv_dec Int32Indexed.t _ _ x y) as [EQ | NE]; [ssubst; auto using Zcompare_refl|].
  destruct (zlt (@signed Wordsize_32.wordsize_minus_one x) (@signed Wordsize_32.wordsize_minus_one y)) as [LT | GE]; [auto with zarith|].
  unfold Zge in GE; destruct (_ ?= _)%Z eqn:CMP.
  + apply Z.compare_eq in CMP.
    destruct x as [x px], y as [y py].
    unfold signed,unsigned in CMP; simpl in CMP.
    destruct (zlt x (half_modulus _)),(zlt y (half_modulus _)); ssubst;
    solve [omega
          | contradict NE; apply mkint_eq; solve [reflexivity | omega]].
  + congruence.
  + reflexivity.
Qed.

Open Scope Z_scope.

Instance concrete_int_32_ops_spec : machine_ops_spec concrete_int_32_ops.
Proof.
  constructor.
  - Opaque pack.
    Opaque unpack.
    Opaque unpack2.
    unfold encode_instr,decode_instr,concrete_int_32_ops.
      intros; destruct i; simpl;
      rewrite packU /= pack2K encode_opcodeK /= ?packK //.
    Transparent pack.
    Transparent unpack.
    Transparent unpack2.
  - admit.
  - vm_compute; inversion 1.
  - reflexivity.
  - simpl. apply repr_signed.
  - simpl; intros. apply signed_repr. compute -[Zle] in *; omega.
  - exact: add_repr.
  - exact: neg_repr.
  - exact compare_signed.
  - intros w.
    assert (min_signed 31 <= word_to_Z w) by apply signed_range.
    unfold min_word,word_to_Z,concrete_int_32_ops,le,Wordsize_32.wordsize_minus_one in *.
    rewrite compare_signed signed_repr; last by
      (unfold Wordsize_32.wordsize_minus_one; generalize (signed_range 31 (repr 0)); omega).
    assumption.
  - intros w.
    assert (word_to_Z w <= max_signed 31) by apply signed_range.
    unfold max_word,word_to_Z,concrete_int_32_ops,le in *.
    rewrite compare_signed signed_repr; last by
      (unfold Wordsize_32.wordsize_minus_one; generalize (signed_range 31 (repr 0)); omega).
    assumption.
  - constructor.
    + (* get_set_eq *)
      intros V mem i x. by apply Int32PMap.gss.
    + (* get_set_neq *)
      intros V mem i i' x y. by apply Int32PMap.gso.
    + (* filter_correctness *)
      intros V f m k. by apply Int32PMap.gfilter.
    + (* map_correctness *)
      intros V1 V2 f m k. by apply Int32PMap.gmap1.
    + (* empty_is_empty *)
      intros V k. by apply Int32PMap.gempty.
  - constructor.
    + (* get_set_eq *)
      intros V mem i x. by apply RegtPMap.gss.
    + (* get_set_neq *)
      intros V mem i i' x y. by apply RegtPMap.gso.
    + (* filter_correctness *)
      intros V f m k. by apply RegtPMap.gfilter.
    + (* map_correctness *)
      intros V1 V2 f m k. by apply RegtPMap.gmap1.
    + (* empty_is_empty *)
      intros V k. by apply RegtPMap.gempty.
  - constructor.
    +(* get_upd_eq *)
      intros V mem i x. simpl in *.
      apply RegtTMap.gss.
    + intros V mem i i' x Hneq. simpl in *.
      apply RegtTMap.gso; assumption.
Defined.

Import Concrete.

Let atom := atom (word concrete_int_32_t) (word (concrete_int_32_t)).

Open Scope string_scope.
Import printing.

Instance p : printing concrete_int_32_t := {|
  format_word := fun i => format_Z (unsigned i);
  format_reg := fun i => format_Z (unsigned i);
  format_imm := fun i => format_Z (unsigned i)
|}.

Definition format_instr := printing.format_instr.

Open Scope Z_scope.

Require Import String.

(* BCP: all this needs some fixing to live here...

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
  let os := match (Z_to_op (word_to_Z (@Concrete.cop (word concrete_int_32_t) l))) with
              Some o => format_opcode o
            | None => ss "<BAD OPCODE>"
            end in
   os
   +++ sspace +++
   format_word (@Concrete.ctpc (word concrete_int_32_t) l)
   +++ sspace +++
   format_word (@Concrete.cti (word concrete_int_32_t) l)
   +++ sspace +++
   format_word (@Concrete.ct1 (word concrete_int_32_t) l)
   +++ sspace +++
   format_word (@Concrete.ct2 (word concrete_int_32_t) l)
   +++ sspace +++
   format_word (@Concrete.ct3 (word concrete_int_32_t) l).

Definition format_rvec l :=
   format_word (@Concrete.ctrpc (word concrete_int_32_t) l)
   +++ sspace +++
   format_word (@Concrete.ctr (word concrete_int_32_t) l).

Definition format_whole_cache (c : Concrete.rules (word concrete_int_32_t)) :=
  map (fun l => let: (m,r) := l in (format_mvec m +++ ss " => " +++ format_rvec r)) c.

Definition format_cache (c : Concrete.rules (word concrete_int_32_t)) :=
  format_whole_cache (take 3 c).

Require Import Coqlib.

Fixpoint enum (M R S : Type) (map : M) (get : M -> Int32.int -> R) (f : R -> S) (n : nat) (i : Int32.int) :=
  match n with
  | O => []
  | S p => (Int32.intval i, f (get map i)) :: enum map get f p (Int32.add i (Int32.repr 1))
  end.

Definition summarize_concrete_state mem_count cache_count st :=
  let mem' := just_somes
               (@enum _ _ _
                 (@Concrete.mem concrete_int_32_t cp st)
                 (@PartMaps.get _ Int32.int _ _)
                 (@omap atom sstring format_atom)
                 mem_count
                 (Int32.repr 0)) in
  let mem := ssconcat sspace (map (fun x => let: (addr,con) := x in format_Z addr +++ ss ":" +++ con) mem') in
  let regs' := @enum _ _ _
                 (@Concrete.regs concrete_int_32_t cp st)
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
      None => ss "(UNDEF ADDR)"
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
*)
