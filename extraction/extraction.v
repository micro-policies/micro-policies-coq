Require Import Ssreflect.ssreflect.
Require Import Ssreflect.eqtype Ssreflect.fintype.
Require Import Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.seq.
Require Import MathComp.ssrint MathComp.ssrnum MathComp.ssralg MathComp.finset.
Require Import CoqUtils.ord CoqUtils.hseq CoqUtils.word CoqUtils.partmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Require Import lib.utils lib.partmap_utils.
Require Import common.types common.segment.
Require Import concrete.concrete concrete.int_32.
Require Import symbolic.symbolic symbolic.int_32 symbolic.exec.
Require Import compartmentalization.common compartmentalization.symbolic.
Require Import compartmentalization.common compartmentalization.symbolic.
Require Import os.os.

Extraction Language Haskell.

Extract Inductive unit => "()" ["()"].

Extract Inductive prod => "(,)" ["(,)"].
Extract Inductive sigT => "(,)" ["(,)"].
Extract Inductive sigT2 => "(,,)" ["(,,)"].
Extract Constant prod_rect    => "Prelude.uncurry".
Extract Constant prod_uncurry => "Prelude.curry".
Extract Constant sigT_rect    => "Prelude.uncurry".
Extract Constant fst          => "Prelude.fst".
Extract Constant snd          => "Prelude.snd".
Extract Constant projT1       => "Prelude.fst".
Extract Constant projT2       => "Prelude.snd".
(* choice *)
Extract Constant choice.tag_of_pair => "Prelude.id".
Extract Constant choice.pair_of_tag => "Prelude.id".

Extract Inductive bool         => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive sumbool      => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive Bool.reflect => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Constant andb             => "(Prelude.&&)".
Extract Constant orb              => "(Prelude.||)".
Extract Constant xorb             => "(Prelude./=)".
Extract Constant negb             => "Prelude.not".
Extract Constant bool_choice      => "Prelude.id".
Extract Constant Bool.bool_dec    => "(Prelude.==)".
Extract Constant Bool.eqb         => "(Prelude.==)".
Extract Constant Bool.iff_reflect => "Prelude.id".
Extract Constant Bool.reflect_dec => "Prelude.flip Prelude.const".
Extract Constant addb             => "(Prelude./=)". (* addb == xor *)
Extract Constant eqb              => "(Prelude.==)".
Extract Constant isSome           => "Data.Maybe.isJust".
Extract Constant is_inl           => "Data.Either.isLeft".
Extract Constant is_left          => "Prelude.id".
Extract Constant is_inleft        => "Data.Maybe.isJust".
Extract Constant compareb         => "(Prelude.$)".

(* Like booleans, but super important! *)
Extract Inductive reflect => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Constant introP   => "Prelude.id".
Extract Constant sumboolP => "Prelude.id".
Extract Constant idP      => "Prelude.id".
Extract Constant idPn     => "Prelude.not".
Extract Constant negP     => "Prelude.not".
Extract Constant negPn    => "Prelude.id".
Extract Constant negPf    => "Prelude.not".
Extract Constant andP     => "(Prelude.&&)".
Extract Constant and3P    => "\b1 b2 b3 -> b1 Prelude.&& b2 Prelude.&& b3".
Extract Constant and4P    => "\b1 b2 b3 b4 -> b1 Prelude.&& b2 Prelude.&& b3 Prelude.&& b4".
Extract Constant and5P    => "\b1 b2 b3 b4 b5 -> b1 Prelude.&& b2 Prelude.&& b3 Prelude.&& b4 Prelude.&& b5".
Extract Constant orP      => "(Prelude.||)".
Extract Constant or3P     => "\b1 b2 b3 -> b1 Prelude.|| b2 Prelude.|| b3".
Extract Constant or4P     => "\b1 b2 b3 b4 -> b1 Prelude.|| b2 Prelude.|| b3 Prelude.|| b4".
Extract Constant nandP    => "\b1 b2 -> Prelude.not (b1 Prelude.&& b2)".
Extract Constant norP     => "\b1 b2 -> Prelude.not (b1 Prelude.|| b2)".
Extract Constant addbP    => "(Prelude./=)".
Extract Constant compareP => "(Prelude.$)".

Extract Inductive alt_spec => "Prelude.Bool" ["Prelude.True" "Prelude.False"].

Extract Inductive option => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].
Extract Inductive sumor  => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].
Extract Constant option_rect    => "Prelude.flip Prelude.maybe".
Extract Constant option_map     => "Prelude.fmap".
Extract Constant Option.apply   => "Prelude.flip Prelude.maybe".
Extract Constant Option.default => "Data.Maybe.fromMaybe".
Extract Constant Option.bind    => "(Prelude.=<<)".
Extract Constant Option.map     => "Prelude.fmap".

Extract Inductive sum => "Prelude.Either" ["Prelude.Left" "Prelude.Right"].
Extract Constant sum_rect => "Prelude.either".

Extract Inductive list => "[]" ["[]" "(:)"].
Extract Constant length  => "Data.List.genericLength".
Extract Constant app     => "(Prelude.++)".
(* seq *)
Extract Constant size    => "Data.List.genericLength".
Extract Constant nilp    => "Prelude.null".
Extract Constant nilP    => "Prelude.null".
Extract Constant nseq    => "Prelude.replicate Prelude.. Prelude.fromInteger".
Extract Constant cat     => "(Prelude.++)".
Extract Constant filter  => "Prelude.filter".
Extract Constant has     => "Prelude.any".
Extract Constant all     => "Prelude.all".
Extract Constant drop    => "Prelude.drop Prelude.. Prelude.fromInteger".
Extract Constant take    => "Prelude.take Prelude.. Prelude.fromInteger".
Extract Constant rev     => "Prelude.reverse".
Extract Constant map     => "Prelude.map".
Extract Constant pmap    => "Data.Maybe.mapMaybe".
Extract Constant iota    => "\f t -> [f .. f Prelude.+ t Prelude.- 1]".
Extract Constant foldr   => "Prelude.foldr".
Extract Constant sumn    => "Prelude.sum".
Extract Constant foldl   => "Data.List.foldl'".
Extract Constant scanl   => "Prelude.scanl".
Extract Constant zip     => "Prelude.zip".
Extract Constant flatten => "Prelude.concat".
(* choice *)
Extract Constant choice.seq_of_opt => "Prelude.maybe [] Prelude.return".

Extract Inductive comparison  => "Prelude.Ordering" ["Prelude.EQ" "Prelude.LT" "Prelude.GT"].
Extract Inductive CompareSpec => "Prelude.Ordering" ["Prelude.EQ" "Prelude.LT" "Prelude.GT"].
  (* Like `comparison`, but with proofs -- except those have been erased *)

Extract Inductive nat => "Prelude.Integer" ["(0 :: Prelude.Integer)" "(Prelude.+ 1)"]
                         "(\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))".
Extract Constant Peano.pred      => "\x -> Prelude.max (x Prelude.- 1) 0".
Extract Constant Peano.plus      => "(Prelude.+)".
Extract Constant Peano.minus     => "\x y -> Prelude.max (x Prelude.- y) 0".
Extract Constant Peano.mult      => "(Prelude.*)".
Extract Constant Peano.max       => "Prelude.max".
Extract Constant Peano.min       => "Prelude.min".
(* ssrnat *)
Extract Constant eqn             => "(Prelude.==)".
Extract Constant addn_rec        => "(Prelude.+)".
Extract Constant addn            => "(Prelude.+)".
Extract Constant subn_rec        => "\x y -> Prelude.max (x Prelude.- y) 0".
Extract Constant subn            => "\x y -> Prelude.max (x Prelude.- y) 0".
Extract Constant leq             => "(Prelude.<=)".
Extract Constant maxn            => "Prelude.max".
Extract Constant minn            => "Prelude.min".
Extract Constant muln_rec        => "(Prelude.*)".
Extract Constant muln            => "(Prelude.*)".
Extract Constant expn_rec        => "(Prelude.^)".
Extract Constant expn            => "(Prelude.^)".
Extract Constant fact_rec        => "Prelude.product Prelude.. Prelude.enumFromTo 1".
Extract Constant factorial       => "Prelude.product Prelude.. Prelude.enumFromTo 1".
Extract Constant nat_of_bool     => "\b -> (if b then 1 else 0 :: Prelude.Integer)".
Extract Constant odd             => "Prelude.odd".
Extract Constant double_rec      => "(2 Prelude.*)".
Extract Constant double          => "(2 Prelude.*)".
Extract Constant half            => "(`Prelude.quot` 2)".
Extract Constant uphalf          => "\x -> (x Prelude.+ 1) `Prelude.quot` 2".
Extract Constant NatTrec.add     => "(Prelude.+)".
Extract Constant NatTrec.add_mul => "\x y acc -> (x Prelude.* y) Prelude.+ acc".
Extract Constant NatTrec.mul     => "(Prelude.*)".
Extract Constant NatTrec.mul_exp => "\x y acc -> (x Prelude.^ y) Prelude.* acc".
Extract Constant NatTrec.exp     => "(Prelude.^)".
Extract Constant NatTrec.odd     => "Prelude.odd".
Extract Constant NatTrec.double  => "(2 Prelude.*)".
Extract Constant nat_of_pos      => "Prelude.id".
Extract Constant nat_of_bin      => "Prelude.id".
Extract Constant bin_of_nat      => "Prelude.id".
(* ssr div *)
Extract Constant div.edivn    => "\x y -> if y Prelude.== 0 then (0,x) else x `Prelude.quotRem` y".
Extract Constant div.divn     => "\x y -> if y Prelude.== 0 then 0     else x `Prelude.quot`    y".
Extract Constant div.modn     => "\x y -> if y Prelude.== 0 then x     else x `Prelude.rem`     y".
Extract Constant div.gcdn_rec => "Prelude.gcd".
Extract Constant div.gcdn     => "Prelude.gcd".
Extract Constant div.lcmn     => "Prelude.lcm".

Extract Inductive BinNums.positive =>
  "Prelude.Integer"
  ["((Prelude.+ 1) Prelude.. (2 Prelude.*))"
   "(2 Prelude.*)"
   "(1 :: Prelude.Integer)"]
  "(\fxI fxO fxH p -> if p Prelude.== 1 then fxH p else (if Data.Bits.testBit p 0 then fxI else fxO) (p `Data.Bits.shiftR` 1))".
Extract Inductive BinNums.N =>
  "Prelude.Integer" ["(0 :: Prelude.Integer)" "Prelude.id"]
  "(\fN0 fNpos n -> if n Prelude.== 0 then fN0 () else fNpos n)".
Extract Inductive BinNums.Z =>
  "Prelude.Integer" ["(0 :: Prelude.Integer)" "Prelude.id" "Prelude.negate"]
  "(\fZ0 fZpos fZneg z -> case z `Prelude.compare` 0 of { Prelude.GT -> fZpos z ; Prelude.EQ -> fZ0 () ; Prelude.LT -> fZneg (- z) })".

Extract Constant BinPos.Pos.succ         => "(Prelude.+ 1)".
Extract Constant BinPos.Pos.add          => "(Prelude.+)".
Extract Constant BinPos.Pos.add_carry    => "\x y -> x Prelude.+ y Prelude.+ 1".
Extract Constant BinPos.Pos.pred_double  => "\x -> (2 Prelude.* x) Prelude.- 1".
Extract Constant BinPos.Pos.pred         => "\x -> Prelude.max (x Prelude.- 1) 1".
Extract Constant BinPos.Pos.pred_N       => "Prelude.subtract 1".
Extract Constant BinPos.Pos.sub          => "\x y -> Prelude.max (x Prelude.- y) 1".
Extract Constant BinPos.Pos.mul          => "(Prelude.*)".
Extract Constant BinPos.Pos.pow          => "(Prelude.^)".
Extract Constant BinPos.Pos.square       => "(Prelude.^ 2)".
Extract Constant BinPos.Pos.div2         => "\x -> Prelude.max (x `Prelude.quot` 2) 1".
Extract Constant BinPos.Pos.div2_up      => "\x -> (x Prelude.+ 1) `Prelude.quot` 2".
Extract Constant BinPos.Pos.compare      => "Prelude.compare".
Extract Constant BinPos.Pos.min          => "Prelude.min".
Extract Constant BinPos.Pos.max          => "Prelude.max".
Extract Constant BinPos.Pos.eqb          => "(Prelude.==)".
Extract Constant BinPos.Pos.leb          => "(Prelude.<=)".
Extract Constant BinPos.Pos.ltb          => "(Prelude.<)".
Extract Constant BinPos.Pos.gcd          => "Prelude.gcd".
Extract Constant BinPos.Pos.Nsucc_double => "\x -> 2 Prelude.* x Prelude.+ 1".
Extract Constant BinPos.Pos.Ndouble      => "(2 Prelude.*)".
Extract Constant BinPos.Pos.lor          => "(Data.Bits..|.)".
Extract Constant BinPos.Pos.land         => "(Data.Bits..&.)".
Extract Constant BinPos.Pos.ldiff        => "\x y -> x Data.Bits..&. Data.Bits.complement y".
Extract Constant BinPos.Pos.lxor         => "Data.Bits.xor".
Extract Constant BinPos.Pos.shiftl_nat   => "\x s -> x `Data.Bits.shiftL` (Prelude.fromInteger s)".
Extract Constant BinPos.Pos.shiftr_nat   => "\x s -> Prelude.max (x `Data.Bits.shiftR` (Prelude.fromInteger s)) 1".
Extract Constant BinPos.Pos.shiftl       => "\x s -> x `Data.Bits.shiftL` (Prelude.fromInteger s)".
Extract Constant BinPos.Pos.shiftr       => "\x s -> Prelude.max (x `Data.Bits.shiftR` (Prelude.fromInteger s)) 1".
Extract Constant BinPos.Pos.testbit_nat  => "\x b -> Data.Bits.testBit x (Prelude.fromInteger b)".
Extract Constant BinPos.Pos.testbit      => "\x b -> Data.Bits.testBit x (Prelude.fromInteger b)".
Extract Constant BinPos.Pos.to_nat       => "Prelude.id".
Extract Constant BinPos.Pos.of_nat       => "Prelude.max 1".
Extract Constant BinPos.Pos.of_succ_nat  => "(Prelude.+ 1)".
Extract Constant BinPos.Pos.eq_dec       => "(Prelude.==)".

Extract Constant BinNat.N.zero         => "0 :: Prelude.Integer".
Extract Constant BinNat.N.one          => "1 :: Prelude.Integer".
Extract Constant BinNat.N.two          => "2 :: Prelude.Integer".
Extract Constant BinNat.N.succ_double  => "\x -> 2 Prelude.* x Prelude.+ 1".
Extract Constant BinNat.N.double       => "(2 Prelude.*)".
Extract Constant BinNat.N.succ         => "(Prelude.+ 1)".
Extract Constant BinNat.N.pred         => "\x -> Prelude.max (x Prelude.- 1) 0".
Extract Constant BinNat.N.succ_pos     => "(Prelude.+ 1)".
Extract Constant BinNat.N.add          => "(Prelude.+)".
Extract Constant BinNat.N.sub          => "\x y -> Prelude.max (x Prelude.- y) 0".
Extract Constant BinNat.N.mul          => "(Prelude.*)".
Extract Constant BinNat.N.compare      => "Prelude.compare".
Extract Constant BinNat.N.eqb          => "(Prelude.==)".
Extract Constant BinNat.N.leb          => "(Prelude.<=)".
Extract Constant BinNat.N.ltb          => "(Prelude.<)".
Extract Constant BinNat.N.min          => "Prelude.min".
Extract Constant BinNat.N.max          => "Prelude.max".
Extract Constant BinNat.N.div2         => "(`Prelude.quot` 2)".
Extract Constant BinNat.N.even         => "Prelude.even".
Extract Constant BinNat.N.odd          => "Prelude.odd".
Extract Constant BinNat.N.pow          => "(Prelude.^)".
Extract Constant BinNat.N.square       => "(Prelude.^ 2)".
Extract Constant BinNat.N.pos_div_eucl => "\x y -> if y Prelude.== 0 then (0,x) else x `Prelude.quotRem` y".
Extract Constant BinNat.N.div_eucl     => "\x y -> if y Prelude.== 0 then (0,x) else x `Prelude.quotRem` y".
Extract Constant BinNat.N.div          => "Prelude.quot".
Extract Constant BinNat.N.modulo       => "Prelude.rem".
Extract Constant BinNat.N.gcd          => "Prelude.gcd".
Extract Constant BinNat.N.lor          => "(Data.Bits..|.)".
Extract Constant BinNat.N.land         => "(Data.Bits..&.)".
Extract Constant BinNat.N.ldiff        => "\x y -> x Data.Bits..&. Data.Bits.complement y".
Extract Constant BinNat.N.lxor         => "Data.Bits.xor".
Extract Constant BinNat.N.shiftl_nat   => "\x s -> x `Data.Bits.shiftL` (Prelude.fromInteger s)".
Extract Constant BinNat.N.shiftr_nat   => "\x s -> x `Data.Bits.shiftR` (Prelude.fromInteger s)".
Extract Constant BinNat.N.shiftl       => "\x s -> x `Data.Bits.shiftL` (Prelude.fromInteger s)".
Extract Constant BinNat.N.shiftr       => "\x s -> x `Data.Bits.shiftR` (Prelude.fromInteger s)".
Extract Constant BinNat.N.testbit_nat  => "\x b -> Data.Bits.testBit x (Prelude.fromInteger b)".
Extract Constant BinNat.N.testbit      => "\x b -> Data.Bits.testBit x (Prelude.fromInteger b)".
Extract Constant BinNat.N.to_nat       => "Prelude.id".
Extract Constant BinNat.N.of_nat       => "Prelude.id".
Extract Constant BinNat.N.eq_dec       => "(Prelude.==)".
Extract Constant BinNat.N.lcm          => "Prelude.lcm".
Extract Constant BinNat.N.setbit       => "\x b -> Data.Bits.setBit x (Prelude.fromInteger b)".
Extract Constant BinNat.N.clearbit     => "\x b -> Data.Bits.clearBit x (Prelude.fromInteger b)".

Extract Inductive int => "Prelude.Integer"
                         ["Prelude.id" "(Prelude.negate Prelude.. (Prelude.+1))"]
                         "(\fP fN n -> if n Prelude.>= 0 then fP n else fN (Prelude.abs n Prelude.- 1))".
Extract Constant intZmod.addz   => "(Prelude.+)".
Extract Constant intZmod.oppz   => "Prelude.negate".
Extract Constant intRing.mulz   => "(Prelude.*)".
Extract Constant absz           => "Prelude.abs".
Extract Constant intOrdered.lez => "(Prelude.<=)".
Extract Constant intOrdered.ltz => "(Prelude.<)".
(* intmul? (no)  exprz? (maybe)  sgz? (probably not) *)
(* Extract Constant int_eqMixin    => "Eqtype.coq_CanEqMixin (Prelude.==) (unsafeCoerce natsum_of_int) (unsafeCoerce int_of_natsum)". *)
(* ^ The above doesn't work because `(==)' needs to be an eqtype.  Thus,
   equality will be a bit slower than it should be. *)

Extract Constant intdiv.divz => "\x y -> unsafeCoerce (if y Prelude.== 0 then 0 else x `Prelude.div` y)". (* I cannot BELIEVE I need unsafeCoerce here. *)
Extract Constant intdiv.modz => "\x y -> if y Prelude.== 0 then x else x `Prelude.mod` Prelude.abs y".

Extract Inductive rat.rat => "Prelude.Rational" ["(Prelude.uncurry (Data.Ratio.%))"]
                             "(\f q -> f (Data.Ratio.numerator q, Data.Ratio.denominator q))".
Extract Constant rat.valq   => "\q -> (Data.Ratio.numerator q, Data.Ratio.denominator q)".
Extract Constant rat.ratz   => "Prelude.fromInteger".
Extract Constant rat.numq   => "Data.Ratio.numerator".
Extract Constant rat.denq   => "Data.Ratio.denominator".
Extract Constant rat.fracq  => "Prelude.uncurry (Data.Ratio.%)".
Extract Constant rat.zeroq  => "0".
Extract Constant rat.oneq   => "1".
Extract Constant rat.addq   => "(Prelude.+)".
Extract Constant rat.oppq   => "Prelude.negate".
Extract Constant rat.mulq   => "(Prelude.*)".
Extract Constant rat.invq   => "Prelude.recip".
Extract Constant rat.subq   => "(Prelude.-)".
Extract Constant rat.divq   => "\x y -> if y Prelude.== 0 then 0 else x Prelude./ y".
Extract Constant rat.le_rat => "(Prelude.<=)".
Extract Constant rat.lt_rat => "(Prelude.<)".

(* The `zmodp' stuff for Ordinals should mostly extract efficiently!  I'm not
   sure about `Zp_inv', though, in particular its use of `div.egcdn'. *)

(* Word arithmetic is left alone -- the bitwise hacks don't seem worth it, and
   we can't just extract `word 32' to `Int32', so... yeah.  We do deal with the
   bitwise stuff to avoid finfuns, though.  *)

Extract Constant negw => "\k (Word w) -> as_word k (Data.Bits.complement w)".
Extract Constant andw => "\_ (Word w1) (Word w2) -> Word (w1  Data.Bits..&.  w2)".
Extract Constant orw  => "\_ (Word w1) (Word w2) -> Word (w1  Data.Bits..|.  w2)".
Extract Constant xorw => "\_ (Word w1) (Word w2) -> Word (w1 `Data.Bits.xor` w2)".

Extract Inductive set_type => "Finset.Coq_set_type"
                              ["(finsetAbstract ""FinSet constructor"")"]
                              "(finsetAbstract ""FinSet case"")".
Extract Constant set_type_rect      => "finsetAbstract ""set_type_rect""".
Extract Constant set_type_rec       => "finsetAbstract ""set_type_rec""".
Extract Constant finfun_of_set      => "finsetAbstract ""finfun_of_set""".
Extract Constant SetDef.finset      => "finsetAbstract ""SetDef.finset""".
Extract Constant SetDef.pred_of_set => "finsetAbstract ""SetDef.pred_of_set""".
Extract Constant Imset.imset        => "finsetAbstract ""Imset.imset""".
Extract Constant Imset.imset2       => "finsetAbstract ""Imset.imset2""".
Extract Constant preimset           => "finsetAbstract ""preimset""".
(*
Extract Constant set_subType        => "finsetAbstract ""set_subType""".
Extract Constant set_choiceMixin    => "finsetAbstract ""set_choiceMixin""".
Extract Constant set_choiceType     => "finsetAbstract ""set_choiceType""".
Extract Constant set_countMixin     => "finsetAbstract ""set_countMixin""".
Extract Constant set_countType      => "finsetAbstract ""set_countType""".
Extract Constant set_subCountType   => "finsetAbstract ""set_subCountType""".
Extract Constant set_finMixin       => "finsetAbstract ""set_finMixin""".
Extract Constant set_finType        => "finsetAbstract ""set_finType""".
Extract Constant set_subFinType     => "finsetAbstract ""set_subFinType""".
Extract Constant set_predType       => "finsetAbstract ""set_predType""".
...
*)

Extract Constant set_eqMixin => "withFintypeOrd' (Eqtype.equality__mixin (Prelude.==) (finsetAbstract ""set_eqMixin/eqP""))".

Extract Constant set0     => "\_ -> Data.Set.empty".
Extract Constant setTfor  => "finsetFinite ""setTfor""".
Extract Constant set1     => "\_ x -> Data.Set.singleton (unitAny x)".
Extract Constant setU     => "withFintypeOrd' Data.Set.union".
Extract Constant setI     => "withFintypeOrd' Data.Set.intersection".
Extract Constant setC     => "finsetFinite ""setC""".
Extract Constant setD     => "withFintypeOrd' Data.Set.difference".
Extract Constant ssetI    => "withFintypeOrd' (\xss ys -> flattenedSet (Data.Set.filter (`Data.Set.isSubsetOf` ys) (nestedSet xss)))".
Extract Constant powerset => "withFintypeOrd' (\s -> flattenedSet (setPowerset s))".
Extract Constant setX     => "\_ _ xs ys ->
  unsafeCoerce (Data.Set.fromDistinctAscList [ (x,y) | x <- Data.Set.toAscList xs
                                                     , y <- Data.Set.toAscList ys ])".
  (* Due to Dan Weston's mailing list post at
     https://mail.haskell.org/pipermail/haskell-cafe/2007-August/029859.html;
     the proof obligation for `fromDistinctAscList' is fulfilled by
     construction *)

(* Not confident about the `unsafeCoerce' in this one *)
Extract Constant set_0Vmem => "\_ s -> if Data.Set.null s then Prelude.Left () else Prelude.Right (unsafeCoerce (Data.Set.findMin s))".

(* Not sure about cover, pblock, trivIset, partition, is_transversal, transversal *)
(* Also not sure about minset and maxset *)

(* Cardinality *will* break, too *)

(* eqtypes get included comparator functions -- the definition of the type is
   stored in extra/eqtype.hs *)
Extract Inductive Equality.mixin_of => "Eqtype.Equality__Coq_mixin_of" ["Eqtype.equality__mixin"]
                                       "(\f em -> case em of Eqtype.Equality__Mixin eqb eqP _ -> f eqb eqP)".
Extract Constant sub_eqMixin => "\t p sT ->
  Equality__Mixin
    (\x y -> eq_op t (val p sT x) (val p sT y))
    (val_eqP t p sT)
    (\x y -> compare_op t (val p sT x) (val p sT y))".
Extract Constant SubEqMixin => "\t p sT ->
  let {vP = val_eqP t p sT} in
  case sT of {
   SubType v sub p0 ->
     Equality__Mixin
       (\x y -> eq_op t (v x) (v y))
       vP
       (\x y -> compare_op t (v x) (v y))
  }".
Extract Constant sig_eqMixin => "\t p ->
  Equality__Mixin
    (\x y -> eq_op t (Specif.proj1_sig x) (Specif.proj1_sig y))
    (unsafeCoerce (val_eqP t (\x -> p x) (sig_subType p)))
    (\x y -> compare_op t (Specif.proj1_sig x) (Specif.proj1_sig y))".
Extract Constant prod_eqMixin => "\t1 t2 ->
  Equality__Mixin
    (Ssrbool.rel_of_simpl_rel (pair_eq t1 t2))
    (pair_eqP t1 t2)
    (\(x1,x2) (y1,y2) -> compare_op t1 x1 y1 Data.Monoid.<> compare_op t2 x2 y2)".
Extract Constant option_eqMixin => "\t ->
  Equality__Mixin (opt_eq t) (opt_eqP t)
    (\mx my -> case (mx,my) of {
                 (Prelude.Nothing, Prelude.Nothing) -> Prelude.EQ;
                 (Prelude.Nothing, Prelude.Just _)  -> Prelude.LT;
                 (Prelude.Just _,  Prelude.Nothing) -> Prelude.GT;
                 (Prelude.Just x,  Prelude.Just y)  -> compare_op t x y})".
Extract Constant tag_eqMixin => "\i t_ ->
  Equality__Mixin (tag_eq i t_) (tag_eqP i t_)
                  (\x1 x2 -> compare_op i             (tag x1)    (tag x2) Data.Monoid.<>
                             compare_op (t_ (tag x1)) (tagged x1) (tagged_as i x1 x2))".
Extract Constant sum_eqMixin => "\t1 t2 ->
  Equality__Mixin (sum_eq t1 t2) (sum_eqP t1 t2)
    (\x12 y12 -> case (x12, y12) of {
                   (Prelude.Left  x1, Prelude.Left  y1) -> compare_op t1 x1 y1;
                   (Prelude.Right x2, Prelude.Right y2) -> compare_op t2 x2 y2;
                   (Prelude.Left  _,  Prelude.Right _)  -> Prelude.LT;
                   (Prelude.Right _,  Prelude.Left  _)  -> Prelude.GT })".

(* The type `finfun_type` is horribly inefficient, but I don't believe we ever
   use it, as long as we extract sets properly. *)
Extract Constant finfun.finfun_eqMixin => "\aT rT ->
  Eqtype.Equality__Mixin (\x y ->
    Eqtype.eq_op
      (Tuple.tuple_eqType
        (Fintype._CardDef__card aT
          (Ssrbool.mem Ssrbool.predPredType
            (Ssrbool.sort_of_simpl_pred Ssrbool.pred_of_argType))) rT)
      (unsafeCoerce (fgraph aT x)) (unsafeCoerce (fgraph aT y)))
    (unsafeCoerce
      (Eqtype.val_eqP
        (Tuple.tuple_eqType
          (Fintype._CardDef__card aT
            (Ssrbool.mem Ssrbool.predPredType
              (Ssrbool.sort_of_simpl_pred Ssrbool.pred_of_argType))) rT)
        (\x -> Prelude.True) (unsafeCoerce (finfun_subType aT))))
    (\x y ->
      Eqtype.compare_op
        (Tuple.tuple_eqType
          (Fintype._CardDef__card aT
            (Ssrbool.mem Ssrbool.predPredType
              (Ssrbool.sort_of_simpl_pred Ssrbool.pred_of_argType))) rT)
        (unsafeCoerce (fgraph aT x)) (unsafeCoerce (fgraph aT y)))".

Extract Constant fingroup.group_eqMixin => "\gT ->
  Eqtype.Equality__Mixin (\x y ->
    Eqtype.eq_op (group_set_eqType (_FinGroup__base gT))
      (unsafeCoerce (gval gT x)) (unsafeCoerce (gval gT y)))
    (unsafeCoerce
      (Eqtype.val_eqP (group_set_eqType (_FinGroup__base gT))
        (unsafeCoerce (group_set gT)) (unsafeCoerce (group_subType gT))))
    (\x y ->
      Eqtype.compare_op (group_set_eqType (_FinGroup__base gT))
        (unsafeCoerce (gval gT x)) (unsafeCoerce (gval gT y)))".

Extract Constant fingroup.subg_eqMixin => "\gT g ->
  Eqtype.Equality__Mixin (\x y ->
    Eqtype.eq_op (_FinGroup__arg_eqType (_FinGroup__base gT)) (sgval gT g x)
      (sgval gT g y))
    (unsafeCoerce
      (Eqtype.val_eqP (_FinGroup__arg_eqType (_FinGroup__base gT)) (\x ->
        Ssrbool.in_mem x
          (Ssrbool.mem Ssrbool.predPredType
            (Finset._SetDef__pred_of_set
              (_FinGroup__arg_finType (_FinGroup__base gT)) (gval gT g))))
        (subg_subType gT g)))
    (\x y ->
      Eqtype.compare_op (_FinGroup__arg_eqType (_FinGroup__base gT)) (sgval gT g x)
        (sgval gT g y))".

Extract Constant choice.tree_eqMixin => "\t ->
  let { (<=>) :: GenTree__Coq_tree Eqtype.Equality__Coq_sort
              -> GenTree__Coq_tree Eqtype.Equality__Coq_sort
              -> Prelude.Ordering
      ; GenTree__Leaf x    <=> GenTree__Leaf y    = Eqtype.compare_op t x y
      ; GenTree__Leaf _    <=> GenTree__Node _ _  = Prelude.LT
      ; GenTree__Node _ _  <=> GenTree__Leaf _    = Prelude.GT
      ; GenTree__Node m xs <=> GenTree__Node n ys =
          (m `Prelude.compare` n) Data.Monoid.<>
          (Eqtype.compare_op
            (unsafeCoerce (Seq.seq_eqMixin (unsafeCoerce (tree_eqMixin t))))
            (unsafeCoerce xs)
            (unsafeCoerce ys)) }
  in Data.Reflection.Constraint.providing (Data.Reflection.Constraint.Ord (<=>))
       (Eqtype.coq_PcanEqMixin
          (Seq.seq_eqType (Eqtype.sum_eqType Ssrnat.nat_eqType t))
          (unsafeCoerce _GenTree__encode) (unsafeCoerce _GenTree__decode))".

Extract Constant fintype.seq_sub_eqMixin => "\t s ->
  Eqtype.Equality__Mixin (\x y ->
    Eqtype.eq_op (Choice._Choice__eqType t) (ssval t s x) (ssval t s y))
    (unsafeCoerce
      (Eqtype.val_eqP (Choice._Choice__eqType t) (\x ->
        Ssrbool.in_mem x
          (Ssrbool.mem (Seq.seq_predType (Choice._Choice__eqType t))
            (unsafeCoerce s))) (seq_sub_subType t s)))
    (\x y -> Eqtype.compare_op (Choice._Choice__eqType t) (ssval t s x) (ssval t s y))".

Extract Constant hseq.hseq_eqMixin => "\t_ idx ->
  Eqtype.Equality__Mixin (hseq_eq t_ idx) (hseq_eqP t_ idx) (hseq_compare t_ idx)".
Extract Constant hseq.HSeqChoiceType.hseq_choiceMixin =>
  "Prelude.error ""_HSeqChoiceType__hseq_choiceMixin: failed to compile with infinite type errors""".

Extract Constant poly.polynomial_eqMixin => "\r ->
  Eqtype.Equality__Mixin (\x y ->
    Eqtype.eq_op (Seq.seq_eqType (Ssralg._GRing__Ring__eqType r))
      (unsafeCoerce (polyseq r x)) (unsafeCoerce (polyseq r y)))
    (unsafeCoerce
      (Eqtype.val_eqP (Seq.seq_eqType (Ssralg._GRing__Ring__eqType r)) (\x ->
        Datatypes.negb
          (Eqtype.eq_op (Ssralg._GRing__Ring__eqType r)
            (Seq.last (Ssralg._GRing__one r) (unsafeCoerce x))
            (Ssralg._GRing__zero (Ssralg._GRing__Ring__zmodType r))))
        (unsafeCoerce (polynomial_subType r))))
    (\x y ->
      Eqtype.compare_op (Seq.seq_eqType (Ssralg._GRing__Ring__eqType r))
        (unsafeCoerce (polyseq r x)) (unsafeCoerce (polyseq r y)))".

Extract Constant quotient.coset_eqMixin => "\gT a ->
  Eqtype.Equality__Mixin (\x y ->
    Eqtype.eq_op (Fingroup.group_set_eqType (Fingroup._FinGroup__base gT))
      (unsafeCoerce (set_of_coset gT a x))
      (unsafeCoerce (set_of_coset gT a y)))
    (unsafeCoerce
      (Eqtype.val_eqP
        (Fingroup.group_set_eqType (Fingroup._FinGroup__base gT))
        (Ssrbool.pred_of_simpl (coset_range gT a))
        (unsafeCoerce (coset_subType gT a))))
    (\x y ->
      Eqtype.compare_op (Fingroup.group_set_eqType (Fingroup._FinGroup__base gT))
        (unsafeCoerce (set_of_coset gT a x))
        (unsafeCoerce (set_of_coset gT a y)))".

Extract Constant seq_eqMixin => "\t ->
  let {[]     <=> []     = Prelude.EQ;
       []     <=> (_:_)  = Prelude.LT;
       (_:_)  <=> []     = Prelude.GT;
       (x:xs) <=> (y:ys) = Eqtype.compare_op t x y Data.Monoid.<> xs <=> ys}
  in Eqtype.Equality__Mixin (eqseq t) (eqseqP t) (<=>)".

Extract Constant tuple.tuple_eqMixin => "\n t ->
  Eqtype.Equality__Mixin (\x y ->
    Eqtype.eq_op (Seq.seq_eqType t) (unsafeCoerce (tval n x))
      (unsafeCoerce (tval n y)))
    (unsafeCoerce
      (Eqtype.val_eqP (Seq.seq_eqType t) (\x ->
        Eqtype.eq_op Ssrnat.nat_eqType
          (unsafeCoerce (Seq.size (unsafeCoerce x))) (unsafeCoerce n))
        (unsafeCoerce (tuple_subType n))))
    (\x y ->
      Eqtype.compare_op
        (Seq.seq_eqType t)
        (unsafeCoerce (tval n x))
        (unsafeCoerce (tval n y)))".

Extract Constant atom_eqMixin => "\vEM tEM ->
  Eqtype.Equality__Mixin
    (atom_eqb  vEM tEM)
    (atom_eqbP vEM tEM)
    (\(Atom v1 t1) (Atom v2 t2) ->
        Eqtype.compare_op vEM v1 v2 Data.Monoid.<> Eqtype.compare_op tEM t1 t2)".

Extract Constant symbolic.Exports.state_eqMixin => "\mt p ->
  Eqtype.Equality__Mixin
    (_Exports__state_eqb  mt p)
    (_Exports__state_eqbP mt p)
    (_Exports__state_cmp  mt p)".

Extract Constant data_tag_eqMixin => "\mt ->
  Eqtype.Equality__Mixin
    (_Sym__Exports__data_tag_eq  mt)
    (_Sym__Exports__data_tag_eqP mt)
    (_Sym__Exports__data_tag_cmp mt)".

Extract Constant Sym.compartmentalization_internal_eqMixin => "\mt ->
  Eqtype.Equality__Mixin
    (_Sym__compartmentalization_internal_eqb  mt)
    (_Sym__compartmentalization_internal_eqbP mt)
    (_Sym__compartmentalization_internal_cmp  mt)".

Extract Constant concrete.Exports.state_eqMixin => "\mt ->
  Eqtype.Equality__Mixin
    (_Exports__state_eqb  mt)
    (_Exports__state_eqbP mt)
    (_Exports__state_cmp  mt)".

Extract Constant rules.mtag_eqMixin => "\tty ->
  let { (<=>) :: Coq_mtag -> Coq_mtag -> Prelude.Ordering
      ; User  u1 <=> User  u2 = Eqtype.compare_op (Symbolic._Symbolic__mem_tag_type   tty) u1 u2
      ; Entry e1 <=> Entry e2 = Eqtype.compare_op (Symbolic._Symbolic__entry_tag_type tty) e1 e2
      ; User  _  <=> Entry _  = Prelude.LT
      ; Entry _  <=> User  _  = Prelude.GT }
  in Data.Reflection.Constraint.providing (Data.Reflection.Constraint.Ord (<=>))
       (Eqtype.coq_CanEqMixin
         (Eqtype.sum_eqType
           (Symbolic._Symbolic__mem_tag_type tty)
           (Symbolic._Symbolic__entry_tag_type tty))
         (unsafeCoerce (sum_of_mtag tty))
         (unsafeCoerce (mtag_of_sum tty)))".

(* I've ignored most of the pure math stuff in MathComp (beyond what was
   necessary for the `eqType' change) -- we don't use it, and it's quite
   complicated.  This includes polynomials and matrices/linear algebra -- we
   certainly *could* use those things (they aren't super pure), but we don't,
   and there's plenty of extraction work already. *)

(* `concrete/exec.v'                  -> `exec.hs'
   `symbolic/exec.v'                  -> `exec0.hs'
   `concrete/int_32.v'                -> `int_32.hs'
   `symbolic/int_32.v'                -> `int_0.hs'
   `symbolic/symbolic.v'              -> `symbolic.hs'
   `compartmentalization/symbolic.hs' -> `symbolic0.hs' *)
