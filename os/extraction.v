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

Extract Inductive set_type => "Data.Set.Set" [""]
                              "error ['S','e','t','s',' ','a','r','e',' ','a','b','s','t','r','a','c','t','!']".

(*
Extract Inductive int => "Prelude.Integer"
                         ["Prelude.id" "(Prelude.negate Prelude.. (Prelude.+1))"]
                         "(\fP fN n -> if n Prelude.>= 0 then fP n else fN (Prelude.abs n Prelude.- 1))".
Extract Constant GRing.add   => "Prelude.const (Prelude.+)".
Extract Constant GRing.opp   => "Prelude.const Prelude.negate".
Extract Constant GRing.mul   => "Prelude.const (Prelude.* )".
Extract Constant intdiv.divz => "Prelude.div". (* XXX: Different behavior on negative numbers *)
Extract Constant intdiv.modz => "Prelude.mod". (* XXX: Different behavior on negative numbers *)
Extract Constant absz        => "Prelude.abs".

Extract Inductive word.word => "Prelude.Integer" [""] "(Prelude.$)".
Extract Constant as_word => "\k n -> n Data.Bits..&. ((1 `Data.Bits.shiftL` Prelude.fromInteger k) Prelude.- 1)".*)

Recursive Extraction Library os.
