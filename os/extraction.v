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
Extract Constant isSome           => "Data.Maybe.isJust".
Extract Constant is_inl           => "Data.Either.isLeft".
Extract Constant is_left          => "Prelude.id".
Extract Constant is_inleft        => "Data.Maybe.isJust".

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
Extract Constant length => "Data.List.genericLength".
Extract Constant app    => "(Prelude.++)".

Extract Inductive comparison  => "Prelude.Ordering" ["Prelude.EQ" "Prelude.LT" "Prelude.GT"].
Extract Inductive CompareSpec => "Prelude.Ordering" ["Prelude.EQ" "Prelude.LT" "Prelude.GT"].
  (* Like `comparison`, but with proofs -- except those have been erased *)

Extract Inductive nat => "Prelude.Integer" ["0" "(Prelude.+1)"]
                         "(\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))".
Extract Constant Peano.pred  => "\x -> Prelude.max (x Prelude.- 1) 0".
Extract Constant Peano.plus  => "(Prelude.+)".
Extract Constant addn        => "(Prelude.+)".
Extract Constant Peano.minus => "\x y -> Prelude.max (x Prelude.- y) 0".
Extract Constant subn        => "\x y -> Prelude.max (x Prelude.- y) 0".
Extract Constant Peano.mult  => "(Prelude.*)".
Extract Constant muln        => "(Prelude.*)".
Extract Constant Peano.max   => "Prelude.max".
Extract Constant Peano.min   => "Prelude.min".
Extract Constant div.divn    => "Prelude.quot".
Extract Constant div.modn    => "Prelude.rem".
Extract Constant expn        => "(Prelude.^)".

Extract Inductive int => "Prelude.Integer" ["Prelude.id" "(Prelude.negate . (Prelude.+1))"]
                         "(\fP fN n -> if n Prelude.>= 0 then fP n else fN (Prelude.abs n Prelude.- 1))".
Extract Constant GRing.add   => "Prelude.const (Prelude.+)".
Extract Constant GRing.opp   => "Prelude.const Prelude.negate".
Extract Constant GRing.mul   => "Prelude.const (Prelude.*)".
Extract Constant intdiv.divz => "Prelude.div". (* XXX: Different behavior on negative numbers *)
Extract Constant intdiv.modz => "Prelude.mod". (* XXX: Different behavior on negative numbers *)
Extract Constant absz        => "Prelude.abs".

Extract Inductive word.word => "Prelude.Integer" [""] "(Prelude.$)".
Extract Constant as_word => "\k n -> n Data.Bits..&. ((1 `Data.Bits.shiftL` Prelude.fromInteger k) Prelude.- 1)".

Recursive Extraction Library os.
