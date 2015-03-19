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

Extract Inductive nat => "Integer" ["0" "(+1)"] "(\fO fS n -> if n == 0 then fO () else fS (n-1))".
Extract Constant addn => "(+)".
Extract Constant subn => "(\x y -> max (x - y) 0)".
Extract Constant muln => "(*)".
Extract Constant div.divn => "quot".
Extract Constant div.modn => "rem".
Extract Constant expn     => "(^)".

Extract Inductive int => "Integer" ["id" "(negate . (+1))"]
                                   "(\fP fN n -> if n >= 0 then fP n else fN (abs n - 1))".
Extract Constant GRing.add => "const (+)".
Extract Constant GRing.opp => "const negate".
Extract Constant GRing.mul => "const (*)".
Extract Constant intdiv.divz => "div". (* XXX: Different behavior on negative numbers *)
Extract Constant intdiv.modz => "mod". (* XXX: Different behavior on negative numbers *)
Extract Constant absz => "abs".

Extract Inductive word.word => "Integer" [""] "($)".
Extract Constant as_word => "\k n -> fromInteger $ n .&. ((1 `shiftL` fromInteger k) - 1)".

Recursive Extraction Library os.
