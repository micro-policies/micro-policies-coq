{-# LANGUAGE TypeSynonymInstances, OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Haskell.Pretty (module Haskell.Pretty, module PrettyExports) where

import Haskell.Types
import Haskell.Word
import Haskell.Machine

import Data.Monoid
import Text.PrettyPrint.HughesPJClass hiding ((<>))
import Data.Set (Set)
import qualified Data.Set as S

import Prelude hiding (EQ)

import qualified Text.PrettyPrint.HughesPJClass as PrettyExports hiding ((<>))
import qualified Data.Monoid as PrettyExports ((<>))

-- Should be exported from Text.PrettyPrint.* :-/
appPrec :: Rational
appPrec = 10

(<!>) :: (Pretty a, Pretty b) => a -> b -> Doc
a <!> b = pPrint a <> pPrint b

(<&>) :: (Pretty a, Pretty b) => a -> b -> Doc
a <&> b = pPrint a <+> pPrint b

(<.!>) :: Pretty a => Doc -> a -> Doc
(<.!>) = (<!>)

(<!.>) :: Pretty a => a -> Doc -> Doc
(<!.>) = (<!>)

(<.&>) :: Pretty a => Doc -> a -> Doc
(<.&>) = (<&>)

(<&.>) :: Pretty a => a -> Doc -> Doc
(<&.>) = (<&>)

infixl 6 <!>, <.!>, <!.>, <&>, <.&>, <&.>

plain :: Show a => a -> Doc
plain = text . show

-- There are a lot of orphan instances in this file; basically, imagine that
-- this is where 'Pretty' is defined!

instance Pretty Doc where pPrint = id -- Orphan, I know, but obviously missing!

instance Pretty a => Pretty (Set a) where
  pPrintPrec l _ =
    braces . fsep . punctuate comma . map (pPrintPrec l 0) . S.toList

instance (Pretty v, Pretty t) => Pretty (Atom v t) where
  pPrintPrec l p (v :@ t) =
    let ppp :: Pretty a => a -> Doc
        ppp = pPrintPrec l $ appPrec + 2
    in maybeParens (p > appPrec + 1) $ ppp v <> taggedOp <> ppp t

instance               Pretty (Word n)   where pPrint = plain
instance KnownNat n => Pretty (Signed n) where pPrint = plain

instance Pretty Binop where
  pPrint ADD  = "+"
  pPrint SUB  = "-"
  pPrint MUL  = "*"
  pPrint EQ   = "="
  pPrint LEQ  = "<=?"
  pPrint LEQU = "<=!"
  pPrint AND  = "&"
  pPrint OR   = "|"
  pPrint XOR  = "^"
  pPrint SHRU = ">>"
  pPrint SHL  = "<<"

instance Pretty Reg   where pPrint = plain
instance Pretty Imm   where pPrint = plain
instance Pretty MWord where pPrint = plain

instance Pretty WhereFrom where
  pPrint = plain

instance Pretty PCTag where
  pPrintPrec l p (PC wf cid) =
    let ppp :: Pretty a => a -> Doc
        ppp = pPrintPrec l $ appPrec + 1
    in maybeParens (p > appPrec) $ "PC" <+> ppp wf <+> ppp cid

instance Pretty RegTag where
  pPrint = plain

instance Pretty DataTag where
  pPrintPrec l p (DATA cid ws is) =
    let ppp :: Pretty a => a -> Doc
        ppp = pPrintPrec l $ appPrec + 1
    in maybeParens (p > appPrec) $ "DATA" <+> ppp cid <+> ppp ws <+> ppp is

storesOp :: Doc
storesOp = "->"

getsOp :: Doc
getsOp = "<-"

taggedOp :: Doc
taggedOp = "@"

ptrReg :: Reg -> Doc
ptrReg = (char '*' <!>)

instance Pretty Instr where
  pPrintPrec _ p instr = maybeParens (p > appPrec) $ case instr of
    Nop                     -> nullary "Nop"
    Const    imm dest       -> binary  "Const"       imm                    dest
    Mov      src dest       -> binary  "Mov"         src                    dest
    Binop op src1 src2 dest -> ternary (binopFor op) src1 op src2           dest
    Load     srcA dest      -> binary  "Load"        (ptrReg srcA)          dest
    Store    destA src      -> binary' "Store"       (ptrReg destA) getsOp  src
    Jump     pc'            -> unary   "Jump"        pc'
    Bnz      test delta     -> binary' "Bnz"         test           jumpsOp (withSign delta)
    Jal      pc'            -> unary   "Jal"         pc'
    JumpEpc                 -> nullary "JumpEpc"
    AddRule                 -> nullary "AddRule"
    GetTag   src dest       -> binary  "GetTag"      src                    dest
    PutTag   srcV srcT dest -> ternary "PutTag"      srcV taggedOp srcT     dest
    Halt                    -> nullary "Halt"
    where
      binopFor op = "Binop[" <.!> plain op <!.> "]"
      
      jumpsOp  = "=>" :: Doc
      withSign = ("+" <>) . pPrint . immWord
        -- text . showSigned . Signed . immWord
        -- Oops, 'Bnz' can apparently only jump forward
      
      nullary name                   = name
      unary   name r                 = name <.&> r
      binary' name src op dest       = name <.&> src <&> op <&> dest
      binary  name src dest          = binary' name src storesOp dest
      ternary name src1 op src2 dest = name <.&> src1 <&> op <&> src2 <&> storesOp <&> dest
