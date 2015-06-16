{-# LANGUAGE TupleSections  #-}
module Haskell.Assembler (
  module Haskell.Monad.Assembler,
  instr, instrs,
  nop, const_, mov, binop, load, store, jump, bnz, jal,
  jumpEpc, addRule, getTag, putTag,
  tryMWordImm,
  immediateTooBigMsg, addrToImm, addrToImm',
  hereImm, reserveImm
  ) where

{-|
Module      : Haskell.Assembler
Description : Utilities for assembling a symbolic machine
Copyright   : © 2015 Antal Spector-Zabusky
License     : BSD3
Maintainer  : Antal Spector-Zabusky <antal.b.sz@gmail.com>
Stability   : experimental
Portability : GHC only

This module provides the 'Assembler' monad from "Haskell.Monad.Assembler" with
utilities for working with the symbolic machine from "Haskell.Machine": ways of
writing instructions, working with immediates vs. machine words, etc.

-}

import Control.Arrow
import Control.Applicative hiding (Const(..))
import Control.Monad

import Haskell.Word
import Haskell.Machine

import Haskell.Monad.Assembler

instr :: Instr -> Assembler ()
instr = asmWord . encodeInstr

instrs :: [Instr] -> Assembler ()
instrs = asmWords . map encodeInstr

nop     :: Assembler ()
const_  :: Imm -> Reg -> Assembler ()
mov     :: Reg -> Reg -> Assembler ()
binop   :: Binop -> Reg -> Reg -> Reg -> Assembler ()
load    :: Reg -> Reg -> Assembler ()
store   :: Reg -> Reg -> Assembler ()
jump    :: Reg -> Assembler ()
bnz     :: Reg -> Imm -> Assembler ()
jal     :: Reg -> Assembler ()
jumpEpc :: Assembler ()
addRule :: Assembler ()
getTag  :: Reg -> Reg -> Assembler ()
putTag  :: Reg -> Reg -> Reg -> Assembler ()

nop     = instr                Nop
const_  = (instr .)          . Const
mov     = (instr .)          . Mov
binop   = (((instr .) .) .)  . Binop
load    = (instr .)          . Load
store   = (instr .)          . Store
jump    = instr              . Jump
bnz     = (instr .)          . Bnz
jal     = instr              . Jal
jumpEpc = instr                JumpEpc
addRule = instr                AddRule
getTag  = (instr .)          . GetTag
putTag  = ((instr .) .)      . PutTag
halt    = instr                Halt

tryMWordImm :: (Imm -> a) -> (MWord -> a) -> MWord -> a
tryMWordImm fImm fWord w =
  let n = unsignedWord $ mwordWord w
  in if n <= unsignedWord (immWord maxBound)
     then fImm $ imm n
     else fWord w
                                                                         
immediateTooBigMsg :: MWord -> String
immediateTooBigMsg a = "Address " ++ show a ++ " is too big to be immediate."

addrToImm :: MWord -> Assembler Imm
addrToImm = tryMWordImm pure (asmError . immediateTooBigMsg)

addrToImm' :: MWord -> Assembler Imm
addrToImm' = uncurry (<$) . second asmDelayedError
           . tryMWordImm (,Nothing)
                         (   imm . unsignedWord . mwordWord
                         &&& Just . immediateTooBigMsg)

hereImm :: Assembler Imm
hereImm = addrToImm =<< here

reserveImm :: MWord -> Assembler Imm
reserveImm = addrToImm' <=< reserve
