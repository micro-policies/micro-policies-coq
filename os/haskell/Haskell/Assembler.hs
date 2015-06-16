{-# LANGUAGE TupleSections  #-}
module Haskell.Assembler (
  module Haskell.Monad.Assembler,
  SymAssembler,
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
writing instructions, working with immediates vs. machine words, etc.  The
'SymAssembler' type provides the appropriate type parameters to 'Assembler'.
-}

import Control.Arrow
import Control.Applicative hiding (Const(..))
import Control.Monad

import Haskell.Word
import Haskell.Machine

import Haskell.Monad.Assembler

type SymAssembler = Assembler String MWord MWord

instr :: Instr -> SymAssembler ()
instr = asmWord . encodeInstr

instrs :: [Instr] -> SymAssembler ()
instrs = asmWords . map encodeInstr

nop     :: SymAssembler ()
const_  :: Imm -> Reg -> SymAssembler ()
mov     :: Reg -> Reg -> SymAssembler ()
binop   :: Binop -> Reg -> Reg -> Reg -> SymAssembler ()
load    :: Reg -> Reg -> SymAssembler ()
store   :: Reg -> Reg -> SymAssembler ()
jump    :: Reg -> SymAssembler ()
bnz     :: Reg -> Imm -> SymAssembler ()
jal     :: Reg -> SymAssembler ()
jumpEpc :: SymAssembler ()
addRule :: SymAssembler ()
getTag  :: Reg -> Reg -> SymAssembler ()
putTag  :: Reg -> Reg -> Reg -> SymAssembler ()

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

addrToImm :: MWord -> SymAssembler Imm
addrToImm = tryMWordImm pure (asmError . immediateTooBigMsg)

addrToImm' :: MWord -> SymAssembler Imm
addrToImm' = uncurry (<$) . second asmDelayedError
           . tryMWordImm (,Nothing)
                         (   imm . unsignedWord . mwordWord
                         &&& Just . immediateTooBigMsg)

hereImm :: SymAssembler Imm
hereImm = addrToImm =<< here

reserveImm :: MWord -> SymAssembler Imm
reserveImm = addrToImm' <=< reserve
