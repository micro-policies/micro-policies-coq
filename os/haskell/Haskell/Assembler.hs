{-# LANGUAGE TupleSections  #-}

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

import Control.Arrow
import Control.Applicative hiding (Const(..))
import Control.Monad

import Haskell.Word
import Haskell.Machine

import Haskell.Monad.Assembler

-- |An 'Assembler' monad for the symbolic machine.  Errors are 'String's;
-- pointers and words are both 'MWord's.
type SymAssembler = Assembler String MWord MWord

-- |Encodes and writes a single instruction to the instruction stream.
instr :: Instr -> SymAssembler ()
instr = asmWord . encodeInstr

-- |Encodes and writes a list of instructions to the instruction stream.
instrs :: [Instr] -> SymAssembler ()
instrs = asmWords . map encodeInstr

nop     :: SymAssembler ()                               -- ^Write a 'Nop' instruction to the instruction stream
const_  :: Imm -> Reg -> SymAssembler ()                 -- ^Write a 'Const' instruction to the instruction stream
mov     :: Reg -> Reg -> SymAssembler ()                 -- ^Write a 'Mov' instruction to the instruction stream
binop   :: Binop -> Reg -> Reg -> Reg -> SymAssembler () -- ^Write a 'Binop' instruction to the instruction stream
load    :: Reg -> Reg -> SymAssembler ()                 -- ^Write a 'Load' instruction to the instruction stream
store   :: Reg -> Reg -> SymAssembler ()                 -- ^Write a 'Store' instruction to the instruction stream
jump    :: Reg -> SymAssembler ()                        -- ^Write a 'Jump' instruction to the instruction stream
bnz     :: Reg -> Imm -> SymAssembler ()                 -- ^Write a 'Bnz' instruction to the instruction stream
jal     :: Reg -> SymAssembler ()                        -- ^Write a 'Jal' instruction to the instruction stream
jumpEpc :: SymAssembler ()                               -- ^Write a 'JumpEpc' instruction to the instruction stream
addRule :: SymAssembler ()                               -- ^Write an 'AddRule' instruction to the instruction stream
getTag  :: Reg -> Reg -> SymAssembler ()                 -- ^Write a 'GetTag' instruction to the instruction stream
putTag  :: Reg -> Reg -> Reg -> SymAssembler ()          -- ^Write a 'PutTag' instruction to the instruction stream

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

-- |@tryMWordImm fImm fWord w@ checks if the word @w@ fits into an immediate.
-- If it does, then 'fImm' is called on the resulting immediate; if it does not,
-- 'fWord' is called on the original word.
tryMWordImm :: (Imm -> a) -> (MWord -> a) -> MWord -> a
tryMWordImm fImm fWord w =
  let n = unsignedWord $ mwordWord w
  in if n <= unsignedWord (immWord maxBound)
     then fImm $ imm n
     else fWord w
                                                                         
-- |An error message to display when the given word is too big to fit into an
-- immediate.
immediateTooBigMsg :: MWord -> String
immediateTooBigMsg a = "Address " ++ show a ++ " is too big to be immediate."

-- |Convert a word into an immediate, failing /immediately/ if the word was out
-- of range.  Do not use with time-traveling information (such as the result of
-- 'reserve').
addrToImm :: MWord -> SymAssembler Imm
addrToImm = tryMWordImm pure (asmError . immediateTooBigMsg)

-- |Convert a word into an immediate, with a /delayed/ failure if the word was
-- out of range.  This function is safe to use with time-traveling information
-- (such as the result of 'reserve').
addrToImm' :: MWord -> SymAssembler Imm
addrToImm' = uncurry (<$) . second asmDelayedError
           . tryMWordImm (,Nothing)
                         (   imm . unsignedWord . mwordWord
                         &&& Just . immediateTooBigMsg)

-- |Return the current instruction address as an immediate (see also 'here');
-- fails immediately if the current instruction address does not fit into an
-- immediate.
hereImm :: SymAssembler Imm
hereImm = addrToImm =<< here

-- |Reserve some data and return its address as an immediate (see also
-- 'reserve'); causes a delayed failure if the current instruction address does
-- not fit into an immediate.
reserveImm :: MWord -> SymAssembler Imm
reserveImm = addrToImm' <=< reserve
