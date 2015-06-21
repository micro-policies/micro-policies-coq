{-# LANGUAGE TupleSections  #-}

{-|
Module      : Haskell.Assembler
Description : Utilities for assembling a symbolic machine
Copyright   : © 2015 Antal Spector-Zabusky
License     : BSD3
Maintainer  : Antal Spector-Zabusky <antal.b.sz@gmail.com>
Stability   : experimental
Portability : GHC only

This module provides the 'Assembler' monad from "Haskell.Monad.Trans.Assembler"
with utilities for working with the symbolic machine from "Haskell.Machine":
ways of writing instructions, working with immediates vs. machine words, etc.
The 'SymAssembler' type provides the appropriate type parameters to 'Assembler'.
-}

module Haskell.Assembler (
  module Haskell.Monad.Trans.Assembler,
  SymAssemblerT, SymAssembler,
  instr, instrs,
  nop, const_, mov, binop, load, store, jump, bnz, jal,
  jumpEpc, addRule, getTag, putTag,
  halt,
  tryMWordImm,
  immediateTooBigMsg, addrToImm, addrToImm',
  hereImm, reserveImm
  ) where

import Control.Arrow
import Control.Applicative hiding (Const(..))
import Control.Monad
import Control.Monad.Fix

import Haskell.Word
import Haskell.Machine

import Haskell.Monad.Trans.Assembler

-- |An 'AssemblerT' monad transformer for the symbolic machine.  Errors are
-- 'String's; pointers and words are both 'MWord's.
type SymAssemblerT = AssemblerT String MWord MWord

-- |An 'Assembler' monad for the symbolic machine.  Errors are 'String's;
-- pointers and words are both 'MWord's.
type SymAssembler = Assembler String MWord MWord

-- |Encodes and writes a single instruction to the instruction stream.
instr :: MonadFix m => Instr -> SymAssemblerT m ()
instr = asmWord . encodeInstr

-- |Encodes and writes a list of instructions to the instruction stream.
instrs :: MonadFix m => [Instr] -> SymAssemblerT m ()
instrs = asmWords . map encodeInstr

nop     :: MonadFix m => SymAssemblerT m ()                               -- ^Write a 'Nop' instruction to the instruction stream
const_  :: MonadFix m => Imm -> Reg -> SymAssemblerT m ()                 -- ^Write a 'Const' instruction to the instruction stream
mov     :: MonadFix m => Reg -> Reg -> SymAssemblerT m ()                 -- ^Write a 'Mov' instruction to the instruction stream
binop   :: MonadFix m => Binop -> Reg -> Reg -> Reg -> SymAssemblerT m () -- ^Write a 'Binop' instruction to the instruction stream
load    :: MonadFix m => Reg -> Reg -> SymAssemblerT m ()                 -- ^Write a 'Load' instruction to the instruction stream
store   :: MonadFix m => Reg -> Reg -> SymAssemblerT m ()                 -- ^Write a 'Store' instruction to the instruction stream
jump    :: MonadFix m => Reg -> SymAssemblerT m ()                        -- ^Write a 'Jump' instruction to the instruction stream
bnz     :: MonadFix m => Reg -> Imm -> SymAssemblerT m ()                 -- ^Write a 'Bnz' instruction to the instruction stream
jal     :: MonadFix m => Reg -> SymAssemblerT m ()                        -- ^Write a 'Jal' instruction to the instruction stream
jumpEpc :: MonadFix m => SymAssemblerT m ()                               -- ^Write a 'JumpEpc' instruction to the instruction stream
addRule :: MonadFix m => SymAssemblerT m ()                               -- ^Write an 'AddRule' instruction to the instruction stream
getTag  :: MonadFix m => Reg -> Reg -> SymAssemblerT m ()                 -- ^Write a 'GetTag' instruction to the instruction stream
putTag  :: MonadFix m => Reg -> Reg -> Reg -> SymAssemblerT m ()          -- ^Write a 'PutTag' instruction to the instruction stream
halt    :: MonadFix m => SymAssemblerT m ()                               -- ^Write a 'Halt' instruction to the instruction stream

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
addrToImm :: MonadFix m => MWord -> SymAssemblerT m Imm
addrToImm = tryMWordImm pure (asmError . immediateTooBigMsg)

-- |Convert a word into an immediate, with a /delayed/ failure if the word was
-- out of range.  This function is safe to use with time-traveling information
-- (such as the result of 'reserve').
addrToImm' :: MonadFix m => MWord -> SymAssemblerT m Imm
addrToImm' = uncurry (<$) . second asmDelayedError
           . tryMWordImm (,Nothing)
                         (   imm . unsignedWord . mwordWord
                         &&& Just . immediateTooBigMsg)

-- |Return the current instruction address as an immediate (see also 'here');
-- fails immediately if the current instruction address does not fit into an
-- immediate.
hereImm :: MonadFix m => SymAssemblerT m Imm
hereImm = addrToImm =<< here

-- |Reserve some data and return its address as an immediate (see also
-- 'reserve'); causes a delayed failure if the current instruction address does
-- not fit into an immediate.
reserveImm :: MonadFix m => MWord -> SymAssemblerT m Imm
reserveImm = addrToImm' <=< reserve
