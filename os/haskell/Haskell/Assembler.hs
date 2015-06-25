{-# LANGUAGE ConstraintKinds, FlexibleContexts, TupleSections #-}

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
  module Haskell.Monad.Assembler,
  MonadSymAssembler, SymAssemblerT, SymAssembler,
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

import Haskell.Machine

import Haskell.Monad.Assembler

-- |A 'MonadAssembler' monad class/constraint for the symbolic machine.  Errors
-- are 'String's; pointers and words are both 'MWord's.
type MonadSymAssembler = MonadAssembler String MWord MWord

-- |An 'AssemblerT' monad transformer for the symbolic machine.  Errors are
-- 'String's; pointers and words are both 'MWord's.
type SymAssemblerT = AssemblerT String MWord MWord

-- |An 'Assembler' monad for the symbolic machine.  Errors are 'String's;
-- pointers and words are both 'MWord's.
type SymAssembler = Assembler String MWord MWord

-- |Encodes and writes a single instruction to the instruction stream.
instr :: MonadSymAssembler m => Instr -> m ()
instr = asmWord . encodeInstr

-- |Encodes and writes a list of instructions to the instruction stream.
instrs :: MonadFix m => [Instr] -> SymAssemblerT m ()
instrs = asmWords . map encodeInstr

nop     :: MonadSymAssembler m => m ()                               -- ^Write a 'Nop' instruction to the instruction stream
const_  :: MonadSymAssembler m => Imm -> Reg -> m ()                 -- ^Write a 'Const' instruction to the instruction stream
mov     :: MonadSymAssembler m => Reg -> Reg -> m ()                 -- ^Write a 'Mov' instruction to the instruction stream
binop   :: MonadSymAssembler m => Binop -> Reg -> Reg -> Reg -> m () -- ^Write a 'Binop' instruction to the instruction stream
load    :: MonadSymAssembler m => Reg -> Reg -> m ()                 -- ^Write a 'Load' instruction to the instruction stream
store   :: MonadSymAssembler m => Reg -> Reg -> m ()                 -- ^Write a 'Store' instruction to the instruction stream
jump    :: MonadSymAssembler m => Reg -> m ()                        -- ^Write a 'Jump' instruction to the instruction stream
bnz     :: MonadSymAssembler m => Reg -> Imm -> m ()                 -- ^Write a 'Bnz' instruction to the instruction stream
jal     :: MonadSymAssembler m => Reg -> m ()                        -- ^Write a 'Jal' instruction to the instruction stream
jumpEpc :: MonadSymAssembler m => m ()                               -- ^Write a 'JumpEpc' instruction to the instruction stream
addRule :: MonadSymAssembler m => m ()                               -- ^Write an 'AddRule' instruction to the instruction stream
getTag  :: MonadSymAssembler m => Reg -> Reg -> m ()                 -- ^Write a 'GetTag' instruction to the instruction stream
putTag  :: MonadSymAssembler m => Reg -> Reg -> Reg -> m ()          -- ^Write a 'PutTag' instruction to the instruction stream
halt    :: MonadSymAssembler m => m ()                               -- ^Write a 'Halt' instruction to the instruction stream

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
  let n = toInteger w
  in if n <= toInteger (maxBound :: Imm)
     then fImm $ imm n
     else fWord w
                                                                         
-- |An error message to display when the given word is too big to fit into an
-- immediate.
immediateTooBigMsg :: MWord -> String
immediateTooBigMsg a = "Address " ++ show a ++ " is too big to be immediate."

-- |Convert a word into an immediate, failing /immediately/ if the word was out
-- of range.  Do not use with time-traveling information (such as the result of
-- 'reserve').
addrToImm :: MonadSymAssembler m => MWord -> m Imm
addrToImm = tryMWordImm pure (asmError . immediateTooBigMsg)

-- |Convert a word into an immediate, with a /delayed/ failure if the word was
-- out of range.  This function is safe to use with time-traveling information
-- (such as the result of 'reserve').
addrToImm' :: MonadSymAssembler m => MWord -> m Imm
addrToImm' = uncurry (<$) . second asmDelayedError
           . tryMWordImm (,Nothing)
                         (fromIntegral &&& Just . immediateTooBigMsg)

-- |Return the current instruction address as an immediate (see also 'here');
-- fails immediately if the current instruction address does not fit into an
-- immediate.
hereImm :: MonadSymAssembler m => m Imm
hereImm = addrToImm =<< here

-- |Reserve some data and return its address as an immediate (see also
-- 'reserve'); causes a delayed failure if the current instruction address does
-- not fit into an immediate.
reserveImm :: MonadSymAssembler m => MWord -> m Imm
reserveImm = addrToImm' <=< reserve
