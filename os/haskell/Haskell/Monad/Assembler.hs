{-|
Module      : Haskell.Monad.Assembler
Description : Monad transformer and class for assembling a Von Neumann-architecture machine
Copyright   : © 2015 Antal Spector-Zabusky
License     : BSD3
Maintainer  : Antal Spector-Zabusky <antal.b.sz@gmail.com>
Stability   : experimental
Portability : GHC only

This module provides an 'AssemblerT' monad transformer and a 'MonadAssembler'
monad class, which represent monads that support generating the memory of a Von
Neumann-architecture machine.  For more information and documentation see
"Haskell.Monad.Trans.Assembler" and, to a lesser extent,
"Haskell.Monad.Assembler.Class".
-}

module Haskell.Monad.Assembler (
  module Haskell.Monad.Assembler.Class,
  module Haskell.Monad.Trans.Assembler
  ) where

import Haskell.Monad.Assembler.Class
import Haskell.Monad.Trans.Assembler hiding
  ( asmWord, asmWords, reserve
  , here, reservedSegment
  , asmError, asmDelayedError
  , program )
