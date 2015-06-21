{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies,
             FlexibleInstances, UndecidableInstances #-}

{-|
Module      : Haskell.Monad.Assembler.Class
Description : Monad class for assembling a Von Neumann-architecture machine
Copyright   : © 2015 Antal Spector-Zabusky
License     : BSD3
Maintainer  : Antal Spector-Zabusky <antal.b.sz@gmail.com>
Stability   : experimental
Portability : GHC only

This module provides a 'MonadAssembler' monad class which models monads that
support generating the memory of a Von Neumann-architecture machine.  The
intended model of this class is the 'AssemblerT' monad transformer from
"Haskell.Monad.Trans.Assembler"; for more information and documentation, see
that module.
-}

module Haskell.Monad.Assembler.Class (MonadAssembler(..)) where

import Control.Monad.Fix

import qualified Haskell.Monad.Trans.Assembler as A

import           Control.Monad.Trans
import           Control.Monad.Trans.Identity
import           Control.Monad.Trans.Reader
import qualified Control.Monad.Trans.Writer.Lazy   as WL
import qualified Control.Monad.Trans.Writer.Strict as WS
import qualified Control.Monad.Trans.State.Lazy    as SL
import qualified Control.Monad.Trans.State.Strict  as SS
import qualified Control.Monad.Trans.RWS.Lazy      as RWSL
import qualified Control.Monad.Trans.RWS.Strict    as RWSS
import           Control.Monad.Trans.Maybe
import           Control.Monad.Trans.Except
import           Control.Monad.Trans.Either
import           Control.Monad.Trans.Error
import           Data.Monoid

class (MonadFix m, Integral p, Ord p, Num w) => MonadAssembler e p w m | m -> e p w where
  -- Should I leave the non-'MonadFix' constraints on the class?  Unsure...
  asmWords :: [w] -> m ()
  asmWord  :: w -> m ()
  asmWord w = asmWords [w]

  reserve :: p -> m p

  here            :: m p
  reservedSegment :: m p
  
  asmError        :: e -> m a
  asmDelayedError :: Maybe e -> m ()

  program :: m a -> m a

instance (MonadFix m, Integral p, Ord p, Num w) => MonadAssembler e p w (A.AssemblerT e p w m) where
  asmWords = A.asmWords
  asmWord  = A.asmWord

  reserve = A.reserve
  
  here            = A.here
  reservedSegment = A.reservedSegment

  asmError        = A.asmError
  asmDelayedError = A.asmDelayedError

  program = A.program

instance MonadAssembler e p w m => MonadAssembler e p w (IdentityT m) where
  asmWords = lift . asmWords
  asmWord  = lift . asmWord

  reserve = lift . reserve
  
  here            = lift here
  reservedSegment = lift reservedSegment

  asmError        = lift . asmError
  asmDelayedError = lift . asmDelayedError

  program = mapIdentityT program
  
instance MonadAssembler e p w m => MonadAssembler e p w (ReaderT r m) where
  asmWords = lift . asmWords
  asmWord  = lift . asmWord

  reserve = lift . reserve
  
  here            = lift here
  reservedSegment = lift reservedSegment

  asmError        = lift . asmError
  asmDelayedError = lift . asmDelayedError

  program = mapReaderT program

instance (Monoid v, MonadAssembler e p w m) => MonadAssembler e p w (WL.WriterT v m) where
  asmWords = lift . asmWords
  asmWord  = lift . asmWord

  reserve = lift . reserve
  
  here            = lift here
  reservedSegment = lift reservedSegment

  asmError        = lift . asmError
  asmDelayedError = lift . asmDelayedError

  program = WL.mapWriterT program

instance (Monoid v, MonadAssembler e p w m) => MonadAssembler e p w (WS.WriterT v m) where
  asmWords = lift . asmWords
  asmWord  = lift . asmWord

  reserve = lift . reserve
  
  here            = lift here
  reservedSegment = lift reservedSegment

  asmError        = lift . asmError
  asmDelayedError = lift . asmDelayedError

  program = WS.mapWriterT program

instance MonadAssembler e p w m => MonadAssembler e p w (SL.StateT s m) where
  asmWords = lift . asmWords
  asmWord  = lift . asmWord

  reserve = lift . reserve
  
  here            = lift here
  reservedSegment = lift reservedSegment

  asmError        = lift . asmError
  asmDelayedError = lift . asmDelayedError

  program = SL.mapStateT program

instance MonadAssembler e p w m => MonadAssembler e p w (SS.StateT s m) where
  asmWords = lift . asmWords
  asmWord  = lift . asmWord

  reserve = lift . reserve
  
  here            = lift here
  reservedSegment = lift reservedSegment

  asmError        = lift . asmError
  asmDelayedError = lift . asmDelayedError

  program = SS.mapStateT program

instance (Monoid v, MonadAssembler e p w m) => MonadAssembler e p w (RWSL.RWST r v s m) where
  asmWords = lift . asmWords
  asmWord  = lift . asmWord

  reserve = lift . reserve
  
  here            = lift here
  reservedSegment = lift reservedSegment

  asmError        = lift . asmError
  asmDelayedError = lift . asmDelayedError

  program = RWSL.mapRWST program

instance (Monoid v, MonadAssembler e p w m) => MonadAssembler e p w (RWSS.RWST r v s m) where
  asmWords = lift . asmWords
  asmWord  = lift . asmWord

  reserve = lift . reserve
  
  here            = lift here
  reservedSegment = lift reservedSegment

  asmError        = lift . asmError
  asmDelayedError = lift . asmDelayedError

  program = RWSS.mapRWST program

instance MonadAssembler e p w m => MonadAssembler e p w (MaybeT m) where
  asmWords = lift . asmWords
  asmWord  = lift . asmWord

  reserve = lift . reserve
  
  here            = lift here
  reservedSegment = lift reservedSegment

  asmError        = lift . asmError
  asmDelayedError = lift . asmDelayedError

  program = mapMaybeT program

instance MonadAssembler e p w m => MonadAssembler e p w (ExceptT x m) where
  asmWords = lift . asmWords
  asmWord  = lift . asmWord

  reserve = lift . reserve
  
  here            = lift here
  reservedSegment = lift reservedSegment

  asmError        = lift . asmError
  asmDelayedError = lift . asmDelayedError

  program = mapExceptT program

instance MonadAssembler e p w m => MonadAssembler e p w (EitherT x m) where
  asmWords = lift . asmWords
  asmWord  = lift . asmWord

  reserve = lift . reserve
  
  here            = lift here
  reservedSegment = lift reservedSegment

  asmError        = lift . asmError
  asmDelayedError = lift . asmDelayedError

  program = mapEitherT program

instance (Error x, MonadAssembler e p w m) => MonadAssembler e p w (ErrorT x m) where
  asmWords = lift . asmWords
  asmWord  = lift . asmWord

  reserve = lift . reserve
  
  here            = lift here
  reservedSegment = lift reservedSegment

  asmError        = lift . asmError
  asmDelayedError = lift . asmDelayedError

  program = mapErrorT program
