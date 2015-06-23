module Haskell.Util.Lifts (
  liftListenStrictWriter, liftPassStrictWriter,
  liftListenLazyWriter,   liftPassLazyWriter,
  liftCatchError,
  liftCatchEither
  ) where

import Control.Monad.Writer.Strict as StrictWriter
import Control.Monad.Writer.Lazy   as LazyWriter
import Control.Monad.Error
import Control.Monad.Trans.Either
import Control.Monad.Signatures

-- Lift monadic operations through their native monad

liftListenStrictWriter :: Monad m => Listen w1 m (a,w2) -> Listen w1 (StrictWriter.WriterT w2 m) a
liftListenStrictWriter listen' m = StrictWriter.WriterT $ do
  ((a,w2),w1) <- listen' $ StrictWriter.runWriterT m
  return ((a,w1),w2)

liftPassStrictWriter :: Monad m => Pass w1 m (a,w2) -> Pass w1 (StrictWriter.WriterT w2 m) a
liftPassStrictWriter pass' m = StrictWriter.WriterT . pass' $ do
  ((a,f),w2) <- StrictWriter.runWriterT m
  return ((a,w2),f)

liftListenLazyWriter :: Monad m => Listen w1 m (a,w2) -> Listen w1 (LazyWriter.WriterT w2 m) a
liftListenLazyWriter listen' m = LazyWriter.WriterT $ do
  ~((a,w2),w1) <- listen' $ LazyWriter.runWriterT m
  return ((a,w1),w2)

liftPassLazyWriter :: Monad m => Pass w1 m (a,w2) -> Pass w1 (LazyWriter.WriterT w2 m) a
liftPassLazyWriter pass' m = LazyWriter.WriterT . pass' $ do
  ~((a,f),w2) <- LazyWriter.runWriterT m
  return ((a,w2),f)

liftCatchError :: Monad m => Catch e1 m (Either e2 a) -> Catch e1 (ErrorT e2 m) a
liftCatchError catch' m h = ErrorT $ runErrorT m `catch'` (runErrorT . h)

liftCatchEither :: Monad m => Catch e1 m (Either e2 a) -> Catch e1 (EitherT e2 m) a
liftCatchEither catch' m h = EitherT $ runEitherT m `catch'` (runEitherT . h)

-- I'm not writing liftCallCCCont because I don't hate myself
