{-# LANGUAGE GeneralizedNewtypeDeriving, ViewPatterns, LambdaCase, RecursiveDo,
             MultiParamTypeClasses, FlexibleInstances, UndecidableInstances,
             TemplateHaskell #-}

{-|
Module      : Haskell.Monad.Trans.Assembler
Description : Monad transformer for assembling a Von Neumann-architecture machine
Copyright   : © 2015 Antal Spector-Zabusky
License     : BSD3
Maintainer  : Antal Spector-Zabusky <antal.b.sz@gmail.com>
Stability   : experimental
Portability : GHC only

This module provides an 'AssemblerT' monad transformer which supports generating
the memory of a Von Neumann-architecture machine.  The general model is as
follows.  We maintain two simultaneous streams of words which can be added to: a
stream of instructions, and a stream of data.  Once the machine memory is
assembled, the instructions will be immediately followed by the data, and the
data will be all 0s.  Words can be added to the current instruction stream
(using 'asmWord' or 'asmWords'), and the address of the current instruction
('here') will be maintained; data can be "reserved" in size-@n@ chunks, which
allocates @n@ @0@s on the end of the data segment and returns the address of the
first (using 'reserve').

In order to actually allocate the reserved words and place the current
instruction pointer after them, the 'program' operation is used; this allocates
all the reserved @0@s, resets the reservation count and location, and moves the
current instruction pointer after the old data segment.  This allows for writing
a number of disconnected programs/functions/processes, each with their own
directly-adjacent address space.  (When running an 'AssemblerT' computation, it
is wrapped in one final 'program'.)

'AssemblerT' supports the following operations:

    * Writing a word or words to the next free location in the memory;
      notionally, these are the instructions.  ('asmWord', 'asmWords')
    * Reserving some number of words to follow the instructions (returning the
      address of the first reserved word); notionally, this is data memory.
      ('reserve')
    * Getting the current address. ('here')
    * Getting the address of the start of the current reserved segment.
      ('reservedSegment')
    * Throwing an error (either immediate or delayed; see below).  ('asmError',
      'asmDelayedError')
    * Completing the reservation process and advancing the current instruction
      past the reserved words.  ('program')

'AssemblerT' is parametrized by the following types, as
@'AssemblerT' e p w m a@:

    * The type @e@ of error messages.
    * The type @p@ of pointers (should be an 'Integral').
    * The type @w@ of words (should be a 'Num', but only so we can get a @0@).
    * The type @m@ that's the transformed monad (should be a 'MonadFix', not
      simply a 'Monad').
    * The type @a@ of results.

Pointers should be integer-like, and their difference should be another pointer;
this allows the use of the same type for pointers and sizes, which is a bit
specious but works and is commonly the case.

In order to write forward and backward jumps, the 'here' operation is used.
Since 'AssemblerT' is a 'MonadFix', we can use the @RecursiveDo@ @LANGUAGE@
pragma's @mdo@ syntax to write forward jumps quite neatly:

@
    mdo
      'asmWords' . map encodeInstruction $
        [ Const addr r0
        , Jump r0
        , Halt {- Skipped -} ] 
      addr <- 'here'
      'asmWord' $ encodeInstruction Nop
@

This code (given implementations of the missing types and functions) produces a
machine whose instruction memory contains

@
    0: Const #3 -> %r0
    1: Jump %r0
    2: Halt
    3: Nop
@

We can thus safely forward-reference addresses to write our jumps!

Relatedly, the reservation facility also requires "time-traveling" information:
the address of the start of the data segment is not determined until all
instructions (in the current 'program') have been written!  This means that
'reserve' works fine (as does 'reservedSegment'), you must be careful with its
result: any case-analysis on the returned address cannot be used to determine
which monadic action to run, or the knot-tying will become an infinite loop!

This is the rationale for the delayed-error facility provided by
'asmDelayedError'.  If given a 'Nothing', then no error is reported.  If given
@'Just' err@, then an error is reported – but only once the /entire/ computation
has run!  Thus, 'asmError' is more efficient, since it's short-circuiting; the
two functions also has different semantics:
@'runAssembler' $ 'asmError' "err" >> undefined@ evaluates to @Left "err"@,
whereas @'runAssembler' $ 'asmDelayedError' (Just "err") >> undefined@ crashes.

However, as a result, code such as

@
    do addr <- 'reserve' 8
       if fitsInImmediate addr
         then 'asmWord' . encodeInstruction $ Const (immediate addr) r0
         else 'asmError' "Address too large"
@

is a time paradox/infinite loop: since the value of @addr@ comes from the
future, we can't safely branch on it to determine what the future should look
like.  To avoid this, we can use 'asmDelayedError':

@
    do addr <- 'reserve' 8
       'asmDelayedError' $ if fitsInImmediate addr
                           then Nothing
                           else Just "Address too large"
       'asmWord' . encodeInstruction $ Const (immediate addr) r0
@

Now, the branching on 'addr' is /outside/ the monad, and so is safe; this
ability to branch in the argument is exactly why 'asmDelayedError' takes a
'Maybe'.  We also unconditionally emit a @Const@ instruction (assuming that the
notional @immediate@ function wraps around when given an out-of-range value);
this will never be /seen/ in the error case, but it /will/ be run.

I got the 'MonadFix' assembler with forward-references to labels from the
following (in order of my personal discovery thereof):

    * Lewis, aka quietfanatic.  "An ASM Monad".  October 15, 2013.  Available at
      <http://wall.org/~lewis/2013/10/15/asm-monad.html>.
    * Russell O'Connor.  "Assembly: Circular Programming with Recursive do".
      /The Monad.Reader/, issue 6, pp. 35–53.  January 31, 2007.  Available at
      <https://wiki.haskell.org/wikiupload/1/14/TMR-Issue6.pdf>.

The other time-travel fragment – use of reverse-traveling state to manage
reserved data segments after the instructions -- is my own idea.  (Using
'MonadFix' to read the forward-traveling state that keeps track of the current
instruction before they've been written is from the above citations.)
-}

module Haskell.Monad.Trans.Assembler (
  -- * The 'AssemblerT' monad transformer
  AssemblerT(), runAssemblerT, execAssemblerT,
  -- * The 'Assembler' monad
  Assembler(), runAssembler, execAssembler,
  -- * Writing instructions and data
  asmWord, asmWords, reserve,
  -- * The current location(s)
  here, reservedSegment,
  -- * Error reporting
  asmError, asmDelayedError,
  -- * Separating different assembly programs
  program
  ) where

import Control.Applicative
import Control.Monad
import Control.Monad.Tardis as Tardis
import Control.Monad.Writer.Strict
import Control.Monad.State.Lazy
import Control.Monad.Trans.Either
import Control.Monad.Error

import Control.Lens
import Data.List

import qualified Control.Monad.Trans.Writer.Strict as Writer
import qualified Control.Monad.Trans.State.Lazy    as State
import Control.Monad.Reader
import Control.Monad.Cont

import Haskell.Util.Lifts

-- |A monad transformer which acts as a simple assembler.  See the package
-- description for its use and description.  It is parametrized by a type of
-- error messages (@e@), a type of pointers/addresses/sizes (@p@, probably an
-- 'Integral'), and a type of words (@w@, which is probably a 'Num' to allow the
-- use of @0@).
newtype AssemblerT e -- ^The type of error messages
                   p -- ^The type of pointers/addresses (and sizes)
                   w -- ^The type of words
                   m -- ^The transformed monad
                   a -- ^The value type
  = AssemblerT
      (TardisT p (Counters p) (WriterT [w] (StateT (Maybe e) (EitherT e m))) a)
  deriving ( Functor, Applicative, Monad, MonadFix
           , MonadReader r, MonadCont, MonadIO)
               -- We lift the mtl classes that we can automatically; for nested
               -- Tardis/Writer/State/Either, we do it ourselves
-- See Note [AssemblerT implementation]

-- I don't know why I can't just derive this
instance MonadTrans (AssemblerT e p w) where
  lift = AssemblerT . lift . lift . lift . lift

instance (MonadFix m, MonadError f m) => MonadError f (AssemblerT e p w m) where
  throwError =
    AssemblerT . lift . lift . lift . lift . throwError
  catchError (AssemblerT asm) handler =
    AssemblerT $
      (Tardis.liftCatch . Writer.liftCatch . State.liftCatch . liftCatchEither)
      catchError
      asm
      (\e -> case handler e of AssemblerT asm' -> asm')

instance (MonadFix m, MonadWriter v m) =>
         MonadWriter v (AssemblerT e p w m) where
  writer =
    AssemblerT . lift . lift . writer
  tell =
    AssemblerT . lift . lift . tell
  listen (AssemblerT asm) =
    AssemblerT $ Tardis.liftListen (liftListenStrictWriter listen) asm
  pass (AssemblerT asm) =
    AssemblerT $ Tardis.liftPass (liftPassStrictWriter pass) asm

instance (MonadFix m, MonadState s m) => MonadState s (AssemblerT e p w m) where
  get   = AssemblerT . lift . lift . lift $ get
  put   = AssemblerT . lift . lift . lift . put
  state = AssemblerT . lift . lift . lift . state

instance (MonadFix m, MonadTardis bw fw m) =>
         MonadTardis bw fw (AssemblerT e p w m) where
  -- Sigh... 'EitherT' doesn't have a MonadTardis instance
  getPast    = AssemblerT . lift . lift . lift . lift $ getPast
  getFuture  = AssemblerT . lift . lift . lift . lift $ getFuture
  sendPast   = AssemblerT . lift . lift . lift . lift . sendPast
  sendFuture = AssemblerT . lift . lift . lift . lift . sendFuture
  tardis     = AssemblerT . lift . lift . lift . lift . tardis
               
{-
Note [AssemblerT implementation]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The components of the implementation of 'AssemblerT' are as follows:

  * The backwards-traveling 'TardisT' state is the address of the start of
    the reserved data segment.
  * The forward-traveling 'TardisT' state is a pair of (a) the current
    instruction address, and (b) how much data has been reserved.  (The
    address of the to-be-reserved block depends on both the backwards and the
    forwards-traveling state.)
  * The 'WriterT' log is the instruction stream, sans reserved words (any
    previously-completed 'program's have been placed in the instruction
    stream).
  * The 'StateT' and 'EitherT' combine to give the delayed and
    short-circuiting error behaviors, respectively.  The short-circuiting
    error behavior is clear.  A delayed error is encoded by setting the state
    to @'Just' err@ (in practice, only the first such update is allowed to
    stick); during 'runAssemblerT', if the state evaluated to @'Just' err@,
    then @'Left' err@ is returned, just as if the 'Either' had failed.
-}

-- |A monad which acts as a simple assembler.  A specialization of 'AssemblerT',
-- which see.  Also see the package description for further information on
-- 'Assembler''s use and description.  It is parametrized by a type of error
-- messages (@e@), a type of pointers/addresses/sizes (@p@, probably an
-- 'Integral'), and a type of words (@w@, which is probably a 'Num' to allow the
-- use of @0@).
type Assembler e -- ^The type of error messages
               p -- ^The type of pointers/addresses (and sizes)
               w -- ^The type of words
  = AssemblerT e p w Identity

-- |Unexported data type for the forward-traveling state in an 'AssemblerT';
-- contains the current instruction address ('_currentInstruction') and the
-- number of instructions that have been reserved inside the current 'program'
-- ('_reservedInstructions').
data Counters p = Counters { _currentInstruction   :: !p
                           , _reservedInstructions :: !p }
                deriving (Eq, Ord, Show)
makeLenses ''Counters

-- |Run an 'AssemblerT' computation, producing either (a) a (delayed or
-- short-circuiting) error message, or (b) a pair of the result and the
-- constructed machine memory.  The instruction stream starts at address @0@.
runAssemblerT :: (MonadFix m, Integral p, Num w)
              => AssemblerT e p w m a -> m (Either e (a,[w]))
runAssemblerT (program -> AssemblerT asm) =
  runEitherT . runDelayedError . runWriterT $ evalTardisT asm initialState
  where
    runDelayedError = flip runStateT Nothing >=> \case
                        (_, Just err) -> throwError err
                        (r, Nothing)  -> pure r
    
    initialDataAddr = error $  "runAssemblerT: Somehow accessed undefined "
                            ++ "initial time-traveling data segment address."
    
    initialCounters = Counters { _currentInstruction   = 0
                               , _reservedInstructions = 0 }
    
    initialState = (initialDataAddr, initialCounters)

-- |Run an 'AssemblerT' computation, just producing the memory (or an error) and
-- ignoring the result.  The instruction stream starts at address @0@.
execAssemblerT :: (MonadFix m, Integral p, Num w)
               => AssemblerT e p w m a -> m (Either e [w])
execAssemblerT = liftM (fmap snd) . runAssemblerT

-- |Run an 'Assembler' computation, producing either (a) a (delayed or
-- short-circuiting) error message, or (b) a pair of the result and the
-- constructed machine memory.  The instruction stream starts at address @0@.
runAssembler :: (Integral p, Num w)
             => Assembler e p w a -> Either e (a,[w])
runAssembler = runIdentity . runAssemblerT

-- |Run an 'Assembler' computation, just producing the memory (or an error) and
-- ignoring the result.  The instruction stream starts at address @0@.
execAssembler :: (Integral p, Num w) => Assembler e p w a -> Either e [w]
execAssembler = runIdentity . execAssemblerT

-- |Throw a short-circuiting error immediately.  The first 'asmError' in an
-- 'Assembler' computation is the only one that will be seen, and any 'asmError'
-- will be seen instead of an 'asmDelayedError'.  Do not use with time-traveling
-- information (such as the result of 'reserve').
asmError :: MonadFix m => e -> AssemblerT e p w m a
asmError = AssemblerT . throwError

-- |Possibly register a delayed error.  If passed 'Nothing', no error is
-- reported.  If passed @'Just' err@, then the error @err@ is reported, but
-- execution does /not/ stop (hence the @'Assembler' ()@ return type, instead of
-- @'Assembler' a@).  Only the first 'asmDelayedError' is stored; however, any
-- 'asmError' (before or after) will supersede all 'asmDelayedError's.  This
-- function is safe to use with time-traveling information (such as the result
-- of 'reserve'); note that it does not require @m@ to be a 'MonadFix'.
asmDelayedError :: Monad m => Maybe e -> AssemblerT e p w m ()
asmDelayedError merr = AssemblerT . lift $ modify (<|> merr)

-- |The current address in the instruction stream (i.e., the end of it).  Useful
-- for jumps.
here :: MonadFix m => AssemblerT e p w m p
here = AssemblerT $ getsPast (^.currentInstruction)

-- |The current address of the start of the reserved data segment.
-- Time-traveling information from the future; be careful.
reservedSegment :: MonadFix m => AssemblerT e p w m p
reservedSegment = AssemblerT getFuture

-- |Write a word to the instruction stream, incrementing the current
-- instruction.  There's nothing about this function that mandates that the
-- written word must be an instruction, it's just the most common use.
asmWord :: (MonadFix m, Num p) => w -> AssemblerT e p w m ()
asmWord w = AssemblerT $
  tell [w] *> modifyForwards (currentInstruction +~ 1)

-- |Write a list of words to the instruction stream, incrementing the current
-- instruction by the length of the list.  There's nothing about this function
-- that mandates that the written words must be instructions, it's just the most
-- common use.
asmWords :: (MonadFix m, Num p) => [w] -> AssemblerT e p w m ()
asmWords ws = AssemblerT $
  tell ws *> modifyForwards (currentInstruction +~ genericLength ws)

-- |Reserve some number of words at the end of the reserved data stream,
-- returning the address of the first word reserved.  (If @0@ words are
-- reserved, then the address of the end of the reserved data stream is
-- returned.)  The reserved data will be all @0@s.  The return value is
-- time-traveling information from the future; be careful.  (The 'Ord'
-- constraint is required so that we can ensure we always reserve a nonnegative
-- number of words.)
reserve :: (MonadFix m, Num p, Ord p) => p -> AssemblerT e p w m p
reserve n = AssemblerT $ do
  dataAddr <- getFuture
  dataSize <- getsPast (^.reservedInstructions)
  modifyForwards $ reservedInstructions +~ max 0 n
  pure $ dataAddr + dataSize

-- |@program asm@ runs @asm@, and then completes the pending reservation:
-- it places the appropriate number of reserved @0@s at the end of the
-- instruction stream, advances the current instrunction past them, and sets the
-- number of currently-reserved instructions to @0@.  This allows separate
-- programs/functions/processes to be glued together, each with its own
-- directly-adjacent data segment.
program :: (MonadFix m, Integral p, Num w)
        => AssemblerT e p w m a -> AssemblerT e p w m a
program (AssemblerT asm) = AssemblerT $ mdo
  -- This code has to run the provided program @asm@ inside a "fresh" context,
  -- so that it can flush only its local reserved data segment.  Making the
  -- context fresh requires manipulating the state: saving the old value,
  -- updating the state, running @asm@, and restoring the old value.  The catch
  -- is that we must manipulate /two/ pieces of state:
  -- 
  --   1. The forward-traveling reserved instruction count
  --   2. The backward-traveling reserved address
  --
  -- (We don't modify the instruction address; that's not local.)  The first
  -- piece is saved, set, used, and then restored; the /second/ piece is
  -- restored, used, set, and then saved!

  -- First, stash and clear the reserved-data count and restore the outer
  -- reserved-data address.
  originallyReserved <- getsPast (^.reservedInstructions)
  modifyForwards $ reservedInstructions .~ 0
  sendPast currentReservedLocation
  
  -- Then, run the provided program in a context with its local reserved-data
  -- count (above) and address (below).  This ensures that it will only register
  -- its own requests for reserved data.
  result <- asm

  -- Now, actually reserve the data that @asm@ requested, and in doing so
  -- restore the outer reserved-data count
  cs <- getPast
  tell $ genericReplicate (cs^.reservedInstructions) 0
  sendFuture $ Counters (cs^.currentInstruction + cs^.reservedInstructions)
                        originallyReserved

  -- Finally, stash and set the reserved-data location
  sendPast $ cs^.currentInstruction
  currentReservedLocation <- getFuture
  
  -- Oh yeah, and return the result of running @asm@
  return result
