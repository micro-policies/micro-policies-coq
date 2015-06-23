{-|
Module      : Haskell.ImplicitEffects
Description : Type class for implicitly `pure`ing
Copyright   : © 2015 Antal Spector-Zabusky
License     : BSD3
Maintainer  : Antal Spector-Zabusky <antal.b.sz@gmail.com>
Stability   : experimental
Portability : GHC only

This module provides a type class '(~!)' such that @a ~! f b@ means that @a@ can
be injected into @f b@.  There are two ways this can happen: either @a ~ b@ and
@f@ is 'Applicative'; or @a ~ f b@.  As long as things aren't too polymorphic,
'effectful' will be able to handle this implicitly, using 'pure' in the former
case and doing nothing in the latter.

The big win for this type class is in APIs: this way, a function @f@ can have
the type, say, @(c ~! 'IO' 'Char') => c -> IO String@, and be called as /either/
@f 'a'@ /or/ @f (readLn :: IO Char)@.
-}

{-# LANGUAGE TypeOperators, MultiParamTypeClasses, TypeFamilies, FlexibleInstances #-}
module Haskell.ImplicitEffects (
  (~!)(..),
  withEffectful1, withEffectful2, withEffectful3, withEffectful4, withEffectful5,
  liftEffectful1, liftEffectful2, liftEffectful3, liftEffectful4, liftEffectful5,
  bindEffectful1, bindEffectful2, bindEffectful3, bindEffectful4, bindEffectful5
  ) where

import Control.Applicative
import Haskell.Util (liftA4, liftA5, bind1, bind2, bind3, bind4, bind5)

-- |@(~!)@ is the class for implicit effectful lifting: @a ~! b@ means that @a@
-- can be effectfully interprented as a @b@.  The @~@ is for the equality-ish
-- aspect; the @!@ is for effectfulness.  /Do not instantiate this class./
class a ~! b where
  -- |Inject an @a@ into an effectful @b@.  Like 'pure', but it might not do
  -- anything.
  effectful :: a -> b

-- |The instance that actually supplies effects.  We can't use the equality
-- trick (see the other instance below), since if our two instances of @~!@ are
-- @a ~! f a'@ and @f a ~! f' a'@, things are overlapping.
instance Applicative f => a ~! f a where
  effectful = pure

-- |The instance that does nothing if there are already effects.
-- We need to use the equality constraints to force GHC to /commit/.  Suppose
-- GHC finds 'effectful' at type @g x -> g' x@.  With the equality in the
-- context, this will force GHC to conclude that @g ~ g'@, and type checking
-- will finish; if we instead had an instance @f a ~! f a@, GHC would worry that
-- we might also have an instance like @Maybe x -> IO x@, and so will complain
-- that things are ambiguous.
instance (f ~ f', a ~ a') => f a ~! f' a' where
  effectful = id

-- |Changes a function that takes 1 effectful argument (@f a@) into a function
-- that takes 1 implicitly-effectful argument (@a@ or @f a@).
withEffectful1 :: (a ~! b) => (b -> r) -> (a -> r)
withEffectful1 = (. effectful)

-- |Changes a function that takes 2 effectful arguments (@f a@) into a function
-- that takes 2 implicitly-effectful arguments (@a@ or @f a@).
withEffectful2 :: (a1 ~! b1, a2 ~! b2) => (b1 -> b2 -> r) -> a1 -> a2 -> r
withEffectful2 f a1 a2 = f (effectful a1) (effectful a2)

-- |Changes a function that takes 3 effectful arguments (@f a@) into a function
-- that takes 3 implicitly-effectful arguments (@a@ or @f a@).
withEffectful3 :: (a1 ~! b1, a2 ~! b2, a3 ~! b3) => (b1 -> b2 -> b3 -> r) -> a1 -> a2 -> a3 -> r
withEffectful3 f a1 a2 a3 = f (effectful a1) (effectful a2) (effectful a3)

-- |Changes a function that takes 4 effectful arguments (@f a@) into a function
-- that takes 4 implicitly-effectful arguments (@a@ or @f a@).
withEffectful4 :: (a1 ~! b1, a2 ~! b2, a3 ~! b3, a4 ~! b4) => (b1 -> b2 -> b3 -> b4 -> r) -> a1 -> a2 -> a3 -> a4 -> r
withEffectful4 f a1 a2 a3 a4 = f (effectful a1) (effectful a2) (effectful a3) (effectful a4)

-- |Changes a function that takes 5 effectful arguments (@f a@) into a function
-- that takes 5 implicitly-effectful arguments (@a@ or @f a@).
withEffectful5 :: (a1 ~! b1, a2 ~! b2, a3 ~! b3, a4 ~! b4, a5 ~! b5) => (b1 -> b2 -> b3 -> b4 -> b5 -> r) -> a1 -> a2 -> a3 -> a4 -> a5 -> r
withEffectful5 f a1 a2 a3 a4 a5 = f (effectful a1) (effectful a2) (effectful a3) (effectful a4) (effectful a5)

-- |Changes a function that takes 1 pure argument (@a@) and has a pure result
-- (@r@) into a function that takes 1 implicitly-effectful argument (@a@ or
-- @f a@) and has an effectful result (@f r@).
liftEffectful1 :: Applicative f => (a' ~! f a) => (a -> r) -> (a' -> f r)
liftEffectful1 = withEffectful1 . liftA

-- |Changes a function that takes 2 pure arguments (@a@) and has a pure result
-- (@r@) into a function that takes 2 implicitly-effectful arguments (@a@ or
-- @f a@) and has an effectful result (@f r@).
liftEffectful2 :: Applicative f => (a1' ~! f a1, a2' ~! f a2) => (a1 -> a2 -> r) -> (a1' -> a2' -> f r)
liftEffectful2 = withEffectful2 . liftA2

-- |Changes a function that takes 3 pure arguments (@a@) and has a pure result
-- (@r@) into a function that takes 3 implicitly-effectful arguments (@a@ or
-- @f a@) and has an effectful result (@f r@).
liftEffectful3 :: Applicative f => (a1' ~! f a1, a2' ~! f a2, a3' ~! f a3) => (a1 -> a2 -> a3 -> r) -> a1' -> a2' -> a3' -> f r
liftEffectful3 = withEffectful3 . liftA3

-- |Changes a function that takes 4 pure arguments (@a@) and has a pure result
-- (@r@) into a function that takes 4 implicitly-effectful arguments (@a@ or
-- @f a@) and has an effectful result (@f r@).
liftEffectful4 :: Applicative f => (a1' ~! f a1, a2' ~! f a2, a3' ~! f a3, a4' ~! f a4) => (a1 -> a2 -> a3 -> a4 -> r) -> a1' -> a2' -> a3' -> a4' -> f r
liftEffectful4 = withEffectful4 . liftA4

-- |Changes a function that takes 5 pure arguments (@a@) and has a pure result
-- (@r@) into a function that takes 5 implicitly-effectful arguments (@a@ or
-- @f a@) and has an effectful result (@f r@).
liftEffectful5 :: Applicative f => (a1' ~! f a1, a2' ~! f a2, a3' ~! f a3, a4' ~! f a4, a5' ~! f a5) => (a1 -> a2 -> a3 -> a4 -> a5 -> r) -> a1' -> a2' -> a3' -> a4' -> a5' -> f r
liftEffectful5 = withEffectful5 . liftA5

-- |Changes a function that takes 1 pure argument (@a@) and has an effectful
-- result (@m r@) into a function that takes 1 implicitly-effectful argument
-- (@a@ or @m a@) and has an effectful result (@m r@).
bindEffectful1 :: Monad m => (a' ~! m a) => (a -> m r) -> (a' -> m r)
bindEffectful1 = withEffectful1 . bind1

-- |Changes a function that takes 2 pure arguments (@a@) and has an effectful
-- result (@m r@) into a function that takes 2 implicitly-effectful arguments
-- (@a@ or @m a@) and has an effectful result (@m r@).
bindEffectful2 :: Monad m => (a1' ~! m a1, a2' ~! m a2) => (a1 -> a2 -> m r) -> (a1' -> a2' -> m r)
bindEffectful2 = withEffectful2 . bind2

-- |Changes a function that takes 3 pure arguments (@a@) and has an effectful
-- result (@m r@) into a function that takes 3 implicitly-effectful arguments
-- (@a@ or @m a@) and has an effectful result (@m r@).
bindEffectful3 :: Monad m => (a1' ~! m a1, a2' ~! m a2, a3' ~! m a3) => (a1 -> a2 -> a3 -> m r) -> a1' -> a2' -> a3' -> m r
bindEffectful3 = withEffectful3 . bind3

-- |Changes a function that takes 4 pure arguments (@a@) and has an effectful
-- result (@m r@) into a function that takes 4 implicitly-effectful arguments
-- (@a@ or @m a@) and has an effectful result (@m r@).
bindEffectful4 :: Monad m => (a1' ~! m a1, a2' ~! m a2, a3' ~! m a3, a4' ~! m a4) => (a1 -> a2 -> a3 -> a4 -> m r) -> a1' -> a2' -> a3' -> a4' -> m r
bindEffectful4 = withEffectful4 . bind4

-- |Changes a function that takes 5 pure arguments (@a@) and has an effectful
-- result (@m r@) into a function that takes 5 implicitly-effectful arguments
-- (@a@ or @m a@) and has an effectful result (@m r@).
bindEffectful5 :: Monad m => (a1' ~! m a1, a2' ~! m a2, a3' ~! m a3, a4' ~! m a4, a5' ~! m a5) => (a1 -> a2 -> a3 -> a4 -> a5 -> m r) -> a1' -> a2' -> a3' -> a4' -> a5' -> m r
bindEffectful5 = withEffectful5 . bind5
