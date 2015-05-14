module Haskell.Util where

import Control.Applicative
import Control.Monad
import Data.Maybe
import Data.Data
import Data.List

(??) :: (Eq i, Integral i) => [a] -> i -> Maybe a
[]     ?? _ = Nothing
(x:xs) ?? i = case i `compare` 0 of
                LT -> Nothing
                EQ -> Just x
                GT -> xs ?? (i-1)

-- showSigned   1  == "+1"
-- showSigned   0  == "0"
-- showSigned (-1) == "-1"
showSigned :: (Num a, Ord a, Show a) => a -> String
showSigned x | x > 0     = '+' : show x
             | otherwise = show x

gmapDeepT :: (Typeable a, Data b) => (a -> a) -> b -> b
gmapDeepT f = gmapT $ fromMaybe <$> gmapDeepT f <*> (cast . f <=< cast)

gmapDeepM :: (Typeable a, Data b, Monad m) => (a -> m a) -> b -> m b
gmapDeepM f = gmapM $ fromMaybe <$$> gmapDeepM f <**> use f where
  use f = maybe (return Nothing) (liftM cast) . fmap f . cast
  
  (<$$>) :: (Functor f, Monad g) => (a -> b) -> f (g a) -> f (g b)
  (<$$>) = fmap . liftM
  infixl 4 <$$>

  (<**>) :: (Applicative f, Monad g) => f (g (a -> b)) -> f (g a) -> f (g b)
  (<**>) = liftA2 ap
  infixl 4 <**>

data Alignment = AlignLeft
               | AlignRight
               deriving (Eq, Ord, Enum, Bounded, Show, Read)
               -- AlignCenter is too hard :-)

-- `pad' and friends require finite lengths
pad :: Integral i => Alignment -> a -> i -> [a] -> [a]
pad a p n xs = let ps = genericReplicate (n - genericLength xs) p
               in case a of
                    AlignLeft  -> xs ++ ps
                    AlignRight -> ps ++ xs

padToMatch :: Alignment -> a -> [[a]] -> [[a]]
padToMatch a p xss = map (pad a p . maximum $ 0 : map length xss) xss

alignColumns :: [(Alignment,a)] -> [[[a]]] -> [[[a]]]
alignColumns alignments table =
  transpose . zipWith (uncurry padToMatch) alignments $ transpose table
