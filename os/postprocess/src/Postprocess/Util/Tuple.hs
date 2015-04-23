module Postprocess.Util.Tuple (flat3, first3, second3, third3) where

flat3 :: (a,(b,c)) -> (a,b,c)
flat3 (a,(b,c)) = (a,b,c)

first3 :: (a -> a') -> (a,b,c) -> (a',b,c)
first3 f = \(a,b,c) -> (f a, b, c)

second3 :: (b -> b') -> (a,b,c) -> (a,b',c)
second3 f = \(a,b,c) -> (a, f b, c)

third3 :: (c -> c') -> (a,b,c) -> (a,b,c')
third3 f = \(a,b,c) -> (a, b, f c)
