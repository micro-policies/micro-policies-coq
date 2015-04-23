{-# LANGUAGE ViewPatterns #-}

module Postprocess.Util.List (withBetween, (??)) where

withBetween :: (a -> Bool) -> (a -> Bool) -> (a -> [a] -> a -> [a]) -> [a] -> [a]
withBetween start end f = findStart where
  findStart [] = []
  findStart (x:xs)
    | start x
      = case findEnd xs of
          Just (body, e, rest) -> f x body e ++ findStart rest
          Nothing              -> x : xs
    | otherwise
      = x : findStart xs

  findEnd (break end -> (body, e:rest)) = Just (body, e, rest)
  findEnd _                             = Nothing

(??) :: (Eq i, Integral i) => [a] -> i -> Maybe a
[]     ?? _ = Nothing
(x:xs) ?? i = case i `compare` 0 of
                LT -> Nothing
                EQ -> Just x
                GT -> xs ?? (i-1)
