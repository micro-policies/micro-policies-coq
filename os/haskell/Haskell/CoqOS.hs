{-# LANGUAGE BangPatterns #-}
module Haskell.CoqOS where

import Haskell.Machine
import Os

stepMany' :: Integral i => i -> CoqState -> (i, CoqState)
stepMany' = go 0 where
  go !k n s | n <= 0    = (k,s)
            | otherwise = maybe (k,s) (go (k+1) (n-1)) $ step_os s

stepMany :: Integral i => i -> CoqState -> Maybe CoqState
stepMany n s | n <= 0    = return s
             | otherwise = stepMany (n-1) =<< step_os s

os0 :: CoqState
os0 = symbolic_os

stepOS' :: Integral i => i -> (i, CoqState)
stepOS' = flip stepMany' os0

stepOS :: Integral i => i -> Maybe CoqState
stepOS = flip stepMany os0
