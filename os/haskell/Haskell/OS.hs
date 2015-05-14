{-# LANGUAGE BangPatterns #-}
module Haskell.OS where

import Haskell.Machine
import Os

stepMany' :: Integral i => i -> State -> (i, State)
stepMany' = go 0 where
  go !k n s | n <= 0    = (k,s)
            | otherwise = maybe (k,s) (go (k+1) (n-1)) $ step_os s

stepMany :: Integral i => i -> State -> Maybe State
stepMany n s | n <= 0    = return s
             | otherwise = stepMany (n-1) =<< step_os s

os0 :: State
os0 = symbolic_os

stepOS' :: Integral i => i -> (i, State)
stepOS' = flip stepMany' os0

stepOS :: Integral i => i -> Maybe State
stepOS = flip stepMany os0
