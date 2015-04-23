module Postprocess.Util.Haskell (isHaskellQualidChar) where

import Data.Char

isHaskellQualidChar :: Char -> Bool
isHaskellQualidChar c = isAlphaNum c || c == '_' || c == '\'' || c == '.'
