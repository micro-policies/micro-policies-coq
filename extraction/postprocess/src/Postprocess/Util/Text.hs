module Postprocess.Util.Text (replaceAll) where

import Data.Monoid

import Data.Maybe

import           Data.Text     (Text)
import           Data.Text.ICU (Regex)
import qualified Data.Text.ICU as ICU

replaceAll :: Regex -> Text -> Text -> Text
replaceAll needle replacement = go where
  go haystack = case ICU.find needle haystack of
    Just match -> fromJust (ICU.prefix 0 match)
               <> replacement
               <> go (fromJust (ICU.suffix 0 match))
    Nothing    -> haystack
