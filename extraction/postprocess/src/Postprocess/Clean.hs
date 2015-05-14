{-# LANGUAGE OverloadedStrings #-}

module Postprocess.Clean (deCPP, changeReservedWords, fixOptions) where

import Control.Monad
import Data.Monoid

import qualified Data.Text as T

import qualified Data.Text.ICU as ICU

import Postprocess.Util.List
import Postprocess.Util.Text

import Postprocess.Processor

deCPP :: Processor
deCPP =
  withBetween (== "#ifdef __GLASGOW_HASKELL__") (== "#endif") $ \_ text _ ->
    takeWhile (/= "#else") text

changeReservedWords :: Processor
changeReservedWords = map (unreserve $ ["rec", "mdo", "proc", "pattern"]) where
  unreserve = foldr (.) id . map word
  word w = replaceAll (ICU.regex [ ICU.Multiline
                                 , ICU.UnicodeWord]
                                 $ "\\b" <> w <> "\\b")
                      ("reserved_word_" <> w)

fixOptions :: Processor
fixOptions = concatMap $ fixGHC >=> fixHugs where
  fixGHC str | "{-# OPTIONS_GHC" `T.isPrefixOf` str =
                 do let ghc' = T.replace " -cpp " " " str
                    guard $ ghc' /= "{-# OPTIONS_GHC #-}"
                    return $ T.replace "#-}" "-w #-}" ghc'
             | otherwise =
                 [str]

  fixHugs str | "{- For Hugs" `T.isPrefixOf` str = []
              | otherwise                        = [str]
