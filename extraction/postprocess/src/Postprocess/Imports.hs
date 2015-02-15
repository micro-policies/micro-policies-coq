{-# LANGUAGE ViewPatterns, LambdaCase, OverloadedStrings #-}

module Postprocess.Imports (getImportedModules, getReferencedModules) where

import Data.Char
import Data.Maybe

import Language.Haskell.Exts.Parser (ParseResult(..))
import Language.Haskell.Exts.Lexer

import           Data.Set (Set)
import qualified Data.Set as S

import           Data.Text (Text)
import qualified Data.Text as T

import Postprocess.Processor

getImportedModules :: Scanner (Set Text)
getImportedModules =
  S.fromList . mapMaybe ( fmap (T.takeWhile (not . isSpace))
                        . fmap (dropOptToken "qualified")
                        . tryDropToken "import"
                        . dropSpaces )
  where
    dropSpaces = T.dropWhile isSpace
    -- Drops token + trailing space
    tryDropToken tok = fmap dropSpaces . T.stripPrefix tok
    dropOptToken tok = fromMaybe <*> tryDropToken tok

getReferencedModules :: Scanner (Set Text)
getReferencedModules (lexTokenStream . T.unpack . T.unlines -> ParseOk (map unLoc -> toks)) =
  S.fromList . flip mapMaybe toks $ fmap T.pack . \case
    QVarId  (m,_) -> Just m
    QConId  (m,_) -> Just m
    QVarSym (m,_) -> Just m
    QConSym (m,_) -> Just m
    _             -> Nothing
getReferencedModules _ =
  S.empty
