{-# LANGUAGE OverloadedStrings #-}

module Postprocess.FileStructure (
  splitPreambleImportsBody,
  partitionExtraPreambleImports,
  collectPreambleImportsBody
  ) where

import Control.Arrow
import Control.Applicative

import Data.Char
import Data.List

import           Data.Text (Text)
import qualified Data.Text as T

import Postprocess.Util.Tuple
import Postprocess.Util.Monoid

import Postprocess.Processor

-- Preamble: up to and including the `module` line
-- Imports: the imports (duh)
-- Body: the rest of the module
splitPreambleImportsBody :: Document -> (Document,Document,Document)
splitPreambleImportsBody =
      break ("module" `T.isPrefixOf`) >>> shift
  >>> second (span $ (||) <$> ("import" `T.isPrefixOf`) <*> T.all isSpace)
  >>> flat3
  where
    shift (pre,mid:post) = (pre ++ [mid], post)
    shift (pre,[])       = (pre,[])

partitionExtraPreambleImports :: Document -> (Document,Document,Document)
partitionExtraPreambleImports =
      partition ("{-#" `T.isPrefixOf`)
  >>> second (partition ("import" `T.isPrefixOf`))
  >>> flat3

collectPreambleImportsBody :: [Text] -> Document -> (Document,Document,Document)
collectPreambleImportsBody extraBody doc =
  let (filePre,  fileImp,  fileBody) = splitPreambleImportsBody doc
      (extraPre, extraImp, body)     = partitionExtraPreambleImports $ extraBody ?+++ fileBody
  in (extraPre ?+++ filePre, fileImp +++? extraImp, body)
