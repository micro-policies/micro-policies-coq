{-# LANGUAGE OverloadedStrings #-}

module Postprocess (fixExtractedCode, fixExtractedCodeDirectory) where

import Control.Applicative
import Control.Monad
import Data.Monoid

import Data.Char
import Data.List

import qualified Data.Set as S

import           Data.Text    (Text)
import qualified Data.Text    as T
import qualified Data.Text.IO as T

import System.FilePath
import System.Directory

import Postprocess.Util.Monoid

import Postprocess.Processor
import Postprocess.FileStructure
import Postprocess.Imports
import Postprocess.Constraints
import Postprocess.Clean

fixExtractedCode :: Maybe Text -> [Text] -> Processor
fixExtractedCode thisModule extraBody doc =
  let (pre, imps, body)  = collectPreambleImportsBody extraBody . changeReservedWords $ deCPP doc
      (pre',constraints) = partitionConstraints $ "{-# OPTIONS_GHC -w #-}" : fixOptions pre
      body'              = addConstraints constraints body
      neededImps         = maybe id S.delete thisModule $ getReferencedModules body' S.\\ getImportedModules imps
      imps'              = imps ++?? map ("import qualified " <>) (S.toList neededImps)
  in pre' ++ imps' ++ body'

fixExtractedCodeDirectory :: FilePath -> FilePath -> Maybe FilePath -> IO ()
fixExtractedCodeDirectory from to mExtra = do
  hsFiles <- filter (".hs" `isSuffixOf`) <$> getDirectoryContents from
  createDirectoryIfMissing True to
  forM_ hsFiles $ \file -> do
    let fromFile   = from </> file
        toFile     = to   </> case file of c : cs -> toUpper c : cs ; "" -> ""
        moduleName = T.pack $ takeBaseName toFile
    putStrLn $ "Processing file `" ++ fromFile ++ "' to `" ++ toFile ++ "'"
    extra <- case mExtra of
      Just extra -> do let extraFile = extra </> file
                       exists <- doesFileExist $ extra </> file
                       if exists
                         then T.lines <$> T.readFile extraFile
                         else pure []
      Nothing    -> pure []
    runReplacingFile fromFile toFile $ fixExtractedCode (Just moduleName) extra
