module Postprocess.Processor (
  Document, Processor, Scanner,
  run, runReplacingFile
  ) where

import Control.Applicative

import           Data.Text    (Text)
import qualified Data.Text    as T
import qualified Data.Text.IO as T

import System.Directory

type Document  = [Text]
type Processor = Document -> Document
type Scanner a = Document -> a

run :: Processor -> Text -> Text
run p = T.unlines . p . T.lines

runReplacingFile :: FilePath -> FilePath -> Processor -> IO ()
runReplacingFile from to p = do
  txt <- run p <$> T.readFile from
  -- The removal has to come after the read but before the write, so that we can
  -- overwrite a file in-place.
  removeFile from
  T.writeFile to txt
