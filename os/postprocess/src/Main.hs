{-# LANGUAGE LambdaCase, OverloadedStrings #-}

module Main (printHelp, main) where

import Control.Applicative
import Data.Monoid

import qualified Data.Text    as T
import qualified Data.Text.IO as T

import System.Environment
import System.Exit

import Postprocess.Processor
import Postprocess

printHelp :: IO ()
printHelp = do
  name <- T.pack <$> getProgName
  T.putStrLn $ "Usage: " <> name
  T.putStrLn $ "       " <> name <> " EXTRACTION-DIR"
  T.putStrLn $ "       " <> name <> " EXTRACTION-DIR TARGET-DIR"
  T.putStrLn $ "       " <> name <> " EXTRACTION-DIR TARGET-DIR EXTRA-DIR"
  T.putStrLn $ "       " <> name <> " --help"
  T.putStrLn $ "       " <> name <> " -h"
  T.putStrLn ""
  T.putStrLn "Cleans up extracted Coq code for use with GHC by:"
  T.putStrLn "  (1) Removing CPP and Hugs references."
  T.putStrLn "  (2) Fixing errors (misplaced imports and variables with illegal names)."
  T.putStrLn "  (3) Inserting all necessary qualified module imports."
  T.putStrLn "  (4) Optionally, inserting arbitrary extra code."
  T.putStrLn "  (5) Optionally, inserting extra constraints into type signatures."
  T.putStrLn ""
  T.putStrLn "Without arguments, fixes Haskell code given on stdin and prints the result to"
  T.putStrLn "stdout."
  T.putStrLn ""
  T.putStrLn "With one non-help argument, fixes every .hs file in the given directory,"
  T.putStrLn "including uppercasing the first letter of the filename."
  T.putStrLn ""
  T.putStrLn "With two arguments, removes every `.hs' file in the first directory and creates"
  T.putStrLn "an identically-named (modulo case) fixed file in the second directory."
  T.putStrLn ""
  T.putStrLn "With three arguments, operates as with two arguments, except extra code may be"
  T.putStrLn "added to each file by looking in the extra directory for `.hs' files with the"
  T.putStrLn "same name as the source."
  T.putStrLn ""
  T.putStrLn "If this extra code (or the generated code, hypothetically) contains pragmas of"
  T.putStrLn "the form `{-# POSTPROCESS CONSTRAINT val :: con1 tv1, con2 tv2, ... #-}', then"
  T.putStrLn "these pragmas are removed; instead, the value `val', if defined in the file, has"
  T.putStrLn "the various `conN tvN` constraints prepended to its type signature.  The `conN'"
  T.putStrLn "must be individual Haskell names (probably qualified); the `tvN' must be"
  T.putStrLn "unsigned integers that specify the (0-based, left-to-right) index of the type"
  T.putStrLn "variable to constrain.  Thus, `val :: (a -> b) -> a' with the pragma"
  T.putStrLn "`{-# POSTPROCESS CONSTRAINT val :: Eq 0, Ord 1 #-}' will become"
  T.putStrLn "`val :: (Eq a, Ord b) => (a -> b) -> a'.  Note that type variables referenced on"
  T.putStrLn "lines after the `::' will not be found.  Malformed pragmas are silently passed"
  T.putStrLn "through to the cleaned-up code; invalid type variable indices will cause the"
  T.putStrLn "pragma to silently not be applied."
  T.putStrLn ""
  T.putStrLn "With `--help` or `-h`, or with more than three arguments, prints this help."

main :: IO ()
main = getArgs >>= \case
  ["--help"]        -> printHelp
  ["-h"]            -> printHelp
  []                -> T.interact . run $ fixExtractedCode Nothing []
  [dir]             -> fixExtractedCodeDirectory dir  dir Nothing
  [from, to]        -> fixExtractedCodeDirectory from to  Nothing
  [from, to, extra] -> fixExtractedCodeDirectory from to  (Just extra)
  _                 -> printHelp >> exitFailure
