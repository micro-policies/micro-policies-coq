{-# LANGUAGE ViewPatterns, LambdaCase, OverloadedStrings #-}

import Control.Arrow
import Control.Applicative
import Control.Monad
import Data.Monoid

import Data.Char
import Data.Maybe
import Data.List

import Language.Haskell.Exts.Parser (ParseResult(..))
import Language.Haskell.Exts.Lexer

import           Data.Set (Set)
import qualified Data.Set as S

import           Data.Text    (Text)
import qualified Data.Text    as T
import qualified Data.Text.IO as T

import System.FilePath
import System.Directory
import System.Environment
import System.Exit

withBetween :: (a -> Bool) -> (a -> Bool) -> (a -> [a] -> a -> [a]) -> [a] -> [a]
withBetween start end f = findStart where
  findStart [] = []
  findStart (x:xs)
    | start x, Just (body, e, rest) <- findEnd xs
      = f x body e ++ findStart rest
    | otherwise
      = x : findStart xs

  findEnd (break end -> (body, e:rest)) = Just (body, e, rest)
  findEnd _                             = Nothing

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

-- Preamble: up to and including the `module` line
-- Imports: the imports (duh)
-- Body: the rest of the module
splitPreambleImportsBody :: Document -> (Document,Document,Document)
splitPreambleImportsBody =
      break ("module" `T.isPrefixOf`) >>> shift
  >>> second (span $ (||) <$> ("import" `T.isPrefixOf`) <*> T.all isSpace)
  >>> triple
  where
    shift (pre,mid:post) = (pre ++ [mid], post)
    shift (pre,[])       = (pre,[])
    
    triple (a,(b,c)) = (a,b,c)

deCPP :: Processor
deCPP =
  withBetween (== "#ifdef __GLASGOW_HASKELL__") (== "#endif") $ \_ text _ ->
    takeWhile (/= "#else") text

fixOptions :: Processor
fixOptions = concatMap $ fixGHC >=> fixHugs where
  fixGHC str | "{-# OPTIONS_GHC" `T.isPrefixOf` str =
                 do let ghc' = T.replace " -cpp " " " str
                    guard $ ghc' /= "{-# OPTIONS_GHC #-}"
                    return ghc'
             | otherwise =
                 [str]

  fixHugs str | "{- For Hugs" `T.isPrefixOf` str = []
              | otherwise                        = [str]

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

fixExtractedCode :: Processor
fixExtractedCode doc =
  let (pre, imps, body)  = splitPreambleImportsBody $ deCPP doc
      pre'               = fixOptions pre
      (extraImps, body') = partition ("import" `T.isPrefixOf`) body
      currentImps        = imps ++ "" : extraImps
      neededImps         = getReferencedModules body' S.\\ getImportedModules currentImps
      imps'              =  currentImps
                         ++ "" : map ("import qualified " <>) (S.toList neededImps) ++ [""]
  in pre' ++ imps' ++ body'

fixExtractedCodeDirectory :: FilePath -> FilePath -> IO ()
fixExtractedCodeDirectory from to =
  (getDirectoryContents from >>=) . (. filter (".hs" `isSuffixOf`)) . mapM_ $ \file -> do
    let fromFile = from </> file
        toFile   = to   </> file
    putStrLn $ "Cleaning file `" ++ fromFile ++ "' to `" ++ toFile ++ "'"
    runReplacingFile (from </> file) (to </> file) fixExtractedCode

test :: IO ()
test = T.putStr . run (take 30 . fixExtractedCode) =<< T.readFile "../ssrbool.hs"

printHelp :: IO ()
printHelp = do
  name <- getProgName
  putStrLn $ "Usage: " ++ name
  putStrLn $ "       " ++ name ++ " EXTRACTION-DIR"
  putStrLn $ "       " ++ name ++ " EXTRACTION-DIR TARGET-DIR"
  putStrLn $ "       " ++ name ++ " --help"
  putStrLn $ "       " ++ name ++ " -h"
  putStrLn ""
  putStrLn "Cleans up extracted Coq code for use with GHC by:"
  putStrLn "  (1) removing CPP;"
  putStrLn "  (2) fixing errors; and"
  putStrLn "  (3) inserting all necessary qualified module imports"
  putStrLn ""
  putStrLn "Without arguments, fixes Haskell code given on stdin and prints the result to"
  putStrLn "stdout."
  putStrLn ""
  putStrLn "With one non-help argument, fixes every .hs file in the given directory."
  putStrLn ""
  putStrLn "With two arguments, removes every `.hs' file in the first directory and creates"
  putStrLn "an identically-named fixed file in the second directory."
  putStrLn ""
  putStrLn "With `--help` or `-h`, or with more than two arguments, prints this help."

main :: IO ()
main = getArgs >>= \case
  ["--help"] -> printHelp
  ["-h"]     -> printHelp
  []         -> T.interact $ run fixExtractedCode
  [dir]      -> fixExtractedCodeDirectory dir  dir
  [from, to] -> fixExtractedCodeDirectory from to
  _          -> printHelp >> exitFailure
