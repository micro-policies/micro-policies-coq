{-# LANGUAGE OverloadedStrings #-}

module Postprocess.Constraints (
  ExtraConstraint(..),
  parseConstraint, partitionConstraints, addConstraints
  ) where

import Control.Arrow
import Control.Monad
import Data.Monoid

import Data.Char
import Data.Maybe
import Data.Either

import           Data.Map (Map)
import qualified Data.Map as M

import           Data.Text      (Text)
import qualified Data.Text      as T
import qualified Data.Text.Read as T

import Postprocess.Util.List
import Postprocess.Util.Haskell

import Postprocess.Processor

data ExtraConstraint = ExtraConstraint { constraintName              :: Text
                                       , constraintTypeVariableIndex :: Integer }
                     deriving (Eq, Ord, Show, Read)

parseConstraint :: Text -> Maybe (Text,[ExtraConstraint])
parseConstraint line = do
  [val, conDesc] <-   map T.strip . T.splitOn "::"
                 <$> (T.stripPrefix "{-# POSTPROCESS CONSTRAINT"
                 =<<  T.stripSuffix "#-}" (T.strip line))
  constraints <- forM (map T.words $ T.splitOn "," conDesc) $ \conWords -> do
                   [constraint,tvIxStr] <- pure conWords
                   guard $ T.all isHaskellQualidChar constraint
                   case T.decimal tvIxStr of
                     Right (tvIx,"") -> pure $ ExtraConstraint constraint tvIx
                     _               -> mzero
  pure (val, constraints)

partitionConstraints :: Document -> (Document, Map Text [ExtraConstraint])
partitionConstraints = second M.fromList . partitionEithers
                     . map (\line -> maybe (Left line) Right $ parseConstraint line)

addConstraints :: Map Text [ExtraConstraint] -> Processor
addConstraints valConstraints = map $ \line -> fromMaybe line $ do
  [val, ty]  <- pure $ T.splitOn " :: " line
  guard . not $ "=>" `T.isInfixOf` ty
  let tvs = filter (maybe False (isLower . fst) . T.uncons)
          . T.words
          $ T.map (\c -> if isHaskellQualidChar c then c else ' ') ty
      constrain (ExtraConstraint c ix) = ((c <> " ") <>) <$> (tvs ?? ix)
  constraints <- mapM constrain =<< M.lookup val valConstraints
  pure $ T.concat [val, " :: (", T.intercalate ", " constraints, ") => ", ty]
