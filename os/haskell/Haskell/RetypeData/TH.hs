{-# LANGUAGE LambdaCase, TemplateHaskell #-}
module Haskell.RetypeData.TH (retypeData) where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

import Data.Data
import Data.Maybe

import Control.Applicative

import Unsafe.Coerce

import Haskell.Util

-- Given
--
-- > data Old = XA | YB Bad Int | XC Good Bad deriving (Eq, Ord)
--
-- running
--
-- > retypeData ''Old "New"
-- >            Nothing
-- >            [(''Bad,''Good)]
-- >            (dropWhile (== 'X'))
-- >            [''Eq]
-- >            "olden" "newen"
--
-- produces
--
-- > data New = A | YB Good Int | C Good Good deriving Eq
-- >
-- > olden :: New -> Old
-- > olden = unsafeCoerce
-- >
-- > newen :: Old -> New
-- > newen = unsafeCoerce
--
-- We can also produce records.  Given
--
-- > data Old = XRec Good Int Bad deriving (Eq, Ord)
--
-- running
--
-- > retypeData ''Old "New"
-- >            (Just ["good", "int", "bad"])
-- >            [(''Bad,''Good)]
-- >            (dropWhile (== 'X'))
-- >            [''Eq]
-- >            "olden" "newen"
--
-- produces
--
-- > data New = Rec {good :: Good, int :: Int, bad :: Bad} deriving Eq
-- >
-- > olden :: New -> Old
-- > olden = unsafeCoerce
-- >
-- > newen :: Old -> New
-- > newen = unsafeCoerce

retypeData :: Name -> String -> Maybe [String]
           -> [(Name,Name)] -> (String -> String)
           -> [Name]
           -> String -> String
           -> DecsQ
retypeData oldDataType newDataType fieldNames
           replacements rename
           derivations
           toOld fromOld = do
  let unqualify name = (<$> reify name) $ \case
        DataConI _ _ ty _ | ty == oldDataType ->
          mkName . rename $ nameBase name
        _ ->
          name
  TyConI (DataD [] _ [] ctors _) <- reify oldDataType
  ctors' <-  gmapDeepM (fromMaybe <$> unqualify
                                  <*> fmap pure . (`lookup` replacements))
                       ctors
         >>= maybe pure convert_to_record fieldNames
  let newTypeD = [DataD [] (mkName newDataType) [] ctors' derivations]

  let mkCoercion name from to =
        [ SigD name $ ArrowT `AppT` ConT from `AppT` ConT to
        , FunD name [Clause [] (NormalB $ VarE 'unsafeCoerce) []] ]
      toOldD   = mkCoercion (mkName toOld)   (mkName newDataType) oldDataType
      fromOldD = mkCoercion (mkName fromOld) oldDataType (mkName newDataType)
  
  return $ newTypeD ++ toOldD ++ fromOldD

convert_to_record :: [String] -> [Con] -> Q [Con]
convert_to_record fieldNames [NormalC name strictTys] = do
  fields <- add_field_names fieldNames strictTys
  pure [RecC name fields]
convert_to_record _ _ =
  fail $  "retypeDataAsRecord: Cannot process data types unless they have "
       ++ "exactly one ordinary (non-infix, non-record, non-existential) "
       ++ "constructor"

add_field_names :: [String] -> [StrictType] -> Q [VarStrictType]
add_field_names []     []          =
  pure []
add_field_names (f:fs) ((s,t):sts) =
  ((mkName f,s,t) :) <$> add_field_names fs sts
add_field_names (_:_)  []          =
  fail "retypeDataAsRecord: Too many field names"
add_field_names []     (_:_)       =
  fail "retypeDataAsRecord: Not enough field names"
