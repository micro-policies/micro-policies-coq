{-# LANGUAGE LambdaCase #-}
module Haskell.TH where

import Language.Haskell.TH

import Data.Data
import Data.Maybe
import Data.Char

import Control.Applicative
import Control.Lens

import Unsafe.Coerce

import Haskell.Util

-- Given
--
-- > data Old = XA | YB Bad Int | XC Good Bad deriving (Eq, Ord)
--
-- running
--
-- > retypeData ''Old "New"
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

retypeData :: Name -> String
           -> [(Name,Name)] -> (String -> String)
           -> [Name]
           -> String -> String
           -> DecsQ
retypeData oldDataType newDataType replacements rename derivations toOld fromOld = do
  let unqualify name = (<$> reify name) $ \case
        DataConI _ _ ty _ | ty == oldDataType ->
          mkName . rename $ nameBase name
        _ ->
          name
  TyConI (DataD [] _ [] ctors _) <- reify oldDataType
  ctors' <- gmapDeepM (fromMaybe <$> unqualify
                                 <*> fmap pure . (`lookup` replacements))
                      ctors
  let newTypeD = [DataD [] (mkName newDataType) [] ctors' derivations]

  let mkCoercion name from to =
        [ SigD name $ ArrowT `AppT` ConT from `AppT` ConT to
        , FunD name [Clause [] (NormalB $ VarE 'unsafeCoerce) []] ]
      toOldD   = mkCoercion (mkName toOld)   (mkName newDataType) oldDataType
      fromOldD = mkCoercion (mkName fromOld) oldDataType (mkName newDataType)
  
  return $ newTypeD ++ toOldD ++ fromOldD
