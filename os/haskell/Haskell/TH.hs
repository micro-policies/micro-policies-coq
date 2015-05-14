{-# LANGUAGE LambdaCase #-}
module Haskell.TH where

import Language.Haskell.TH

import Data.Data
import Data.Maybe
import Control.Applicative

import Haskell.Util

-- data Old = XA | YB Bad Int | XC Good Bad deriving (Eq, Ord)
-- retypeData ''Old "New" [(''Bad,''Good)] (dropWhile (== 'X')) [''Eq]
-- data New = A | YB Good Int | C Good Good deriving Eq

retypeData :: Name -> String
           -> [(Name,Name)] -> (String -> String)
           -> [Name]
           -> DecsQ
retypeData oldDataType newDataType replacements rename derivations = do
  let unqualify name = (<$> reify name) $ \case
        DataConI _ _ ty _ | ty == oldDataType ->
          mkName . rename $ nameBase name
        _ ->
          name
  TyConI (DataD [] _ [] ctors _) <- reify oldDataType
  ctors' <- gmapDeepM (fromMaybe <$> unqualify
                                 <*> fmap pure . (`lookup` replacements))
                      ctors
  return $ [DataD [] (mkName newDataType) [] ctors' derivations]

{-
-- The following TH makes the 'Coq_instr' type more informative by replacing the
-- plain old extracted 'Coq_reg' and 'Coq_imm' type synonyms with their very
-- strongly typed newtype equivalents 'Reg' and 'Imm'.
do TyConI (DataD [] _ [] ctors []) <- reify ''Coq_instr
   -- We (a) replace the extracted types with newtypes (or, for 'Coq_Binop',
   -- with a type synonym); and (b) unqualify the constructor names so we can
   -- bind them in our new type.
   ctors' <- flip gmapDeepM ctors $ \name ->
               if | name == ''Coq_binop -> return ''Binop
                  | name == ''Coq_reg   -> return ''Reg
                  | name == ''Coq_imm   -> return ''Imm
                  | otherwise           -> (<$> reify name) $ \case
                      DataConI _ _ ty _ | ty == ''Coq_instr -> mkName $ nameBase name
                      _ -> name
   return $ [DataD [] (mkName "Instr") [] ctors' [''Eq,''Ord,''Show]]
-}
