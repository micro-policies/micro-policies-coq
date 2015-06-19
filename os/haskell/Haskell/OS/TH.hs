{-# LANGUAGE LambdaCase, TemplateHaskell #-}
module Haskell.OS.TH where

import Control.Applicative
import Control.Monad
import Control.Monad.Reader (MonadReader())
import Control.Lens
import Data.Char
import Data.List.Lens
import Language.Haskell.TH

-- |@recordFields \'\'Foo@ with the data declaration
-- @data Foo = Bar { baz :: Baz, quux :: Quux }@ evaluates to
-- @[("baz",[t|Baz|]), ("quux", [t|Quux|])]@.  @recordFields@ ignores strictness
-- and is careless about type variables.
recordFields :: Name -> Q [(String,Type)]
recordFields = reify >=> \case
  TyConI dec -> pure $ recordFieldsDec dec
  _          -> fail "recordFields: Expected type constructor name"

-- "Borrowed" from Control.Lens.Internal.FieldTH.makeFieldOpticsForDec
recordFieldsDec :: Dec -> [(String,Type)]
recordFieldsDec dec = case dec of
  DataD        _cxt _ty _tvs   cons _deriving ->
    extractFields cons
  NewtypeD     _cxt _ty _tvs   con  _deriving ->
    extractFields [con]
  DataInstD    _cxt _ty _targs cons _deriving ->
    extractFields cons
  NewtypeInstD _cxt _ty _targs con  _deriving ->
    extractFields [con]
  _ -> fail "recordFieldsDec: Expected data or newtype type-constructor"
  where
  extractFields [RecC _name fields] =
    [(nameBase field, ty) | (field,_,ty) <- fields]
  extractFields [_] =
    fail "recordFieldsDec: Expected a (non-quantified) record constructor"
  extractFields [] =
    fail "recordFieldsDec: No constructors in type declaration"
  extractFields _  =
    fail "recordFieldsDec: Too many constructors in type declaration"

-- |@makeMonadicAccessors ''Foo@ with the data declaration
-- @data Foo = Bar { _bazVal :: Baz, _quuxVal :: Quux }@ in scope produces the
-- declarations
--
-- @
--     baz :: (HasBar p, MonadReader p m) => m Baz
--     baz = view bazVal
--     
--     quux :: (HasBar p, MonadReader p m) => m Quux
--     quux = view quuxVal
-- @
--
-- Note the requirement for the @_fieldVal@ syntax -- the @_@ is optional, but
-- the @Val@ is mandatory.
makeMonadicAccessors :: Name -> DecsQ
makeMonadicAccessors tyName = do
  let assertName lookupName nameStr =
        maybe (fail $  "makeMonadicAccessors: Could not find `"
                    ++ nameStr ++ "'")
              pure
          =<< lookupName nameStr
  
  hasClass <- assertName lookupTypeName$ "Has" ++ nameBase tyName
  fields   <- recordFields tyName
  
  let makeMonadicAccessor (fieldName, fieldTy) = do
        let lensName = dropWhile (== '_') fieldName & _head %~ toLower
        lens     <- assertName lookupValueName lensName
        accessor <- case stripSuffix "Val" lensName of
                      Just accessorName ->
                        pure $ mkName accessorName
                      Nothing ->
                        fail $  "makeMonadicAccessors: "
                             ++ "Could not make accessor name for `"
                             ++ fieldName ++ "'"
        
        let accessorType =
              let pName = mkName "p"
                  p     = VarT pName
                  mName = mkName "m"
                  m     = VarT mName
              in ForallT [PlainTV pName, PlainTV mName]
                         [ ClassP hasClass      [p]
                         , ClassP ''MonadReader [p,m] ]
                         (m `AppT` fieldTy)
        (SigD accessor accessorType :) <$>
          [d|$(varP accessor) = view $(varE lens)|]
  concat <$> mapM makeMonadicAccessor fields
