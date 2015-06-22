{-|
Module      : Haskell.ImplicitEffects.QQ
Description : Quasiquoter for adding implicit effects ('(~!)') to function types
Copyright   : © 2015 Antal Spector-Zabusky
License     : BSD3
Maintainer  : Antal Spector-Zabusky <antal.b.sz@gmail.com>
Stability   : experimental
Portability : GHC only

This module provides a type quasiquoter 'eff' such that

@
    [eff|(Monad m, Show a) => Bool -> !Int -> !a -> !(f Char) -> m ()|]
@

becomes

@
    forall m a f i1 a'2 fc3 .
      (Monad m, Show a, i1 ~! m Int, a'2 ~! m a, fc3 ~! m (f Char)) =>
      Bool -> i1 -> a'2 -> fc3 -> m ()
@

See why we want a quasiquoter?

Here's how 'eff' works.  The type is mostly left unchanged.  Any type @t@ prefixed
with @!@ is potentially effectful, and will be replaced with a fresh type
variable @v@ such that @v ~! m t@.  This means that @v@ is strictly more general
than the old @t@, having the option to be effectful.  The effect is guessed to
be the "terminating" effect type, i.e., the monad/applicative functor/whatever
the result is in -- if the type is of the form @a1 -> a2 -> ... -> aN -> m b@
(where @N@ may be @0@!), then the effect type is @m@.

The generated variables are named based on the type they're replacing, plus a
globally-incrememnting unique counter.  There are some heuristics packed into
'abbreviateType', which should mostly give not-terrible results.  Not
necessarily great, but not terrible.
-}

{-# LANGUAGE ViewPatterns, LambdaCase, TemplateHaskell, UnboxedTuples #-}
module Haskell.ImplicitEffects.QQ
       (eff, effHSEType, effString, abbreviateType)
       where

import Control.Applicative
import qualified Data.Foldable as F
import Data.Monoid

import Data.Maybe
import Data.List
import Data.Char

import Data.Set (Set)
import qualified Data.Set as S

import Control.Monad.RWS

import Language.Haskell.TH.Quote
import Language.Haskell.TH
import qualified Language.Haskell.TH as TH
import Language.Haskell.Exts
import qualified Language.Haskell.Exts as HS

import Data.Constraint (Constraint())

import Haskell.ImplicitEffects

-- |A type quasiquoter for generating implicitly effectful parameters.
eff :: QuasiQuoter
eff = QuasiQuoter { quoteExp  = unsupported "expression"
                  , quotePat  = unsupported "pattern"
                  , quoteType = effString
                  , quoteDec  = unsupported "declaration" }
  where
    unsupported loc _ =
      fail $ "eff: Can't use this quasiquoter in " ++ loc ++ " context, only in types"

--------------------------------------------------------------------------------

type Build = RWST (Set TH.Name)          -- Bound type variables
                  ( [TH.Name]            -- Free type variables
                  , [(TH.Name,TH.Type)]) -- Implicitly-effectful type variables
                  Integer                -- Fresh ID
                  Q
  -- We use lists instead of sets and maps in the writer component because we
  -- care about order; the list of free type variables will be small enough that
  -- 'nub' isn't painful.

with_bound :: Set TH.Name -> Build a -> Build a
with_bound s = local (s <>)

report_free :: TH.Name -> Build ()
report_free n = tell ([n], mempty)

bind_effectful :: TH.Name -> TH.Type -> Build ()
bind_effectful n t = tell (mempty, [(n,t)])

fresh_id :: Build Integer
fresh_id = get <* modify (+ 1)

--------------------------------------------------------------------------------

-- |The core of 'eff'; exposed in case it can be reused.
effHSEType :: HS.Type -> Q TH.Type
effHSEType ty = do
  (ty', (nub -> free, effected)) <- evalRWST (go_type ty) S.empty 1
  effect <- maybe (fail "eff: Could not guess effect type") pure $ guess_effect ty'
  let tvs = map PlainTV $ free ++ map fst effected
      aps = map (\(n,t) -> ClassP ''(~!) [VarT n, effect `AppT` t]) effected
  pure $ case ty' of
    ForallT binders cxt inner -> ForallT (binders ++ tvs) (cxt ++ aps) inner
    _                         -> ForallT tvs              aps          ty'

-- |The core of 'eff' with some parsing; exposed in case it can be reused.
effString :: String -> Q TH.Type
effString str =
  case parseWithMode
         defaultParseMode{ extensions = map EnableExtension
                                            [ TypeOperators
                                            , FlexibleContexts
                                            , MultiParamTypeClasses
                                            , RankNTypes
                                            , TypeFamilies
                                            , KindSignatures
                                            , ConstraintKinds
                                            , DataKinds
                                            , PolyKinds
                                            , UnicodeSyntax
                                            , MagicHash
                                              -- These last few are for error messages
                                            , TemplateHaskell
                                            , ImplicitParams ]
                                      ++ extensions defaultParseMode }
         str
  of
    ParseOk     ty    -> effHSEType ty
    ParseFailed _ err -> fail $ "eff: " ++ err

--------------------------------------------------------------------------------

name_string :: HS.Name -> String
name_string (Ident  n) = n
name_string (Symbol n) = n

go_name :: HS.Name -> TH.Name
go_name = mkName . name_string

--------------------------------------------------------------------------------

data QNameMode = TypeMode | ValueMode

mode_what :: QNameMode -> String
mode_what TypeMode  = "type"
mode_what ValueMode = "value"

mode_lookup :: QNameMode -> String -> Q (Maybe TH.Name)
mode_lookup TypeMode  = lookupTypeName
mode_lookup ValueMode = lookupValueName

-- 1st type, 2nd value
mode_select :: QNameMode -> a -> a -> a
mode_select TypeMode  t _ = t
mode_select ValueMode _ v = v

qname_resolve :: QNameMode -> String -> Q TH.Name
qname_resolve mode n =
  mode_lookup mode n >>=
    maybe (fail $  "eff: Unknown " ++ mode_what mode ++ " `" ++ n ++ "'") pure

go_qname :: QNameMode -> HS.QName -> Q TH.Name

go_qname TypeMode (Qual (ModuleName m) (Symbol n)) =
  pure . mkName $ m ++ "." ++ n

go_qname TypeMode (UnQual (Symbol n)) = do
  pure $ mkName n

-- Some bug in GHC 7.8.3 / template-haskell 2.9.0.0 prevents 'lookupTypeName'
-- from working with operators
      
go_qname mode (Qual (ModuleName m) n) =
  qname_resolve mode $ m ++ "." ++ name_string n

go_qname mode (UnQual n) = do
  let nstr        = name_string n
      constructor = qname_resolve mode
      variable    = fmap (fromMaybe $ mkName nstr) . mode_lookup mode
      bound       = pure . mkName
      resolve     = case (mode, n) of
        (_,         Ident  ((isUpper -> True) : _)) -> constructor
        (TypeMode,  Symbol _)                       -> constructor -- Handled above
        (ValueMode, Symbol (':' : _))               -> constructor
        (TypeMode,  _)                              -> bound
        (ValueMode, _)                              -> variable
  resolve nstr

go_qname mode (Special UnitCon)              = pure $ mode_select mode ''()   '()
go_qname mode (Special ListCon)              = pure $ mode_select mode ''[]   '[]
go_qname mode (Special UnboxedSingleCon)     = pure $ mode_select mode ''(##) '(##) -- The name is a lie -- this is 0-ary now
go_qname mode (Special (TupleCon Boxed n))   = pure $ mode_select mode (tupleTypeName n) (tupleDataName n)
go_qname mode (Special (TupleCon Unboxed n)) = pure $ mode_select mode (unboxedTupleTypeName n) (unboxedTupleDataName n)
go_qname mode (Special FunCon)               = mode_select mode (pure ''(->)) (fail "eff: `->' is type-level")
go_qname mode (Special Cons)                 = mode_select mode (fail "eff: `:' is value-level") (pure '(:))

--------------------------------------------------------------------------------

go_type :: HS.Type -> Build TH.Type

go_type (TyForall binders cxt ty) = do
  binders' <- lift . mapM go_binder $ F.concat binders
  with_bound (S.fromList $ map (\case { PlainTV n -> n ; KindedTV n _ -> n }) binders') $
    ForallT     binders'
            <$> mapM go_pred cxt
            <*> go_type ty

go_type (TyFun a b) = do
  a' <- go_type a
  b' <- go_type b
  pure $ ArrowT `AppT` a' `AppT` b'

go_type (TyTuple boxed tys) = do
  tys' <- mapM go_type tys
  let tuple = case boxed of
                Boxed   -> TupleT
                Unboxed -> UnboxedTupleT
  pure $ foldl' AppT (tuple $ length tys') tys'

go_type (TyList a) = AppT ListT <$> go_type a

go_type (TyParArray _) = fail "eff: Data Parallel Haskell unsupported"

go_type (TyApp f a) = AppT <$> go_type f <*> go_type a

go_type (TyVar x) = do
  let n = go_name x
  bound <- ask
  unless (n `S.member` bound) $ report_free n
  pure $ VarT n

go_type (TyCon c) = lift $ ConT <$> go_qname TypeMode c

go_type (TyParen t) = go_type t

go_type (TyInfix l op r) = do
  op' <- lift $ go_qname TypeMode op
  l'  <- go_type l
  r'  <- go_type r
  pure $ ConT op' `AppT` l' `AppT` r'

go_type (TyKind t k) = SigT <$> go_type t <*> lift (go_kind k)

go_type (TyPromoted p) = lift $ do
  reportWarning "eff: Promoted types are not handled well by haskell-src-exts"
  go_promoted p

go_type (TyEquals _ _) = fail "eff: Type equality not supported here"

go_type (TySplice _) = fail "eff: Template Haskell not supported"

go_type (TyBang UnpackedTy _) = fail "eff: `UNPACK' pragma not supported"

go_type (TyBang BangedTy t) = do
  t' <- go_type t
  n <- mkName . (abbreviateType t' ++) . show <$> fresh_id
  bind_effectful n t'
  pure $ VarT n

--------------------------------------------------------------------------------

-- The Promoted type is wrong -- promoted lists contain *types*, not just
-- promoted things!
go_promoted :: HS.Promoted -> Q TH.Type
go_promoted (PromotedInteger   n)  =
  pure . LitT $ NumTyLit n
go_promoted (PromotedString    s)  =
  pure . LitT $ StrTyLit s
go_promoted (PromotedCon     _ qn) =
  PromotedT <$> go_qname ValueMode qn
go_promoted (PromotedList    _ ps) =
  foldr (AppT . AppT PromotedConsT) PromotedNilT <$> mapM go_promoted ps
go_promoted (PromotedTuple     ps) =
  foldl' AppT (PromotedTupleT $ length ps) <$> mapM go_promoted ps
go_promoted PromotedUnit           =
  pure $ PromotedT '()

--------------------------------------------------------------------------------

-- Why are there promoted things here?
go_kind :: HS.Kind -> Q TH.Kind
go_kind KindStar        = pure StarT
go_kind KindBang        = fail "eff: Kind `#' unsupported"
go_kind (KindFn k1 k2)  = do
  k1' <- go_kind k1
  k2' <- go_kind k2
  pure $ ArrowT `AppT` k1' `AppT` k2'
go_kind (KindParen k)   = go_kind k
go_kind (KindVar n)     = VarT <$> go_qname TypeMode n
go_kind (KindApp k1 k2) = AppT <$> go_kind k1 <*> go_kind k2
go_kind (KindTuple ks)  =
  foldl' AppT (PromotedTupleT $ length ks) <$> mapM go_kind ks
go_kind (KindList ks)   =
  foldr (AppT . AppT PromotedConsT) PromotedNilT <$> mapM go_kind ks

--------------------------------------------------------------------------------

go_binder :: HS.TyVarBind -> Q TH.TyVarBndr
go_binder (KindedVar   n k) = KindedTV (go_name n) <$> go_kind k
go_binder (UnkindedVar n)   = pure . PlainTV $ go_name n

--------------------------------------------------------------------------------

go_pred :: HS.Asst -> Build TH.Pred
go_pred (ClassA c ts)     = ClassP <$> lift (go_qname TypeMode c) <*> mapM go_type ts
go_pred (VarA   n)        = pure $ ClassP (go_name n) []
go_pred (InfixA l op r)   = ClassP <$> lift (go_qname TypeMode op) <*> mapM go_type [l,r]
go_pred (IParam _ _)      = fail "eff: Implicit parameters unsupported"
go_pred (HS.EqualP t1 t2) = TH.EqualP <$> go_type t1 <*> go_type t2
go_pred (ParenA a)        = go_pred a

--------------------------------------------------------------------------------

-- If the type is of the form @a -> b -> c -> m d@, then this function returns
-- @Just m@; otherwise, it returns @Nothing@.
guess_effect :: TH.Type -> Maybe TH.Type
guess_effect (ForallT _ _ t)                              = guess_effect t
guess_effect (SigT t _)                                   = guess_effect t
guess_effect (ArrowT   `AppT` _ `AppT` t)                 = guess_effect t
guess_effect (ConT arr `AppT` _ `AppT` t) | arr == ''(->) = guess_effect t
guess_effect (t `AppT` _)                                 = Just t
guess_effect _                                            = Nothing

--------------------------------------------------------------------------------

-- |A short type variable (prefix) to replace a full type.
abbreviateType :: TH.Type -> String
abbreviateType = unclones . abbrevType where
  abbrevType (ForallT _ _ t)                     = abbrevType t
  abbrevType (SigT t _)                          = abbrevType t
  abbrevType (VarT v)                            = abbrevName v (\vn _  -> clone vn)
  abbrevType (ConT c)                            = abbrevName c (\_  c0 -> [c0])
  abbrevType (PromotedT p)                       = abbrevName p (\_  p0 -> [p0])
  abbrevType (TupleT 0)                          = "u"
  abbrevType (UnboxedTupleT 0)                   = "uu"
  abbrevType (TupleT n)                          = "t" ++ show n
  abbrevType (UnboxedTupleT n)                   = "ut" ++ show n
  abbrevType ArrowT                              = "fn"
  abbrevType ListT                               = "l"
  abbrevType (PromotedTupleT n)                  = "t" ++ show n
  abbrevType PromotedNilT                        = "n"
  abbrevType PromotedConsT                       = "c"
  abbrevType StarT                               = "s"
  abbrevType ConstraintT                         = "con"
  abbrevType (LitT (NumTyLit _))                 = "n"
  abbrevType (LitT (StrTyLit _))                 = "s"
  abbrevType (AppT (AppT (isArrow -> True) _) _) = abbrevType ArrowT
  abbrevType (AppT (isList -> True) t)           = abbrevType t ++ "s"
  abbrevType (isFullTuple -> Just ts)            = concatMap abbrevType ts
  abbrevType (AppT t1 t2)                        = abbrevType t1 ++ abbrevType t2
  
  -- 'clone' takes a variable name and uses it, but remembers -- via @[]@s --
  -- that it was used.  'unclones' removes all the cloning elements (@[]@s)
  -- from a type, and appens a prime (@'@) iff the string was /precisely/ the
  -- cloning of a single variable.
  clone str = "[" ++ str ++ "]"
  unclones ('[' : (break (== ']') -> (str, "]"))) | '[' `notElem` str = str ++ "'"
  unclones str = filter (`notElem` "[]") str
  
  abbrevDefault = "z"
  
  abbrevName n f
    | n == ''(->)       = abbrevType ArrowT
    | n == ''[]         = abbrevType ListT
    | n == '[]          = abbrevType PromotedNilT
    | n == '(:)         = abbrevType PromotedConsT
    | n == ''Constraint = abbrevType ConstraintT
    | n == ''()         = abbrevType $ TupleT 0
    | n == '()          = abbrevType $ TupleT 0
    | Just k <- isTupleName n =
        abbrevType $ (if '#' `elem` nameBase n then UnboxedTupleT else TupleT) k
    | otherwise =
        case nameBase n of
          n'@(n0 : _) | isAlpha n0 -> f n' $ toLower n0
   --       _                        -> abbrevDefault
  
  isArrow ArrowT   = True
  isArrow (ConT c) = c == ''(->)
  isArrow _        = False
  
  isList ListT    = True
  isList (ConT c) = c == ''[]
  isList _        = False
  
  isTupleName c = case length . filter (== ',') $ nameBase c of
                    0 -> Nothing
                    n -> Just $ n+1
  
  isTuple (TupleT n) = Just n
  isTuple (ConT c)   = isTupleName c
  isTuple _          = Nothing     
  
  isFullTuple = go [] where
    go tys (AppT t1 t2)        = go (t2 : tys) t1
    go tys (isTuple -> Just n) = if length tys == n
                                 then Just tys
                                 else Nothing
    go _   _                   = Nothing
