type Coq_set_type = Data.Set.Set GHC.Base.Any
  -- Or should I use my finite-infinite set library from ages ago?

finsetAbstract :: Prelude.String -> a
finsetAbstract fn = GHC.Stack.errorWithStackTrace (fn Prelude.++ ": finsets are abstract, not finfuns!")

finsetFinite :: Prelude.String -> a
finsetFinite fn = GHC.Stack.errorWithStackTrace (fn Prelude.++ ": finsets are finite!")

-- Interestingly 'withFintypeOrd' does not typecheck if (a) eta-expanded, or (b)
-- implemented as 'withFintypeOrd''.  WTF‽

withFintypeOrd :: Fintype.Finite__Coq_type -> (Prelude.Ord GHC.Base.Any => a) -> a
withFintypeOrd ft =
  Data.Reflection.Constraint.providing
    (Data.Reflection.Constraint.Ord
       (unsafeCoerce (Eqtype.compare_op (Fintype._Finite__eqType ft))))
          -- 'unsafeCoerce' takes us from '()' to 'Any'

withFintypeOrd' :: (Prelude.Ord GHC.Base.Any => a) -> Fintype.Finite__Coq_type -> a
withFintypeOrd' = Prelude.flip withFintypeOrd

unitAny :: () -> GHC.Base.Any
unitAny = unsafeCoerce

anyUnit :: GHC.Base.Any -> ()
anyUnit = unsafeCoerce

nestedSet :: Data.Set.Set GHC.Base.Any -> Data.Set.Set (Data.Set.Set GHC.Base.Any)
nestedSet = unsafeCoerce

flattenedSet :: Data.Set.Set (Data.Set.Set GHC.Base.Any) -> Data.Set.Set GHC.Base.Any
flattenedSet = unsafeCoerce

forgetToCoqSet :: Data.Set.Set a -> Data.Set.Set GHC.Base.Any
forgetToCoqSet = unsafeCoerce

-- This implementation is due to Dan Burton's answer to MarcoS's StackOverflow
-- question "why Data.Set has no powerset function?" [sic], available at
-- http://stackoverflow.com/a/6429301/237428
setPowerset :: Prelude.Ord a => Data.Set.Set a -> Data.Set.Set (Data.Set.Set a)
setPowerset s
  | Data.Set.null s   = Data.Set.singleton Data.Set.empty
  | Prelude.otherwise = Data.Set.map (Data.Set.insert x) ps' `Data.Set.union` ps'
    where (x, s') = Data.Set.deleteFindMin s
          ps'     = setPowerset s'
