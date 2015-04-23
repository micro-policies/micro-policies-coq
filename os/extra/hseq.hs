{-# LANGUAGE StandaloneDeriving #-}

hseq_compare :: (a1 -> Eqtype.Equality__Coq_type) -> ([] a1) -> 
                Coq_hseq a1 Eqtype.Equality__Coq_sort ->
                Coq_hseq a1 Eqtype.Equality__Coq_sort ->
                Prelude.Ordering
hseq_compare t_ idx hs1 hs2 =
  case idx of {
   [] -> Prelude.EQ;
   (:) i idx0 ->
    (Data.Monoid.<>)
      (Eqtype.compare_op (t_ i) (hshead i idx0 (unsafeCoerce hs1))
        (hshead i idx0 (unsafeCoerce hs2)))
      (hseq_compare t_ (Seq.behead ((:) i idx0)) (hsbehead ((:) i idx0) hs1)
        (hsbehead ((:) i idx0) hs2))}

-- `Show' instances
deriving instance Prelude.Show Coq_hseq_nil
deriving instance (Prelude.Show t, Prelude.Show s) => Prelude.Show (Coq_hseq_cons t s)
