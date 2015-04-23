{-# LANGUAGE StandaloneDeriving #-}

-- `Show' instances
deriving instance Prelude.Show t => Prelude.Show (GenTree__Coq_tree t)

{-# POSTPROCESS CONSTRAINT _Countable__coq_EqMixin :: Prelude.Ord 0 #-}
