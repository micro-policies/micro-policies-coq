{-# LANGUAGE StandaloneDeriving #-}

data Equality__Coq_mixin_of t =
  Equality__Mixin (Ssrbool.Coq_rel t) (Equality__Coq_axiom t) (t -> t -> Prelude.Ordering)

equality__mixin :: Prelude.Ord t => Ssrbool.Coq_rel t -> Equality__Coq_axiom t -> Equality__Coq_mixin_of t
equality__mixin eqb eqP = Equality__Mixin eqb eqP Prelude.compare

compare_op :: Equality__Coq_type -> () -> () -> Prelude.Ordering
compare_op (Equality__Mixin _ _ cmp) = cmp

-- `Show' instances
deriving instance Prelude.Show t => Prelude.Show (Sub_spec t)
deriving instance Prelude.Show (Coq_insub_spec t)

{-# POSTPROCESS CONSTRAINT comparableClass :: Prelude.Ord 0 #-}
{-# POSTPROCESS CONSTRAINT coq_InjEqMixin  :: Prelude.Ord 0 #-}
{-# POSTPROCESS CONSTRAINT coq_PcanEqMixin :: Prelude.Ord 0 #-}
{-# POSTPROCESS CONSTRAINT coq_CanEqMixin  :: Prelude.Ord 0 #-}
