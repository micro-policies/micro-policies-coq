{-# LANGUAGE StandaloneDeriving #-}

deriving instance Prelude.Eq  Sym__Coq_pc_tag
deriving instance Prelude.Ord Sym__Coq_pc_tag

_Sym__Exports__data_tag_cmp :: Types.Coq_machine_types -> Sym__Coq_data_tag ->
                               Sym__Coq_data_tag -> Prelude.Ordering
_Sym__Exports__data_tag_cmp mt (Sym__DATA c1 i1 w1) (Sym__DATA c2 i2 w2) =
  Eqtype.compare_op (Word.word_eqType (Types.word_size mt))
                    (unsafeCoerce c1) (unsafeCoerce c2)
  Data.Monoid.<>
  Eqtype.compare_op (Finset.set_of_eqType (Word.word_finType (Types.word_size mt)))
                    (unsafeCoerce i1) (unsafeCoerce i2)
  Data.Monoid.<>
  Eqtype.compare_op (Finset.set_of_eqType (Word.word_finType (Types.word_size mt)))
                    (unsafeCoerce w1) (unsafeCoerce w2)

_Sym__compartmentalization_internal_cmp :: Types.Coq_machine_types ->
                                           Sym__Coq_compartmentalization_internal ->
                                           Sym__Coq_compartmentalization_internal ->
                                           Prelude.Ordering
_Sym__compartmentalization_internal_cmp mt i1 i2 =
  Eqtype.compare_op (Word.word_eqType (Types.word_size mt))
                    (unsafeCoerce (_Sym__next_id mt i1))
                    (unsafeCoerce (_Sym__next_id mt i2))
  Data.Monoid.<>
  Eqtype.compare_op (_Sym__Exports__data_tag_eqType mt)
                    (unsafeCoerce (_Sym__isolate_tag mt i1))
                    (unsafeCoerce (_Sym__isolate_tag mt i2))
  Data.Monoid.<>
  Eqtype.compare_op (_Sym__Exports__data_tag_eqType mt)
                    (unsafeCoerce (_Sym__add_to_jump_targets_tag mt i1))
                    (unsafeCoerce (_Sym__add_to_jump_targets_tag mt i2))
  Data.Monoid.<>
  Eqtype.compare_op (_Sym__Exports__data_tag_eqType mt)
                    (unsafeCoerce (_Sym__add_to_store_targets_tag mt i1))
                    (unsafeCoerce (_Sym__add_to_store_targets_tag mt i2))

-- `Show' instances
deriving instance Prelude.Show Sym__Coq_pc_tag
deriving instance Prelude.Show Sym__Coq_compartmentalization_internal

instance Prelude.Show Sym__Coq_data_tag where
  showsPrec p (Sym__DATA c ii ww) = Prelude.showParen (p Prelude.>= 11)
                                  $ Prelude.showString "Sym__DATA "
                                  . Prelude.showsPrec 11 c
                                  . Prelude.showChar ' '
                                  . Prelude.showsPrec 11 (wordSet ii)
                                  . Prelude.showChar ' '
                                  . Prelude.showsPrec 11 (wordSet ww)
    where
      wordSet :: Finset.Coq_set_of -> Data.Set.Set Types.Coq_mword
      wordSet = unsafeCoerce
      
      (.) = (Prelude..)
      infixr 9 .
      {-# INLINABLE (.) #-}
      
      ($) = (Prelude.$)
      infixr 0 $
      {-# INLINABLE ($) #-}
