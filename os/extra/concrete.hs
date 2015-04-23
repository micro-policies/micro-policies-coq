{-# LANGUAGE StandaloneDeriving #-}

deriving instance Prelude.Eq  Concrete__Coq_mvec
deriving instance Prelude.Ord Concrete__Coq_mvec

deriving instance Prelude.Eq  Concrete__Coq_rvec
deriving instance Prelude.Ord Concrete__Coq_rvec

_Exports__state_cmp :: Types.Coq_machine_types ->
                       Concrete__Coq_state -> Concrete__Coq_state -> Prelude.Ordering
_Exports__state_cmp mt s1 s2 =
  Data.Monoid.mconcat
    [ Eqtype.compare_op
        (Partmap._PartMap__Exports__partmap_eqType
          (Word.word_ordType (Types.word_size mt))
          (Types.atom_eqType
            (Word.word_eqType (Types.word_size mt))
            (Word.word_eqType (Types.word_size mt))))
        (unsafeCoerce (_Concrete__mem mt s1))
        (unsafeCoerce (_Concrete__mem mt s2))
    , Eqtype.compare_op
        (Partmap._PartMap__Exports__partmap_eqType
          (Word.word_ordType (Types.reg_field_size mt))
          (Types.atom_eqType
            (Word.word_eqType (Types.word_size mt))
            (Word.word_eqType (Types.word_size mt))))
        (unsafeCoerce (_Concrete__regs mt s1))
        (unsafeCoerce (_Concrete__regs mt s2))
    , Eqtype.compare_op
        (Partmap._PartMap__Exports__partmap_eqType
          (_Concrete__mvec_ordType mt)
          (_Concrete__rvec_eqType  mt))
        (unsafeCoerce (_Concrete__cache mt s1))
        (unsafeCoerce (_Concrete__cache mt s2))
    , Eqtype.compare_op
        (Types.atom_eqType
          (Word.word_eqType (Types.word_size mt))
          (Word.word_eqType (Types.word_size mt)))
        (unsafeCoerce (_Concrete__pc mt s1))
        (unsafeCoerce (_Concrete__pc mt s2))
    , Eqtype.compare_op
        (Types.atom_eqType
          (Word.word_eqType (Types.word_size mt))
          (Word.word_eqType (Types.word_size mt)))
        (unsafeCoerce (_Concrete__epc mt s1))
        (unsafeCoerce (_Concrete__epc mt s2)) ]

-- `Show' instances
deriving instance Prelude.Show Concrete__Coq_mvec
deriving instance Prelude.Show Concrete__Coq_rvec
deriving instance Prelude.Show Concrete__Coq_mvec_part
deriving instance Prelude.Show Concrete__CTMask
deriving instance Prelude.Show Concrete__Coq_state
