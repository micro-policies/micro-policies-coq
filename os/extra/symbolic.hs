{-# LANGUAGE StandaloneDeriving #-}

deriving instance Prelude.Eq  Symbolic__Coq_tag_kind
deriving instance Prelude.Ord Symbolic__Coq_tag_kind

_Exports__state_cmp :: Types.Coq_machine_types -> Symbolic__Coq_params ->
                       Symbolic__Coq_state -> Symbolic__Coq_state -> Prelude.Ordering
_Exports__state_cmp mt p s1 s2 =
  Data.Monoid.mconcat
    [ Eqtype.compare_op
      (Partmap._PartMap__Exports__partmap_eqType
        (Word.word_ordType (Types.word_size mt))
        (Types.atom_eqType
          (Word.word_eqType (Types.word_size mt))
          (_Symbolic__tag_type (_Symbolic__ttypes p) Symbolic__M)))
      (unsafeCoerce (_Symbolic__mem mt p s1))
      (unsafeCoerce (_Symbolic__mem mt p s2))
    , Eqtype.compare_op
        (Partmap._PartMap__Exports__partmap_eqType
          (Word.word_ordType (Types.reg_field_size mt))
          (Types.atom_eqType
            (Word.word_eqType (Types.word_size mt))
            (_Symbolic__tag_type (_Symbolic__ttypes p) Symbolic__R)))
        (unsafeCoerce (_Symbolic__regs mt p s1))
        (unsafeCoerce (_Symbolic__regs mt p s2))
    , Eqtype.compare_op
        (Types.atom_eqType
          (Word.word_eqType (Types.word_size mt))
          (_Symbolic__tag_type (_Symbolic__ttypes p) Symbolic__P))
        (unsafeCoerce (_Symbolic__pc mt p s1))
        (unsafeCoerce (_Symbolic__pc mt p s2))
    , Eqtype.compare_op
        (_Symbolic__internal_state p)
        (_Symbolic__internal mt p s1)
        (_Symbolic__internal mt p s2) ]

-- `Show' instances
deriving instance Prelude.Show Symbolic__Coq_tag_kind
deriving instance Prelude.Show Symbolic__Coq_ivec
deriving instance Prelude.Show Symbolic__Coq_ovec
deriving instance Prelude.Show Symbolic__Coq_state
