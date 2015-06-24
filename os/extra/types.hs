{-# LANGUAGE StandaloneDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

data Atom v t = v :@ t
              deriving ( Prelude.Eq, Prelude.Ord, Prelude.Read, Prelude.Show
                       , Prelude.Functor
                       , Data.Foldable.Foldable, Data.Traversable.Traversable )
infix 9 :@

instance Data.Bifunctor.Bifunctor Atom where
  bimap vf tf (v :@ t) = vf v :@ tf t

deriving instance Prelude.Eq  Coq_binop
deriving instance Prelude.Ord Coq_binop

deriving instance Prelude.Eq  Coq_opcode
deriving instance Prelude.Ord Coq_opcode

deriving instance Prelude.Eq  Coq_vopcode
deriving instance Prelude.Ord Coq_vopcode

deriving instance Prelude.Eq  Coq_instr
deriving instance Prelude.Ord Coq_instr

-- `Show' instances
deriving instance Prelude.Show Coq_binop
deriving instance Prelude.Show Coq_opcode
deriving instance Prelude.Show Coq_vopcode
deriving instance Prelude.Show Coq_machine_types
deriving instance Prelude.Show Coq_instr
deriving instance Prelude.Show Coq_machine_ops_spec
deriving instance Prelude.Show Coq_syscall_regs
