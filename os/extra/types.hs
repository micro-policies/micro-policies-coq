{-# LANGUAGE StandaloneDeriving #-}

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
deriving instance (Prelude.Show v, Prelude.Show t) => Prelude.Show (Coq_atom v t)
deriving instance Prelude.Show Coq_syscall_regs
