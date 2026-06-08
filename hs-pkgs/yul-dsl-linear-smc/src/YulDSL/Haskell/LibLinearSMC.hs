module YulDSL.Haskell.LibLinearSMC
  (  keccak256'l
  ) where
-- linear-base
-- yul-dsl
import YulDSL.Core
-- yul-dsl-pure
-- (lvm)
--
import YulDSL.Haskell.Effects.LinearSMC.YulPort



keccak256'l :: forall a r. YulO2 r a => P'P r a ⊸ P'P r B32
keccak256'l = encodeP'x (YulJmpB (MkYulBuiltIn @"__keccak_c_" @a @B32))
