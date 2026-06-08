module YulDSL.Haskell.LibLinearSMC
  ( module YulDSL.Haskell.LibPure
  , keccak256'l
  ) where
-- linear-base
import Prelude.Linear
-- yul-dsl
import YulDSL.Core
-- yul-dsl-pure
import YulDSL.Haskell.LibPure
-- (lvm)
--
import YulDSL.Haskell.Effects.LinearSMC.YulPort



keccak256'l :: forall a r. YulO2 r a => P'P r a ⊸ P'P r B32
keccak256'l = encodeP'x (YulJmpB (MkYulBuiltIn @"__keccak_c_" @a @B32))
