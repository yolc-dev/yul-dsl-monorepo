module YulDSL.Haskell.LibLinearSMC
  ( module YulDSL.Haskell.LibPure
  , keccak256'l
  ) where
-- linear-base
import GHC.TypeLits                     (KnownNat)
import Prelude.Linear
-- yul-dsl
import YulDSL.Core
import YulDSL.StdBuiltIns.ABICodec      ()
-- yul-dsl-pure
import YulDSL.Haskell.LibPure
-- (lvm)
--
import Data.Num.Linear.YulDSL           ()
import YulDSL.Haskell.Effects.LinearSMC.YulPort



keccak256'l :: forall a eff r. YulO2 r a => P'x eff r a ⊸ P'x eff r B32
keccak256'l = encodeP'x (YulJmpB (MkYulBuiltIn @"__keccak_c_" @a @B32))
