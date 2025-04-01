module YulDSL.Haskell.LibLinearSMC
  ( module YulDSL.Haskell.LibPure
  , module YulDSL.Haskell.Effects.LinearSMC
  , keccak256'l
  , ycaller
  ) where
-- linear-base
import Prelude.Linear
-- yul-dsl
import YulDSL.Core
import YulDSL.StdBuiltIns.ABICodec      ()
-- yul-dsl-pure
import YulDSL.Haskell.LibPure
-- (lvm)
import Control.LinearlyVersionedMonad   qualified as LVM
--
import Data.Num.Linear.YulDSL           ()
import YulDSL.Haskell.Effects.LinearSMC


keccak256'l :: forall a eff r. YulO2 r a => P'x eff r a ⊸ P'x eff r B32
keccak256'l = encodeP'x (YulJmpB (MkYulBuiltIn @"__keccak_c_" @a @B32))

ycaller :: forall r va. YulO1 r => YulMonad va va r (P'P r ADDR)
ycaller = embed () LVM.>>= LVM.pure . encodeP'x (YulJmpB (MkYulBuiltIn @"__caller"))
