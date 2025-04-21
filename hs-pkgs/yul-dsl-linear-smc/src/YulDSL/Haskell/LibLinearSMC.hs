module YulDSL.Haskell.LibLinearSMC
  ( -- * Re-export linear-base prelude (TODO: be more selective here)
    module Prelude.Linear
    -- * Re-export library for pure yul functions
  , module YulDSL.Haskell.LibPure
    -- * Re-export library for building linear-smc yul effects
  , module YulDSL.Haskell.Effects.LinearSMC
    -- * Additional linear-smc utilities
  , keccak256'l
  , ycaller
  , getSolo
  ) where
-- linear-base
import GHC.TypeLits                       (KnownNat)
-- replacing Eq/Ord with MPOrd
import Prelude.Linear                     hiding (Eq (..), Ord (..))
-- yul-dsl
import YulDSL.Core
import YulDSL.StdBuiltIns.ABICodec        ()
-- yul-dsl-pure
import YulDSL.Haskell.LibPure
-- (lvm)
import Control.LinearlyVersionedMonad.LVM qualified as LVM
--
import Data.Num.Linear.YulDSL             ()
import YulDSL.Haskell.Effects.LinearSMC


keccak256'l :: forall a eff r. YulO2 r a => P'x eff r a ⊸ P'x eff r B32
keccak256'l = encodeP'x (YulJmpB (MkYulBuiltIn @"__keccak_c_" @a @B32))

ycaller :: forall r v. (KnownNat v, YulO1 r) => YulLVM v v r (P'P r ADDR)
ycaller = embed () LVM.>>= LVM.pure . encodeP'x (YulJmpB (MkYulBuiltIn @"__caller"))

getSolo :: Solo a %p -> a
getSolo (MkSolo a) = a
