{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances   #-}
module YulDSL.Haskell.Effects.LinearSMC.LinearYulCat
  ( -- * Linear Effect Kind
    -- $LinearEffectKind
    decode'l, YulCat'LPP(..)
  ) where
-- base
import GHC.TypeLits                             (KnownNat, type (+))
import Prelude                                  qualified as BasePrelude
-- linear-base
import Prelude.Linear
-- yul-dsl-pure
import YulDSL.Haskell.LibPure
--
import YulDSL.Haskell.Effects.LinearSMC.YulPort

decode'l :: forall a b. YulO2 a b
  => (forall r. YulO1 r => P'x PurePort r a ⊸ P'x PurePort r b)
  -> YulCat Pure a b
decode'l f = YulUnsafeCoerceEffect (decodeP'x (unsafeCoerceYulPortDiagram f))

newtype YulCat'LPP r a b = MkYulCat'LPP (P'P r a ⊸ P'P r b)
