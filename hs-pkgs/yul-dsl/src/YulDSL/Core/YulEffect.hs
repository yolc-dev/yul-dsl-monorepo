
module YulDSL.Core.YulEffect
  ( IsEffectNotPure, MayEffectWorld
  , YulCatEffectClass (..)
  , AssertPureEffect, AssertNonPureEffect
  ) where
-- base
import Data.Kind      (Constraint)
import GHC.TypeError  (Assert, ErrorMessage (Text), Unsatisfiable)
-- eth-abi
import Data.Type.Bool


-- | An open type family for declaring a effect non-pure.
type family IsEffectNotPure (eff :: k) :: Bool

-- | An open type family for declaring a effect may change the state of the world.
type family MayEffectWorld (eff :: k) :: Bool

-- | Classification of yul category effect.
data YulCatEffectClass
  = PureEffect
  deriving (Eq, Show)

-- | Assert whether an effect can be used for morphisms that are pure. (F, F)
type AssertPureEffect :: k -> Constraint
type AssertPureEffect eff = Assert (Not (IsEffectNotPure eff) && Not (MayEffectWorld eff))
                            (Unsatisfiable (Text "pure effect expected"))

-- | Assert whether an effect can be used for morphisms that are pure. (T, -)
type AssertNonPureEffect :: k -> Constraint
type AssertNonPureEffect eff = Assert (IsEffectNotPure eff)
                               (Unsatisfiable (Text "non-pure effect expected"))

