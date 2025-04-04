{-# LANGUAGE AllowAmbiguousTypes #-}
module YulDSL.Core.YulEffect
  ( IsEffectNotPure, MayEffectWorld
  , YulCatEffectClass (..), SYulCatEffectClass, KnownYulCatEffectClass(yulCatEffectClassSing, fromSYulCatEffectClass)
  , ClassifiedYulCatEffect (classifyYulCatEffect)
  , AssertPureEffect, AssertNonPureEffect, AssertStaticEffect, AssertOmniEffect, IsNonsenseEffect
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
  | StaticEffect
  | OmniEffect
  deriving (Eq, Show)

-- | Singleton data for yul category effect classifications.
data SYulCatEffectClass (efc :: YulCatEffectClass) = SYulCatEffectClass

-- | Singleton type class for yul category effect classification
class KnownYulCatEffectClass (efc :: YulCatEffectClass) where
  yulCatEffectClassSing :: SYulCatEffectClass efc
  yulCatEffectClassSing = SYulCatEffectClass @efc
  fromSYulCatEffectClass :: SYulCatEffectClass efc -> YulCatEffectClass
instance KnownYulCatEffectClass PureEffect where fromSYulCatEffectClass _ = PureEffect
instance KnownYulCatEffectClass StaticEffect where fromSYulCatEffectClass _ = StaticEffect
instance KnownYulCatEffectClass OmniEffect where fromSYulCatEffectClass _ = OmniEffect

-- | Singleton class for YulCat effect classification.
class ClassifiedYulCatEffect (eff :: k) where
  -- | Create classification data for known yul effect.
  classifyYulCatEffect :: YulCatEffectClass

-- | Assert whether an effect can be used for morphisms that are pure. (F, F)
type AssertPureEffect :: k -> Constraint
type AssertPureEffect eff = Assert (Not (IsEffectNotPure eff) && Not (MayEffectWorld eff))
                            (Unsatisfiable (Text "pure effect expected"))

-- | Assert whether an effect can be used for morphisms that are pure. (T, -)
type AssertNonPureEffect :: k -> Constraint
type AssertNonPureEffect eff = Assert (IsEffectNotPure eff)
                               (Unsatisfiable (Text "non-pure effect expected"))

-- | Assert whether an effect can be used for morphisms that are non-pure but cannot change world. (T, F)
type AssertStaticEffect :: k -> Constraint
type AssertStaticEffect eff = Assert (IsEffectNotPure eff && Not (MayEffectWorld eff))
                              (Unsatisfiable (Text "static effect expected"))

-- | Assert whether an effect can be used for morphisms that are non-pure and may change world. (T, T)
type AssertOmniEffect :: k -> Constraint
type AssertOmniEffect eff = Assert (IsEffectNotPure eff && MayEffectWorld eff)
                            (Unsatisfiable (Text "omni effect expected"))

-- | This effect doesn't make sense. (F, T)
type IsNonsenseEffect :: k -> Bool
type IsNonsenseEffect eff = Not (IsEffectNotPure eff) && MayEffectWorld eff
