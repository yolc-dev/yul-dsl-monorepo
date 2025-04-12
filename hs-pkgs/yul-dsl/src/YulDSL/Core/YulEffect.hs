{-# LANGUAGE AllowAmbiguousTypes #-}
module YulDSL.Core.YulEffect
  ( IsEffectNonPure, MayAffectWorld
  , YulCatEffectClass (PureEffect, StaticEffect, OmniEffect), KnownYulCatEffect (classifyYulCatEffect)
  , SYulCatEffectClass, KnownYulCatEffectClass(yulCatEffectClassSing, fromSYulCatEffectClass)
  , AssertPureEffect, AssertNonPureEffect, AssertStaticEffect, AssertOmniEffect, IsNonsenseEffect
  ) where
-- base
import Control.Exception                  (assert)
import Data.Kind                          (Constraint)
import GHC.TypeError                      (Assert, ErrorMessage (Text), Unsatisfiable)
-- eth-abi
import Ethereum.ContractABI.CoreType.BOOL


-- | An open type family for declaring a effect non-pure.
type family IsEffectNonPure (eff :: k) :: Bool

-- | An open type family for declaring a effect may change the state of the world.
type family MayAffectWorld (eff :: k) :: Bool

-- | Classification of yul category effect.
data YulCatEffectClass
  = PureEffect
  | StaticEffect
  | OmniEffect
  deriving (Eq, Show)

-- | Singleton type class for any known yulcat effect.
class KnownYulCatEffect eff where
  -- | Get the classification of the known yul effect.
  classifyYulCatEffect :: (KnownBool (IsEffectNonPure eff), KnownBool (MayAffectWorld eff)) => YulCatEffectClass
  classifyYulCatEffect =
    let nonPure = fromBoolKind @(IsEffectNonPure eff)
        effectful = fromBoolKind @(MayAffectWorld eff)
    in if not nonPure then assert (not effectful) PureEffect
       else if effectful then OmniEffect else StaticEffect

-- | Singleton data for yul category effect classifications.
data SYulCatEffectClass (efc :: YulCatEffectClass) = SYulCatEffectClass deriving (Eq, Show)

-- | Singleton type class for yul category effect classification
class KnownYulCatEffectClass (efc :: YulCatEffectClass) where
  -- | To the singleton of @efc@.
  yulCatEffectClassSing :: SYulCatEffectClass efc
  yulCatEffectClassSing = SYulCatEffectClass @efc
  -- | From the singleton to of @efc@.
  fromSYulCatEffectClass :: SYulCatEffectClass efc -> YulCatEffectClass
instance KnownYulCatEffectClass PureEffect   where fromSYulCatEffectClass _ = PureEffect
instance KnownYulCatEffectClass StaticEffect where fromSYulCatEffectClass _ = StaticEffect
instance KnownYulCatEffectClass OmniEffect   where fromSYulCatEffectClass _ = OmniEffect

-- | Assert whether an effect can be used for morphisms that are pure. (F, F)
type AssertPureEffect :: k -> Constraint
type AssertPureEffect eff = Assert (Not (IsEffectNonPure eff) && Not (MayAffectWorld eff))
                            (Unsatisfiable (Text "pure effect expected"))

-- | Assert whether an effect can be used for morphisms that are pure. (T, -)
type AssertNonPureEffect :: k -> Constraint
type AssertNonPureEffect eff = Assert (IsEffectNonPure eff)
                               (Unsatisfiable (Text "non-pure effect expected"))

-- | Assert whether an effect can be used for morphisms that are non-pure but cannot change world. (T, F)
type AssertStaticEffect :: k -> Constraint
type AssertStaticEffect eff = Assert (IsEffectNonPure eff && Not (MayAffectWorld eff))
                              (Unsatisfiable (Text "static effect expected"))

-- | Assert whether an effect can be used for morphisms that are non-pure and may change world. (T, T)
type AssertOmniEffect :: k -> Constraint
type AssertOmniEffect eff = Assert (IsEffectNonPure eff && MayAffectWorld eff)
                            (Unsatisfiable (Text "omni effect expected"))

-- | This effect doesn't make sense. (F, T)
type IsNonsenseEffect :: k -> Bool
type IsNonsenseEffect eff = Not (IsEffectNonPure eff) && MayAffectWorld eff
