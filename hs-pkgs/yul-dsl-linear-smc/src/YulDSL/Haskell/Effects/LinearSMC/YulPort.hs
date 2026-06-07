{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TemplateHaskell     #-}
module YulDSL.Haskell.Effects.LinearSMC.YulPort
  ( -- * Yul Port Definitions
    -- $LinearPortDefs
    PortEffect (PurePort, VersionedPort)
  , P'x (MkP'x), unP'x, P'P, encodeP'x, decodeP'x
  , unsafeCoerceYulPort, unsafeCoerceYulPortDiagram
    -- * General Yul Port Operations
    -- $GeneralOps
    -- * Type Operations
    -- $TypeOps
  , extendType'l
  ) where
-- base
import Control.Monad                       (replicateM)
import Prelude                             qualified as BasePrelude
-- template-haskell
import Language.Haskell.TH                 qualified as TH
-- linear-base
import Prelude.Linear
-- linear-smc
import Control.Category.Linear             (P, copy, decode, discard, encode, ignore, merge, mkUnit, split)
-- yul-dsl-pure
import YulDSL.Haskell.LibPure
--
import Control.Category.Constrained.YulDSL ()


------------------------------------------------------------------------------------------------------------------------
-- $LinearPortDefs
------------------------------------------------------------------------------------------------------------------------


-- | Various types of port effects for the yul port API.
data PortEffect = PurePort          -- ^ Pure port that does not need to be versioned
                | VersionedPort Nat -- ^ Linearly versioned port

type instance IsEffectNotPure PortEffect = True
type instance MayEffectWorld  PortEffect = True

-- | Linear port of yul categories with the port effect kind, aka. yul ports.
newtype P'x (eff :: PortEffect) r a = MkP'x (P (YulCat PortEffect) r a)

-- ^ Role annotation to make sure @eff@ is nominal, so only unsafe coercing is allowed.
type role P'x nominal _ _

unP'x :: forall (eff :: PortEffect) r a. P'x eff r a ⊸ P (YulCat PortEffect) r a
unP'x (MkP'x x) = x

-- | Linear port of yul category with pure data, aka. pure yul ports.
type P'P = P'x PurePort

-- | Linear port of yul category with linearly versioned data, aka. versioned yul ports.

encodeP'x :: forall (eff :: PortEffect) a b r.
  YulO3 r a b =>
  YulCat PortEffect a b ->
  (P'x eff r a ⊸ P'x eff r b)
encodeP'x c = MkP'x . encode c . unP'x

decodeP'x :: forall (eff :: PortEffect) a b.
  YulO2 a b =>
  (forall r. YulO1 r => P'x eff r a ⊸ P'x eff r b) ->
  YulCat PortEffect a b
decodeP'x f = decode (\a -> unP'x (f (MkP'x a)))

-- | Unsafe coerce yul port' effects.
unsafeCoerceYulPort :: forall (eff1 :: PortEffect) (eff2 :: PortEffect) r a.
  P'x eff1 r a ⊸ P'x eff2 r a
unsafeCoerceYulPort = MkP'x . unP'x

-- | Unsafe coerce yul port diagram's effects.
unsafeCoerceYulPortDiagram :: forall (eff1 :: PortEffect) (eff2 :: PortEffect) (eff3 :: PortEffect) r a b.
    (P'x eff1 r a ⊸ P'x eff2 r b) ⊸ (P'x eff3 r a ⊸ P'x eff3 r b)
unsafeCoerceYulPortDiagram f x = unsafeCoerceYulPort (f (unsafeCoerceYulPort x))
------------------------------------------------------------------------------------------------------------------------

extendType'l :: forall a eff r.
  (YulO3 a (ABITypeDerivedOf a) r) =>
  P'x eff r (ABITypeDerivedOf a) ⊸ P'x eff r a
extendType'l = encodeP'x YulExtendType

--
-- NP type
