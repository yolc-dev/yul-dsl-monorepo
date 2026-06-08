{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TemplateHaskell     #-}
module YulDSL.Haskell.Effects.LinearSMC.YulPort
  ( -- * Yul Port Definitions
    -- $LinearPortDefs
    PortEffect (PurePort)
  , P'P (MkP'x), unP'x, encodeP'x, decodeP'x
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

type instance IsEffectNotPure PortEffect = True
type instance MayEffectWorld  PortEffect = True

-- | Linear port of yul categories with the port effect kind, aka. yul ports.
newtype P'P r a = MkP'x (P (YulCat PortEffect) r a)

unP'x :: forall r a. P'P r a ⊸ P (YulCat PortEffect) r a
unP'x (MkP'x x) = x


-- | Linear port of yul category with linearly versioned data, aka. versioned yul ports.

encodeP'x :: forall (eff :: PortEffect) a b r.
  YulO3 r a b =>
  YulCat PortEffect a b ->
  (P'P r a ⊸ P'P r b)
encodeP'x c = MkP'x . encode c . unP'x

decodeP'x :: forall a b.
  YulO2 a b =>
  (forall r. YulO1 r => P'P r a ⊸ P'P r b) ->
  YulCat PortEffect a b
decodeP'x f = decode (\a -> unP'x (f (MkP'x a)))

-- | Unsafe coerce yul port' effects.
unsafeCoerceYulPort :: forall  r a.
  P'P r a ⊸ P'P r a
unsafeCoerceYulPort = MkP'x . unP'x

-- | Unsafe coerce yul port diagram's effects.
unsafeCoerceYulPortDiagram :: forall  r a b.
    (P'P r a ⊸ P'P r b) ⊸ (P'P r a ⊸ P'P r b)
unsafeCoerceYulPortDiagram f x = unsafeCoerceYulPort (f (unsafeCoerceYulPort x))
------------------------------------------------------------------------------------------------------------------------

extendType'l :: forall a r.
  (YulO3 a (ABITypeDerivedOf a) r) =>
  P'P r (ABITypeDerivedOf a) ⊸ P'P r a
extendType'l = encodeP'x YulExtendType

--
-- NP type
