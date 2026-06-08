{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TemplateHaskell     #-}
module YulDSL.Haskell.Effects.LinearSMC.YulPort
  ( -- * Yul Port Definitions
    -- $LinearPortDefs
    P'P (MkP'x), unP'x, encodeP'x, decodeP'x
    -- * General Yul Port Operations
    -- $GeneralOps
    -- * Type Operations
    -- $TypeOps
  , extendType'l
  ) where
-- linear-base
import Prelude.Linear
-- linear-smc
import Control.Category.Linear             (P, decode, encode)
-- yul-dsl-pure

import YulDSL.Core
import YulDSL.Haskell.Effects.Pure

--
--
import Control.Category.Constrained.YulDSL ()


------------------------------------------------------------------------------------------------------------------------
-- $LinearPortDefs
------------------------------------------------------------------------------------------------------------------------



-- | Linear port of yul categories with the port effect kind, aka. yul ports.
newtype P'P r a = MkP'x (P (YulCat Pure) r a)

unP'x :: forall r a. P'P r a ⊸ P (YulCat Pure) r a
unP'x (MkP'x x) = x


-- | Linear port of yul category with linearly versioned data, aka. versioned yul ports.

encodeP'x :: forall a b r.
  YulO3 r a b =>
  YulCat Pure a b ->
  (P'P r a ⊸ P'P r b)
encodeP'x c = MkP'x . encode c . unP'x

decodeP'x :: forall a b.
  YulO2 a b =>
  (forall r. YulO1 r => P'P r a ⊸ P'P r b) ->
  YulCat Pure a b
decodeP'x f = decode (\a -> unP'x (f (MkP'x a)))

------------------------------------------------------------------------------------------------------------------------

extendType'l :: forall a r.
  (YulO3 a (ABITypeDerivedOf a) r) =>
  P'P r (ABITypeDerivedOf a) ⊸ P'P r a
extendType'l = encodeP'x YulExtendType
