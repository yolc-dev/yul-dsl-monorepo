{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TemplateHaskell     #-}
module YulDSL.Haskell.Effects.LinearSMC.YulPort
  ( -- * Yul Port Definitions
    -- $LinearPortDefs
    P'P (MkP'x), unP'x, encodeP'x, decodeP'x, keccak256'l
    -- * General Yul Port Operations
    -- $GeneralOps
    -- * Type Operations
    -- $TypeOps
  , extendType'l
  , lfn'
    -- $PureEffectKind
    -- $PureFn
  , PureFn (MkPureFn)
  , pureFn
  ) where
-- linear-base
import Prelude.Linear
-- linear-smc
import Control.Category.Linear             (P, decode, encode)
-- yul-dsl-pure

import YulDSL.Core

import Control.Category.Constrained.YulDSL ()
import YulDSL.Core.YulCat


--

lfn' :: forall b xs.
  ( YulO2 (NP '[ADDR]) b
  , '[ADDR] ~ xs   -- crash stops after removing this line
  ) =>
  (forall r. YulO1 r => P'P r (NP '[ADDR]) ⊸ P'P r b) ->
  PureFn
lfn' f = MkPureFn (decodeP'x f)


------------------------------------------------------------------------------------------------------------------------
-- $LinearPortDefs
------------------------------------------------------------------------------------------------------------------------



-- | Linear port of yul categories with the port effect kind, aka. yul ports.
newtype P'P r a = MkP'x (P (YulCat ) r a)

unP'x :: forall r a. P'P r a ⊸ P (YulCat ) r a
unP'x (MkP'x x) = x


-- | Linear port of yul category with linearly versioned data, aka. versioned yul ports.

encodeP'x :: forall a b r.
  YulO3 r a b =>
  YulCat a b ->
  (P'P r a ⊸ P'P r b)
encodeP'x c = MkP'x . encode c . unP'x

decodeP'x :: forall  b.
  YulO2 (NP '[ADDR]) b =>
  (forall r. YulO1 r => P'P r (NP '[ADDR]) ⊸ P'P r b) ->
  YulCat (NP '[ADDR]) b
decodeP'x f = decode (\a -> unP'x (f (MkP'x a)))

------------------------------------------------------------------------------------------------------------------------

extendType'l :: forall a r.
  (YulO3 a (ABITypeDerivedOf a) r) =>
  P'P r (ABITypeDerivedOf a) ⊸ P'P r a
extendType'l = encodeP'x YulExtendType

keccak256'l :: forall a r. YulO2 r a => P'P r a ⊸ P'P r B32
keccak256'l = encodeP'x YulJmpB

data PureFn where
  MkPureFn :: forall xs b. YulCat (NP xs) b -> PureFn

pureFn :: PureFn -> String
pureFn (MkPureFn fn) = yulCatCompactShow fn
