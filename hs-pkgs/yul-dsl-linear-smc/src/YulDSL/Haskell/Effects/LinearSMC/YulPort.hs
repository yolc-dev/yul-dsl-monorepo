{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TemplateHaskell     #-}
module YulDSL.Haskell.Effects.LinearSMC.YulPort
  ( -- * Yul Port Definitions
    -- $LinearPortDefs
    PortEffect (PurePort, VersionedPort)
  , P'x (MkP'x), unP'x, P'V, P'P, encodeP'x, decodeP'x
  , unsafeCoerceYulPort, unsafeCoerceYulPortDiagram
    -- * General Yul Port Operations
    -- $GeneralOps
  , discard'l, ignore'l, mkUnit'l, dup2'l
    -- * Type Operations
    -- $TypeOps
  , coerceType'l, extendType'l
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
type P'V v = P'x (VersionedPort v)

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

-- uncurryNP'lx

------------------------------------------------------------------------------------------------------------------------
-- $GeneralOps
--
-- Note: Yul ports are defined above as "P'*", and a "yul port diagram" is a linear function from input yul port to a
-- output yul port.
------------------------------------------------------------------------------------------------------------------------

discard'l :: forall a eff r. YulO2 r a
  => P'x eff r a ⊸ P'x eff r ()
discard'l = MkP'x . discard . unP'x

ignore'l :: forall a eff r. YulO2 r a
  => P'x eff r () ⊸ P'x eff r a ⊸ P'x eff r a
ignore'l u a = MkP'x $ ignore (unP'x u) (unP'x a)

mkUnit'l :: forall a eff r. YulO2 r a
  => P'x eff r a ⊸ (P'x eff r a, P'x eff r ())
mkUnit'l a = mkUnit (unP'x a) & \ (a', u) -> (MkP'x a', MkP'x u)

-- | Embed a free value to a yul port diagram that discards any input yul ports.
emb'l :: forall a b eff r. YulO3 r a b
  => a -> (P'x eff r b ⊸ P'x eff r a)
emb'l a = MkP'x . encode (yulEmb a) . unP'x

-- | Create a constant yul port diagram that discards any input yul ports.
const'l :: forall a b eff r. YulO3 r a b
  => P'x eff r a ⊸ (P'x eff r b ⊸ P'x eff r a)
const'l a b = MkP'x $ ignore (discard (unP'x b)) (unP'x a)

-- | Duplicate the input yul port twice as a tuple.
dup2'l :: forall a eff r. YulO2 a r
  => P'x eff r a ⊸ (P'x eff r a, P'x eff r a)
dup2'l a = let !(a1, a2) = (split . copy . unP'x) a in (MkP'x a1, MkP'x a2)

merge'l :: forall a b eff r. YulO3 r a b
  => (P'x eff r a, P'x eff r b) ⊸ P'x eff r (a, b)
merge'l (a, b) = MkP'x $ merge (unP'x a, unP'x b)

split'l :: forall a b eff r. YulO3 r a b
  => P'x eff r (a, b) ⊸ (P'x eff r a, P'x eff r b)
split'l ab = let !(a, b) = split (unP'x ab) in (MkP'x a, MkP'x b)

------------------------------------------------------------------------------------------------------------------------
-- $TypeOps
------------------------------------------------------------------------------------------------------------------------

-- | Coerce input yul port to an ABI coercible output yul port.
coerceType'l :: forall a b eff r.
  (YulO3 a b r, ABITypeCoercible a b) =>
  P'x eff r a ⊸ P'x eff r b
coerceType'l = encodeP'x YulCoerceType

extendType'l :: forall a eff r.
  (YulO3 a (ABITypeDerivedOf a) r) =>
  P'x eff r (ABITypeDerivedOf a) ⊸ P'x eff r a
extendType'l = encodeP'x YulExtendType

--
-- NP type
--

instance YulO3 x (NP xs) r => ConstructibleNP (P'x eff r) x xs One where
  consNP x xs = coerceType'l (merge'l (x, xs))
  unconsNP = split'l . coerceType'l


------------------------------------------------------------------------------------------------------------------------
-- Instances
------------------------------------------------------------------------------------------------------------------------

--
-- 'MPEq' instance for the yul ports.
--

instance (YulO1 r, ValidINTx s n) => MPEq (P'x eff r (INTx s n)) (P'x eff r BOOL) where
  a == b = encodeP'x (YulJmpB (MkYulBuiltIn @"__cmp_eq_t_")) (merge'l (a, b))
  a /= b = encodeP'x (YulJmpB (MkYulBuiltIn @"__cmp_ne_t_")) (merge'l (a, b))

-- | 'MPOrd' instance for the yul ports.
instance (YulO1 r, ValidINTx s n) => MPOrd (P'x eff r (INTx s n)) (P'x eff r BOOL) where
  a  < b = encodeP'x (YulJmpB (MkYulBuiltIn @"__cmp_lt_t_")) (merge'l (a, b))
  a <= b = encodeP'x (YulJmpB (MkYulBuiltIn @"__cmp_le_t_")) (merge'l (a, b))
  a  > b = encodeP'x (YulJmpB (MkYulBuiltIn @"__cmp_gt_t_")) (merge'l (a, b))
  a >= b = encodeP'x (YulJmpB (MkYulBuiltIn @"__cmp_ge_t_")) (merge'l (a, b))

--
-- Num instances for (P'x eff r)
