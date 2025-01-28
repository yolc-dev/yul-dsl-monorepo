module YulDSL.Haskell.Effects.LinearSMC.YulPort
  ( -- * Yul Port Definitions
    -- $LinearPortDefs
    PortEffect (PurePort, VersionedPort), EffectVersionDelta, P'x, P'V, P'P
  , ver'l, unsafeCoerce'l
    -- * General Yul Port Operations
    -- $GeneralOps
  , emb'l, const'l, dup2'l, yulKeccak256'l
    -- * Type Operations
    -- $TypeOps
  , coerceType'l, reduceType'l, extendType'l, cons'l, uncons'l
  ) where
-- linear-base
import Prelude.Linear
import Unsafe.Linear                       qualified as UnsafeLinear
-- linear-smc
import Control.Category.Linear
-- yul-dsl
import YulDSL.Core
import YulDSL.StdBuiltIns.ABICodec         ()
import YulDSL.StdBuiltIns.ValueType        ()
-- yul-dsl-pure
import YulDSL.Haskell.Effects.Pure
--
import Control.Category.Constrained.YulDSL ()
import Data.MPOrd


------------------------------------------------------------------------------------------------------------------------
-- $LinearPortDefs
------------------------------------------------------------------------------------------------------------------------

-- | Various types of port effects for the yul port API.
data PortEffect = PurePort          -- ^ Pure port that does not need to be versioned
                | VersionedPort Nat -- ^ Linearly versioned port

type EffectVersionDelta :: eff -> Nat
type family EffectVersionDelta eff :: Nat where
  EffectVersionDelta Pure = 0
  EffectVersionDelta Total = 0
  EffectVersionDelta PurePort = 0
  EffectVersionDelta (VersionedPort vd) = vd

type instance IsEffectNotPure (eff :: PortEffect) = True
type instance MayEffectWorld  (eff :: PortEffect) = True


-- type role P'x phantom
-- | Linear port of yul categories with the port effect kind, aka. yul ports.
-- newtype P'x (eff :: PortEffect) r a = P'x (P (YulCat eff) r a)
type P'x (eff :: PortEffect) = P (YulCat eff)

-- | Linear port of yul category with pure data, aka. pure yul ports.
type P'P = P'x PurePort

-- | Linear port of yul category with linearly versioned data, aka. versioned yul ports.
type P'V v = P'x (VersionedPort v)

-- | Pure port can be converted to any versioned port.
ver'l :: forall a v r. YulO2 a r
      => P'P r a ⊸ P'V v r a
ver'l = unsafeCoerce'l

unsafeCoerce'l :: forall eff1 eff2 r a. P'x eff1 r a ⊸ P'x eff2 r a
unsafeCoerce'l = UnsafeLinear.coerce

------------------------------------------------------------------------------------------------------------------------
-- $GeneralOps
--
-- Note: Yul ports are defined above as "P'*", and a "yul port diagram" is a linear function from input yul port to a
-- output yul port.
------------------------------------------------------------------------------------------------------------------------

-- | Embed a free value to a yul port diagram that discards any input yul ports.
emb'l :: forall a b eff r. YulO3 a b r
      => a -> (P'x eff r b ⊸ P'x eff r a)
emb'l a = encode (YulEmb a) . discard

-- | Create a constant yul port diagram that discards any input yul ports.
const'l :: forall a b eff r. (YulO3 a b r)
        => P'x eff r a ⊸ (P'x eff r b ⊸ P'x eff r a)
const'l = flip (ignore . discard)

-- | Duplicate the input yul port twice as a tuple.
dup2'l :: forall a eff r. YulO2 a r
       => P'x eff r a ⊸ (P'x eff r a, P'x eff r a)
dup2'l = split . copy

yulKeccak256'l :: forall a eff r. YulO2 r a => P'x eff r a ⊸ P'x eff r B32
yulKeccak256'l = encode (YulJmpB (MkYulBuiltIn @"__keccak_c_" @a @B32))

------------------------------------------------------------------------------------------------------------------------
-- $TypeOps
------------------------------------------------------------------------------------------------------------------------

-- | Coerce input yul port to an ABI coercible output yul port.
coerceType'l :: forall a b eff r. (YulO3 a b r, ABITypeCoercible a b)
         => P'x eff r a ⊸ P'x eff r b
coerceType'l = encode YulCoerceType

reduceType'l :: forall a eff r. (YulO3 a (ABITypeDerivedOf a) r)
         => P'x eff r a ⊸ P'x eff r (ABITypeDerivedOf a)
reduceType'l = encode YulReduceType

extendType'l :: forall a eff r. (YulO3 a (ABITypeDerivedOf a) r)
         => P'x eff r (ABITypeDerivedOf a) ⊸ P'x eff r a
extendType'l = encode YulExtendType

-- | Prepend an element to a 'NP'.
cons'l :: forall x xs eff r. YulO3 x (NP xs) r
       => P'x eff r x ⊸ P'x eff r (NP xs) ⊸ P'x eff r (NP (x:xs))
cons'l x xs = coerceType'l (merge (x, xs))

-- | Split a 'NP' into its first element and the rest.
uncons'l :: forall x xs eff r. YulO3 x (NP xs) r
         => P'x eff r (NP (x:xs)) ⊸ (P'x eff r x, P'x eff r (NP xs))
uncons'l = split . coerceType'l

------------------------------------------------------------------------------------------------------------------------

--
-- 'MPEq' instance for the yul ports.
--

instance (YulO1 r, ValidINTx s n) => MPEq (P'x eff r (INTx s n)) (P'x eff r BOOL) where
  a == b = encode (YulJmpB (MkYulBuiltIn @"__cmp_eq_t_")) (merge (a, b))
  a /= b = encode (YulJmpB (MkYulBuiltIn @"__cmp_ne_t_")) (merge (a, b))

-- | 'MPOrd' instance for the yul ports.
instance (YulO1 r, ValidINTx s n) => MPOrd (P'x eff r (INTx s n)) (P'x eff r BOOL) where
  a  < b = encode (YulJmpB (MkYulBuiltIn @"__cmp_lt_t_")) (merge (a, b))
  a <= b = encode (YulJmpB (MkYulBuiltIn @"__cmp_le_t_")) (merge (a, b))
  a  > b = encode (YulJmpB (MkYulBuiltIn @"__cmp_gt_t_")) (merge (a, b))
  a >= b = encode (YulJmpB (MkYulBuiltIn @"__cmp_ge_t_")) (merge (a, b))

--
-- Num instances for (P'x eff r)
--

instance (YulO1 r, ValidINTx s n) => Additive (P'x eff r (INTx s n)) where
  a + b = encode (YulJmpB (MkYulBuiltIn @"__checked_add_t_")) (merge (a, b))

instance (YulO1 r, ValidINTx s n) => AddIdentity (P'x eff r (INTx s n)) where
  -- Note: uni-port is forbidden in linear-smc, but linear-base AdditiveGroup requires this instance.
  zero = error "unit is undefined for linear ports"

instance (YulO1 r, ValidINTx s n) => AdditiveGroup (P'x eff r (INTx s n)) where
  a - b = encode (YulJmpB (MkYulBuiltIn @"__checked_sub_t_")) (merge (a, b))

instance (YulO1 r, ValidINTx s n) => Multiplicative (P'x eff r (INTx s n)) where
  a * b = encode (YulJmpB (MkYulBuiltIn @"__checked_mul_t_")) (merge (a, b))

-- instance (YulO1 r, ValidINTx s n) => FromInteger (P'V v r (INTx s n)) where
--   fromInteger = UnsafeLinear.toLinear BasePrelude.fromInteger
