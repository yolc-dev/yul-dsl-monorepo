module YulDSL.Haskell.Effects.LinearSMC.YulPort
  ( -- * Yul Port Definitions
    -- $LinearPortDefs
    PortEffect (PurePort, VersionedPort)
  , P'x (MkP'x), P'V, P'P, unP'x, encode'x, decode'x
  , ver'l
  , unsafeCoerceYulPort, unsafeCoerceYulPortDiagram
    -- * General Yul Port Operations
    -- $GeneralOps
  , discard'l, ignore'l, mkUnit'l, emb'l, const'l, dup2'l, merge'l, split'l
    -- * Type Operations
    -- $TypeOps
  , coerceType'l, reduceType'l, extendType'l, cons'l, uncons'l
  ) where
-- linear-base
import Prelude.Linear
import Unsafe.Linear                       qualified as UnsafeLinear
-- linear-smc
import Control.Category.Linear             (P, copy, decode, discard, encode, ignore, merge, mkUnit, split)
-- yul-dsl
import YulDSL.Core
import YulDSL.StdBuiltIns.ValueType        ()
--
import Control.Category.Constrained.YulDSL ()
import Data.MPOrd


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

-- | Linear port of yul category with pure data, aka. pure yul ports.
type P'P = P'x PurePort

-- | Linear port of yul category with linearly versioned data, aka. versioned yul ports.
type P'V v = P'x (VersionedPort v)

unP'x :: P'x eff r a ⊸ P (YulCat PortEffect) r a
unP'x (MkP'x x) = x

encode'x :: forall (eff :: PortEffect) a b r. YulO3 r a b
  => YulCat PortEffect a b
  ⊸ (P'x eff r a ⊸ P'x eff r b)
encode'x c (MkP'x a) = MkP'x $ encode c a

decode'x :: forall (eff :: PortEffect) a b. YulO2 a b
  => (forall r. YulO1 r => P'x eff r a ⊸ P'x eff r b)
  -> YulCat PortEffect a b
decode'x f = decode (\a -> unP'x (f (MkP'x a)))

-- | Pure port can be converted to any versioned port.
ver'l :: forall a v r. YulO2 a r
      => P'P r a ⊸ P'V v r a
ver'l = unsafeCoerceYulPort

-- | Unsafe coerce yul port' effects.
unsafeCoerceYulPort :: forall (eff1 :: PortEffect) (eff2 :: PortEffect) r a.
  P'x eff1 r a ⊸ P'x eff2 r a
unsafeCoerceYulPort = UnsafeLinear.coerce

-- | Unsafe coerce yul port diagram's effects.
unsafeCoerceYulPortDiagram :: forall (eff1 :: PortEffect) (eff2 :: PortEffect) (eff3 :: PortEffect) r a b.
    (P'x eff1 r a ⊸ P'x eff2 r b) ⊸ (P'x eff3 r a ⊸ P'x eff3 r b)
unsafeCoerceYulPortDiagram f x = unsafeCoerceYulPort (f (unsafeCoerceYulPort x))

------------------------------------------------------------------------------------------------------------------------
-- $GeneralOps
--
-- Note: Yul ports are defined above as "P'*", and a "yul port diagram" is a linear function from input yul port to a
-- output yul port.
------------------------------------------------------------------------------------------------------------------------

discard'l :: forall a eff r. YulO2 r a
  => P'x eff r a ⊸ P'x eff r ()
discard'l (MkP'x a) = MkP'x $ discard a

ignore'l :: forall a eff r. YulO2 r a
  => P'x eff r () ⊸ P'x eff r a ⊸ P'x eff r a
ignore'l (MkP'x u) (MkP'x a) = MkP'x $ ignore u a

mkUnit'l :: forall a eff r. YulO2 r a
  => P'x eff r a ⊸ (P'x eff r a, P'x eff r ())
mkUnit'l (MkP'x a) = mkUnit a & \ (a', u) -> (MkP'x a', MkP'x u)

-- | Embed a free value to a yul port diagram that discards any input yul ports.
emb'l :: forall a b eff r. YulO3 r a b
  => a -> (P'x eff r b ⊸ P'x eff r a)
emb'l a (MkP'x b) = MkP'x $ encode (YulEmb a) (discard b)

-- | Create a constant yul port diagram that discards any input yul ports.
const'l :: forall a b eff r. YulO3 r a b
  => P'x eff r a ⊸ (P'x eff r b ⊸ P'x eff r a)
const'l (MkP'x a) (MkP'x b) = MkP'x $ ignore (discard b) a

-- | Duplicate the input yul port twice as a tuple.
dup2'l :: forall a eff r. YulO2 a r
  => P'x eff r a ⊸ (P'x eff r a, P'x eff r a)
dup2'l (MkP'x a) = let !(a1, a2) = split (copy a) in (MkP'x a1, MkP'x a2)

merge'l :: forall a b eff r. YulO3 r a b
  => (P'x eff r a, P'x eff r b) ⊸ P'x eff r (a, b)
merge'l (MkP'x a, MkP'x b) = MkP'x $ merge (a, b)

split'l :: forall a b eff r. YulO3 r a b
  => P'x eff r (a, b) ⊸ (P'x eff r a, P'x eff r b)
split'l (MkP'x ab) = let !(a, b) = split ab in (MkP'x a, MkP'x b)

------------------------------------------------------------------------------------------------------------------------
-- $TypeOps
------------------------------------------------------------------------------------------------------------------------

-- | Coerce input yul port to an ABI coercible output yul port.
coerceType'l :: forall a b eff r. (YulO3 a b r, ABITypeCoercible a b)
         => P'x eff r a ⊸ P'x eff r b
coerceType'l = encode'x YulCoerceType

reduceType'l :: forall a eff r. (YulO3 a (ABITypeDerivedOf a) r)
         => P'x eff r a ⊸ P'x eff r (ABITypeDerivedOf a)
reduceType'l = encode'x YulReduceType

extendType'l :: forall a eff r. (YulO3 a (ABITypeDerivedOf a) r)
         => P'x eff r (ABITypeDerivedOf a) ⊸ P'x eff r a
extendType'l = encode'x YulExtendType

-- | Prepend an element to a 'NP'.
cons'l :: forall x xs eff r. YulO3 x (NP xs) r
       => P'x eff r x ⊸ P'x eff r (NP xs) ⊸ P'x eff r (NP (x:xs))
cons'l x xs = coerceType'l (merge'l (x, xs))

-- | Split a 'NP' into its first element and the rest.
uncons'l :: forall x xs eff r. YulO3 x (NP xs) r
         => P'x eff r (NP (x:xs)) ⊸ (P'x eff r x, P'x eff r (NP xs))
uncons'l = split'l . coerceType'l

------------------------------------------------------------------------------------------------------------------------

--
-- 'MPEq' instance for the yul ports.
--

instance (YulO1 r, ValidINTx s n) => MPEq (P'x eff r (INTx s n)) (P'x eff r BOOL) where
  a == b = encode'x (YulJmpB (MkYulBuiltIn @"__cmp_eq_t_")) (merge'l (a, b))
  a /= b = encode'x (YulJmpB (MkYulBuiltIn @"__cmp_ne_t_")) (merge'l (a, b))

-- | 'MPOrd' instance for the yul ports.
instance (YulO1 r, ValidINTx s n) => MPOrd (P'x eff r (INTx s n)) (P'x eff r BOOL) where
  a  < b = encode'x (YulJmpB (MkYulBuiltIn @"__cmp_lt_t_")) (merge'l (a, b))
  a <= b = encode'x (YulJmpB (MkYulBuiltIn @"__cmp_le_t_")) (merge'l (a, b))
  a  > b = encode'x (YulJmpB (MkYulBuiltIn @"__cmp_gt_t_")) (merge'l (a, b))
  a >= b = encode'x (YulJmpB (MkYulBuiltIn @"__cmp_ge_t_")) (merge'l (a, b))

--
-- Num instances for (P'x eff r)
--

instance (YulO1 r, ValidINTx s n) => Additive (P'x eff r (INTx s n)) where
  a + b = encode'x (YulJmpB (MkYulBuiltIn @"__checked_add_t_")) (merge'l (a, b))

instance (YulO1 r, ValidINTx s n) => AddIdentity (P'x eff r (INTx s n)) where
  -- Note: uni-port is forbidden in linear-smc, but linear-base AdditiveGroup requires this instance.
  zero = error "unit is undefined for linear ports"

instance (YulO1 r, ValidINTx s n) => AdditiveGroup (P'x eff r (INTx s n)) where
  a - b = encode'x (YulJmpB (MkYulBuiltIn @"__checked_sub_t_")) (merge'l (a, b))

instance (YulO1 r, ValidINTx s n) => Multiplicative (P'x eff r (INTx s n)) where
  a * b = encode'x (YulJmpB (MkYulBuiltIn @"__checked_mul_t_")) (merge'l (a, b))
