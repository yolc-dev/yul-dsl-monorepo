{-# LANGUAGE AllowAmbiguousTypes #-}
module YulDSL.Haskell.Effects.LinearSMC.YulPort
  ( -- * Yul Port Definitions
    -- $LinearPortDefs
    PortEffect (PurePort, VersionedPort)
  , P'x (MkP'x), P'V, P'P, unP'x, encodeP'x, decodeP'x
  , Versionable'L (ver'l)
  , unsafeCoerceYulPort, unsafeCoerceYulPortDiagram
  , unsafeUncurryNil'lx, uncurryNP'lx
    -- * General Yul Port Operations
    -- $GeneralOps
  , discard'l, ignore'l, mkUnit'l, emb'l, const'l, dup2'l, merge'l, split'l
    -- * Type Operations
    -- $TypeOps
  , coerceType'l, reduceType'l, extendType'l
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

encodeP'x :: forall (eff :: PortEffect) a b r. YulO3 r a b
  => YulCat PortEffect a b
  ⊸ (P'x eff r a ⊸ P'x eff r b)
encodeP'x c (MkP'x a) = MkP'x $ encode c a

decodeP'x :: forall (eff :: PortEffect) a b. YulO2 a b
  => (forall r. YulO1 r => P'x eff r a ⊸ P'x eff r b)
  -> YulCat PortEffect a b
decodeP'x f = decode (\a -> unP'x (f (MkP'x a)))

-- Versionable ports

class Versionable'L ie v where
  ver'l :: forall a r. YulO2 a r => P'x ie r a ⊸ P'V v r a

instance Versionable'L (VersionedPort v) v where
  ver'l = id

instance Versionable'L PurePort v where
  ver'l = unsafeCoerceYulPort

-- -- | Pure port can be converted to any versioned port.
-- ver'l :: forall a v r. YulO2 a r
--       => P'P r a ⊸ P'V v r a
-- ver'l = unsafeCoerceYulPort

-- | Unsafe coerce yul port' effects.
unsafeCoerceYulPort :: forall (eff1 :: PortEffect) (eff2 :: PortEffect) r a.
  P'x eff1 r a ⊸ P'x eff2 r a
unsafeCoerceYulPort = UnsafeLinear.coerce

-- | Unsafe coerce yul port diagram's effects.
unsafeCoerceYulPortDiagram :: forall (eff1 :: PortEffect) (eff2 :: PortEffect) (eff3 :: PortEffect) r a b.
    (P'x eff1 r a ⊸ P'x eff2 r b) ⊸ (P'x eff3 r a ⊸ P'x eff3 r b)
unsafeCoerceYulPortDiagram f x = unsafeCoerceYulPort (f (unsafeCoerceYulPort x))

-- uncurryNP'lx

unsafeUncurryNil'lx :: forall a b r ie oe m1.
  YulO3 a b r =>
  P'x oe r b ⊸
  (m1 a ⊸ P'x ie r (NP '[])) ->
  (m1 a ⊸ P'x oe r b)
unsafeUncurryNil'lx b h a =
  h a                   -- :: P'V v1 (NP '[])
  & coerceType'l @_ @() -- :: P'V v1 ()
  & unsafeCoerceYulPort -- :: P'V vn ()
  & \u -> ignore'l u b

uncurryNP'lx :: forall g x xs b m1 m1b m2_ m2b_ r a ie.
  ( YulO4 x (NP xs) r a
  , P'x ie r ~ m1
  , UncurryNP'Fst g ~ xs, UncurryNP'Snd g ~ b
  , LiftFunction b (m2_ a) (m2b_ a) One ~ (m2b_ a) b
  , UncurryingNP g xs b m1 m1b (m2_ a) (m2b_ a) One
  , YulCatObj (NP xs)
  ) =>
  (m1 x ⊸ LiftFunction g m1 m1b One) ->      -- f
  (m1 a ⊸ m1 (NP (x : xs))) ->               -- h
  ((m1 a ⊸ m1 (NP xs)) ⊸ (m2_ a) (NP xs)) -> -- mk
  ((m2b_ a) b ⊸ (m1 a ⊸ m1b b)) ->           -- un
  (m1 a ⊸ m1b b)
uncurryNP'lx f h mk un xxs =
  dup2'l xxs
  & \(xxs1, xxs2) -> unconsNP (h xxs1)
  & \(x, xs) -> let g = uncurryingNP @g @xs @b @m1 @m1b @(m2_ a) @(m2b_ a) @One
                        (f x)
                        (mk (\a -> ignore'l (discard'l a) xs))
                in (un g) xxs2

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
coerceType'l :: forall a b eff r. (YulO3 a b r, ABITypeCoercible a b) =>
  P'x eff r a ⊸ P'x eff r b
coerceType'l = encodeP'x YulCoerceType

reduceType'l :: forall a eff r. (YulO3 a (ABITypeDerivedOf a) r) =>
  P'x eff r a ⊸ P'x eff r (ABITypeDerivedOf a)
reduceType'l = encodeP'x YulReduceType

extendType'l :: forall a eff r. (YulO3 a (ABITypeDerivedOf a) r) =>
  P'x eff r (ABITypeDerivedOf a) ⊸ P'x eff r a
extendType'l = encodeP'x YulExtendType

--
-- NP type
--

instance YulO3 x (NP xs) r => ConstructibleNP (P'x eff r) x xs One where
  consNP x xs = coerceType'l (merge'l (x, xs))
  unconsNP = split'l . coerceType'l

instance YulO1 r => LinearTraversableNP (P'x eff r) '[] where
  linearSequenceNP snil = (Nil, coerceType'l snil)
instance YulO1 r => LinearDistributiveNP (P'x eff r) '[] where
  linearDistributeNP Nil = coerceType'l
instance (YulO3 x (NP xs) r , LinearTraversableNP (P'x eff r) xs) => LinearTraversableNP (P'x eff r) (x:xs)
instance (YulO3 x (NP xs) r , LinearDistributiveNP (P'x eff r) xs) => LinearDistributiveNP (P'x eff r) (x:xs)

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
--

instance (YulO1 r, ValidINTx s n) => Additive (P'x eff r (INTx s n)) where
  a + b = encodeP'x (YulJmpB (MkYulBuiltIn @"__checked_add_t_")) (merge'l (a, b))

instance (YulO1 r, ValidINTx s n) => AddIdentity (P'x eff r (INTx s n)) where
  -- Note: uni-port is forbidden in linear-smc, but linear-base AdditiveGroup requires this instance.
  zero = error "unit is undefined for linear ports"

instance (YulO1 r, ValidINTx s n) => AdditiveGroup (P'x eff r (INTx s n)) where
  a - b = encodeP'x (YulJmpB (MkYulBuiltIn @"__checked_sub_t_")) (merge'l (a, b))

instance (YulO1 r, ValidINTx s n) => Multiplicative (P'x eff r (INTx s n)) where
  a * b = encodeP'x (YulJmpB (MkYulBuiltIn @"__checked_mul_t_")) (merge'l (a, b))
