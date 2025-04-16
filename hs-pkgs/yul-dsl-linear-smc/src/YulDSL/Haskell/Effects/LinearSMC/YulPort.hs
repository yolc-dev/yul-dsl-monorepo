{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TemplateHaskell     #-}
module YulDSL.Haskell.Effects.LinearSMC.YulPort
  ( -- $YulPortDefs
    PortEffect (PurePort, VersionedPort)
  , P'x (MkP'x), unP'x, P'V, P'P, encodeP'x, decodeP'x
  , Versionable'L (ver'l)
  , unsafeCoerceYulPort, unsafeCoerceYulPortDiagram
  , unsafeUncurryNil'lx, uncurryNP'lx
    -- $GeneralOps
  , discard'l, ignore'l, mkUnit'l, emb'l, const'l, dup2'l, merge'l, split'l
    -- $TypeOps
  , coerceType'l, reduceType'l, extendType'l
    -- $YulPortUniter
  , YulPortUniter (MkYulPortUniter), yulPortUniterMkUnit, yulPortUniterGulp
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
-- $YulPortDefs
-- = Yul Port Definitions
------------------------------------------------------------------------------------------------------------------------

-- | Various types of port effects for the yul port API.
data PortEffect = PurePort          -- ^ Pure port that does not need to be versioned
                | VersionedPort Nat -- ^ Linearly versioned port

-- | An intermediate linear effect kind for encodeP and decodeP to work with.
data LinearEffectX
type instance IsEffectNonPure LinearEffectX = True
type instance MayAffectWorld  LinearEffectX = True

-- | Linear port of yul categories with the port effect kind, aka. yul ports.
newtype P'x (eff :: PortEffect) r a = MkP'x (P (YulCat LinearEffectX) r a)
-- ^ Role annotation to make sure @eff@ is nominal, so only unsafe coercing is allowed.
type role P'x nominal nominal nominal

unP'x :: forall (eff :: PortEffect) r a. P'x eff r a ⊸ P (YulCat LinearEffectX) r a
unP'x (MkP'x x) = x

-- | Linear port of yul category with pure data, aka. pure yul ports.
type P'P = P'x PurePort

-- | Linear port of yul category with linearly versioned data, aka. versioned yul ports.
type P'V v = P'x (VersionedPort v)

encodeP'x :: forall (eff :: PortEffect) a b r.
  YulO3 r a b =>
  YulCat LinearEffectX a b ->
  (P'x eff r a ⊸ P'x eff r b)
encodeP'x c = MkP'x . encode c . unP'x

decodeP'x :: forall (eff :: PortEffect) a b.
  YulO2 a b =>
  (forall r. YulO1 r => P'x eff r a ⊸ P'x eff r b) ->
  YulCat LinearEffectX a b
decodeP'x f = decode (\a -> unP'x (f (MkP'x a)))

-- | Unsafe coerce yul port' effects.
unsafeCoerceYulPort :: forall (eff1 :: PortEffect) (eff2 :: PortEffect) r a.
  P'x eff1 r a ⊸ P'x eff2 r a
unsafeCoerceYulPort = MkP'x . unP'x

-- | Unsafe coerce yul port diagram's effects.
unsafeCoerceYulPortDiagram :: forall (eff1 :: PortEffect) (eff2 :: PortEffect) (eff3 :: PortEffect) r a b.
  (P'x eff1 r a ⊸ P'x eff2 r b) ⊸ (P'x eff3 r a ⊸ P'x eff3 r b)
unsafeCoerceYulPortDiagram f x = unsafeCoerceYulPort (f (unsafeCoerceYulPort x))

-- Versionable ports

class Versionable'L ie v where
  ver'l :: forall a r. YulO2 a r => P'x ie r a ⊸ P'V v r a

instance Versionable'L (VersionedPort v) v where
  ver'l = id

instance Versionable'L PurePort v where
  ver'l = unsafeCoerceYulPort

-- uncurryNP'lx

unsafeUncurryNil'lx :: forall a b r ie oe m1.
  YulO3 a b r =>
  P'x oe r b ⊸
  (m1 a ⊸ P'x ie r (NP '[])) ⊸
  (m1 a ⊸ P'x oe r b)
unsafeUncurryNil'lx b h a =
  h a                   -- :: P'V v1 (NP '[])
  & coerceType'l @_ @() -- :: P'V v1 ()
  & unsafeCoerceYulPort -- :: P'V vn ()
  & \u -> ignore'l u b

uncurryNP'lx :: forall m1 m1b m2 m2b g x xs b r a ie.
  ( YulO4 x (NP xs) r a
  , EquivalentNPOfFunction g xs b
  , P'x ie r ~ m1
  , LiftFunction b (m2 a) (m2b a) One ~ (m2b a) b
  , UncurriableNP g xs b m1 m1b (m2 a) (m2b a) One
  , YulCatObj (NP xs)
  ) =>
  (m1 x ⊸ LiftFunction g m1 m1b One) ⊸   -- ^ f: m1 (x -> xs ->... -> b), the function to be uncurried
  (m1 a ⊸ m1 (NP (x : xs))) ⊸            -- ^ h: m1 (a ⊸ NP xxs)
  ((m1 a ⊸ m1 (NP xs)) ⊸ m2 a (NP xs)) ⊸ -- ^ mk: m1 (a ⊸ NP xs) ⊸ m2 a (NP xs)
  (m2b a b ⊸ (m1 a ⊸ m1b b)) ⊸           -- ^ un: m2b a b ⊸ (m1 a ⊸ m1b b)
  (m1 a ⊸ m1b b)
uncurryNP'lx f h mk un a =
  dup2'l a
  & \(a1, a2) -> unconsNP @m1 @x @xs @One (h a1)
  & \(x, xs) -> let g = uncurryNP @g @xs @b @m1 @m1b @(m2 a) @(m2b a) @One
                        (f x)
                        (mk (\a' -> ignore'l (discard'l a') xs))
                in (un g) a2

------------------------------------------------------------------------------------------------------------------------
-- $GeneralOps
-- = General YulPort Operations
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
-- = Yul Port Type Operations
------------------------------------------------------------------------------------------------------------------------

-- | Coerce input yul port to an ABI coercible output yul port.
coerceType'l :: forall a b eff r.
  (YulO3 a b r, ABITypeCoercible a b) =>
  P'x eff r a ⊸ P'x eff r b
coerceType'l = encodeP'x YulCoerceType

reduceType'l :: forall a eff r.
  (YulO3 a (ABITypeDerivedOf a) r) =>
  P'x eff r a ⊸ P'x eff r (ABITypeDerivedOf a)
reduceType'l = encodeP'x YulReduceType

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

instance YulO1 r => LinearTraversableNP (P'x eff r) '[] where
  linearSequenceNP snil = (Nil, coerceType'l snil)
instance YulO1 r => LinearDistributiveNP (P'x eff r) '[] where
  linearDistributeNP Nil = coerceType'l
instance (YulO3 x (NP xs) r , LinearTraversableNP (P'x eff r) xs) => LinearTraversableNP (P'x eff r) (x:xs)
instance (YulO3 x (NP xs) r , LinearDistributiveNP (P'x eff r) xs) => LinearDistributiveNP (P'x eff r) (x:xs)

--------------------------------------------------------------------------------
-- $YulPortUniter
--------------------------------------------------------------------------------

-- | A machinery to work with yul port units.
newtype YulPortUniter r = MkYulPortUniter (P'P r ())

-- | Create a new yul port unit from the uniter.
yulPortUniterMkUnit :: forall eff r. YulO1 r => YulPortUniter r ⊸ (YulPortUniter r, P'x eff r ())
yulPortUniterMkUnit (MkYulPortUniter u) = let !(u1, u2) = dup2'l u in (MkYulPortUniter u1, unsafeCoerceYulPort u2)

-- | Gulp an input yul port by the uniter.
yulPortUniterGulp :: forall eff r a. YulO2 r a => YulPortUniter r ⊸ P'x eff r a ⊸ YulPortUniter r
yulPortUniterGulp (MkYulPortUniter u) x = MkYulPortUniter (ignore'l u (unsafeCoerceYulPort (discard'l x)))

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

--
-- TupleN
--

-- Tuple1 is Solo and special.

instance (YulO2 a r) =>
         SingleCasePattern (P'x eff r) (Solo a) (P'x eff r a)
         YulCatObj One where
  is = coerceType'l
instance (YulO2 a r, YulCat eff r ~ m) =>
         PatternMatchable (P'x eff r) (Solo a) (P'x eff r a)
         YulCatObj One where
instance YulO2 a r =>
         InjectivePattern (P'x eff r) (Solo a) (P'x eff r a)
         YulCatObj One where
  be = coerceType'l

-- Tuple2 is the base case.

instance (YulO3 a1 a2 r) =>
         SingleCasePattern (P'x eff r) (a1, a2) (P'x eff r a1, P'x eff r a2)
         YulCatObj One where
  is = split'l
instance (YulO3 a1 a2 r) =>
         PatternMatchable (P'x eff r) (a1, a2) (P'x eff r a1, P'x eff r a2)
         YulCatObj One
instance (YulO3 a1 a2 r, P'x eff r ~ m) =>
         InjectivePattern (P'x eff r) (a1, a2) (P'x eff r a1, P'x eff r a2)
         YulCatObj One where
  be = merge'l

-- Tuple3 code is the example for the TH to mimic how to generate more instances inductively:

instance (YulO4 a1 a2 a3 r) =>
         SingleCasePattern (P'x eff r) (a1, a2, a3) (P'x eff r a1, P'x eff r a2, P'x eff r a3)
         YulCatObj One where
  is mtpl =
    let mxxs = (coerceType'l . reduceType'l) mtpl
        !(mx1, mxs) = split'l mxxs
        mxs' = extendType'l mxs :: P'x eff r (a2, a3)
        !(mx2, mx3) = is mxs'
    in (mx1, mx2, mx3)
instance (YulO4 a1 a2 a3 r) =>
         PatternMatchable (P'x eff r) (a1, a2, a3) (P'x eff r a1, P'x eff r a2, P'x eff r a3)
         YulCatObj One
instance (YulO4 a1 a2 a3 r) =>
         InjectivePattern (P'x eff r) (a1, a2, a3) (P'x eff r a1, P'x eff r a2, P'x eff r a3)
         YulCatObj One where
  be (mx1, mx2, mx3) =
    let mxs = be (mx2, mx3) :: P'x eff r (a2, a3)
        mxs' = reduceType'l mxs
    in (extendType'l . coerceType'l . merge'l) (mx1, mxs')

-- Tuple{[4..15]} instances

do
  insts <- BasePrelude.mapM (\n -> do
    -- type variables: r, a, as...
    r <- TH.newName "r"
    a <- TH.newName "a"
    as <- replicateM (n - 1) (TH.newName "a")
    -- term variables: x, xs...
    x <- TH.newName "x"
    xs <- replicateM (n - 1) (TH.newName "x")
    -- m
    m <- [t| P'x $(TH.varT BasePrelude.=<< TH.newName "eff") $(TH.varT r) |]
    [d| instance ( $(tupleNFromVarsTWith (TH.conT ''YulO1 `TH.appT`) (r : a : as))
                 , SingleCasePattern $(BasePrelude.pure m)
                                     $(tupleNFromVarsT as)
                                     $(tupleNFromVarsTWith (BasePrelude.pure m `TH.appT`) as)
                                     YulCatObj One
                 ) =>
                 SingleCasePattern $(BasePrelude.pure m)
                                   $(tupleNFromVarsT (a : as))
                                   $(tupleNFromVarsTWith (BasePrelude.pure m `TH.appT`) (a : as))
                                   YulCatObj One where
          is mtpl_ =
            let mxxs_ = (coerceType'l . reduceType'l) mtpl_
                !(mx1_, mxs_) = split'l mxxs_
                mxs_' = extendType'l mxs_ :: $(BasePrelude.pure m) $(tupleNFromVarsT as)
                $(TH.bangP (TH.tupP (BasePrelude.fmap TH.varP xs))) = is mxs_'
            in $(TH.tupE (TH.varE 'mx1_ : BasePrelude.fmap TH.varE xs))

        instance $(tupleNFromVarsTWith (TH.conT ''YulO1 `TH.appT`) (r : a : as)) =>
                 PatternMatchable $(BasePrelude.pure m)
                                  $(tupleNFromVarsT (a : as))
                                  $(tupleNFromVarsTWith (BasePrelude.pure m `TH.appT`) (a : as))
                                  YulCatObj One

        instance $(tupleNFromVarsTWith (TH.conT ''YulO1 `TH.appT`) (r : a : as)) =>
                 InjectivePattern $(BasePrelude.pure m) $(tupleNFromVarsT (a : as))
                                  $(tupleNFromVarsTWith (BasePrelude.pure m `TH.appT`) (a : as))
                                  YulCatObj One where
          be $(TH.tupP (BasePrelude.fmap TH.varP (x : xs))) =
            let mxs_ = $(TH.varE 'be `TH.appE` TH.tupE (BasePrelude.fmap TH.varE xs))
                      :: $(BasePrelude.pure m) $(tupleNFromVarsT as)
                mxs_' = reduceType'l mxs_
            in (extendType'l . coerceType'l . merge'l) ($(TH.varE x), mxs_')
      |]) [4..15]
  BasePrelude.pure (concat insts)
