{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TemplateHaskell     #-}
{-|

Copyright   : (c) 2024-2025 Miao, ZhiCheng
License     : LGPL-3
Maintainer  : hellwolf@yolc.dev
Stability   : experimental

= Description

This module provides the definition of yul ports and their operations.

-}
module YulDSL.Haskell.Effects.LinearSMC.YulPort
  ( -- $YulPortDefs
    PortEffect (PurePort, VersionedPort)
  , P'x (MkP'x), unP'x, P'V, P'P, encodeP'x, decodeP'x
  , VersionableYulPort (ver'l)
  , unsafeCoerceYulPort, unsafeCoerceYulPortDiagram
    -- $GeneralOps
  , discard'l, ignore'l, mkUnit'l, emb'l, const'l, dup2'l, merge'l, split'l
  , with'l
  , uncurryNP'lx
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
--
-- The linear-smc library provides so-called port API @P k r a@, where @k@ is a smc category and @a@ is an object in
-- that category. It can encode a morphism in @k@ from @a ↝ b@ to its port diagram @P k r a ⊸ P k r b@, and decode it back.
--
-- Yul port applies the yul category and kinds of linear yul effects on top of the port API.
------------------------------------------------------------------------------------------------------------------------

-- | Various kinds of effects for the yul ports.
data PortEffect = PurePort          -- ^ Pure port that does not need to be versioned
                | VersionedPort Nat -- ^ Linearly versioned port

-- | An intermediate linear effect kind for encoding and decoding yul ports.
data LinearEffectX
type instance IsEffectNonPure LinearEffectX = True
type instance MayAffectWorld  LinearEffectX = True

-- | Yul port with the port effect kind, aka. yul ports.
newtype P'x (eff :: PortEffect) r a = MkP'x (P (YulCat LinearEffectX) r a)
-- ^ Role annotation to make sure @eff@ is nominal, so only unsafe coercing is allowed.
type role P'x nominal nominal nominal

-- | Peel off the P'x wrapper for the underlying port. It is a standalone declaration to have the linear arrow.
unP'x :: forall (eff :: PortEffect) r a. P'x eff r a ⊸ P (YulCat LinearEffectX) r a
unP'x (MkP'x x) = x

-- | Yul port with pure data, aka. pure yul ports.
type P'P = P'x PurePort

-- | Yul port with linearly versioned data, aka. versioned yul ports.
type P'V v = P'x (VersionedPort v)

-- | Encode a yul morphism of intermediate linear effect kind to its yul port diagram.
encodeP'x :: forall (ioe :: PortEffect) a b.
  YulO2 a b =>
  YulCat LinearEffectX a b ->
  (forall r. YulO1 r => P'x ioe r a ⊸ P'x ioe r b)
encodeP'x c = MkP'x . encode c . unP'x

-- | Decode a yul port diagram back to its yul morphism.
decodeP'x :: forall (ioe :: PortEffect) a b.
  YulO2 a b =>
  (forall r. YulO1 r => P'x ioe r a ⊸ P'x ioe r b) ->
  YulCat LinearEffectX a b
decodeP'x f = decode (\a -> unP'x (f (MkP'x a)))

-- | Yul port that can be versioned to its compatible version.
class VersionableYulPort ioe v where
  -- | Version a yul port to a compatible versioned port.
  ver'l :: forall a r. YulO2 a r => P'x ioe r a ⊸ P'V v r a
-- ^ A versioned port is stuck with it version.
instance VersionableYulPort (VersionedPort v) v where ver'l = id
-- ^ A pure port can be versioned to any other version.
instance VersionableYulPort PurePort v where ver'l = unsafeCoerceYulPort

-- | Unsafe coerce yul port' effects.
unsafeCoerceYulPort :: forall (eff1 :: PortEffect) (eff2 :: PortEffect) r a.
  P'x eff1 r a ⊸ P'x eff2 r a
unsafeCoerceYulPort = MkP'x . unP'x

-- | Unsafe coerce yul port diagram's effects.
unsafeCoerceYulPortDiagram :: forall (eff1 :: PortEffect) (eff2 :: PortEffect) (eff3 :: PortEffect) r a b.
  (P'x eff1 r a ⊸ P'x eff2 r b) ⊸ (P'x eff3 r a ⊸ P'x eff3 r b)
unsafeCoerceYulPortDiagram f x = unsafeCoerceYulPort (f (unsafeCoerceYulPort x))

------------------------------------------------------------------------------------------------------------------------
-- $GeneralOps
-- = General Yul Port Operations
--
-- Note: Yul ports are defined above as "P'*", and a "yul port diagram" is a linear function from input yul port to a
-- output yul port.
------------------------------------------------------------------------------------------------------------------------

discard'l :: forall a eff r.
  YulO2 r a =>
  P'x eff r a ⊸ P'x eff r ()
discard'l = MkP'x . discard . unP'x

ignore'l :: forall a eff r.
  YulO2 r a =>
  P'x eff r () ⊸ P'x eff r a ⊸ P'x eff r a
ignore'l u a = MkP'x $ ignore (unP'x u) (unP'x a)

mkUnit'l :: forall a eff r.
  YulO2 r a =>
  P'x eff r a ⊸ (P'x eff r a, P'x eff r ())
mkUnit'l a = mkUnit (unP'x a) & \ (a', u) -> (MkP'x a', MkP'x u)

-- | Embed a free value to a yul port diagram that discards any input yul ports.
emb'l :: forall a b eff r.
  YulO3 r a b =>
  a -> (P'x eff r b ⊸ P'x eff r a)
emb'l a = MkP'x . encode (yulEmb a) . unP'x

-- | Create a constant yul port diagram that discards any input yul ports.
const'l :: forall a b eff r.
  YulO3 r a b =>
  P'x eff r a ⊸ (P'x eff r b ⊸ P'x eff r a)
const'l a b = MkP'x $ ignore (discard (unP'x b)) (unP'x a)

-- | Duplicate the input yul port twice as a tuple.
dup2'l :: forall a eff r.
  YulO2 a r =>
  P'x eff r a ⊸ (P'x eff r a, P'x eff r a)
dup2'l a = let !(a1, a2) = (split . copy . unP'x) a in (MkP'x a1, MkP'x a2)

merge'l :: forall a b eff r.
  YulO3 r a b =>
  (P'x eff r a, P'x eff r b) ⊸ P'x eff r (a, b)
merge'l (a, b) = MkP'x $ merge (unP'x a, unP'x b)

split'l :: forall a b eff r.
  YulO3 r a b =>
  P'x eff r (a, b) ⊸ (P'x eff r a, P'x eff r b)
split'l ab = let !(a, b) = split (unP'x ab) in (MkP'x a, MkP'x b)

-- TODO: move to LinearYulCat as its internal function.
uncurryNP'lx :: forall m1 m1b m2_ m2b_ m2' m2b' g x xs b r a ie.
  ( YulO4 x (NP xs) r a
  , UncurriableNP g xs b m1 m1b (m2_ a) (m2b_ a) One
  --
  , P'x ie r ~ m1
  , m1 ~ m2'
  , m1b ~ m2b'
  ) =>
  (m1 x ⊸ LiftFunction g m1 m1b One) ->      -- ^ f: m1 x ⊸ m1 (xs ⊸...) ⊸ m1b b; the function to be uncurried
  (m2' a ⊸ m2' (NP (x : xs))) ->             -- ^ h: m2' (a ⊸ NP xxs)
  ((m2' a ⊸ m2' (NP xs)) ⊸ m2_ a (NP xs)) -> -- ^ mk: m2' (a ⊸ NP xs) ⊸ m2_ a (NP xs)
  (m2b_ a b ⊸ (m2' a ⊸ m2b' b)) ->           -- ^ un: m2b_ a b ⊸ (m2' a ⊸ m2b' b)
  (m2' a ⊸ m2b' b)
uncurryNP'lx f h mk un a =
  let !(a1, a2) = dup2'l a
      !(x, xs) = unconsNP (h a1)
  in let g = uncurryNP @g @xs @b @m1 @m1b @(m2_ a) @(m2b_ a) @One
             (f x)
             (mk (\a' -> ignore'l (discard'l a') xs))
     in (un g) a2

-- | Process TupleN of yul ports with a pure yul function.
with'l :: forall f x xs btpl bs r ioe m1 m2.
  ( YulO4 x (NP xs) btpl r
  -- m1, m2
  , P'x ioe r ~ m1
  , YulCat Pure (NP (x:xs)) ~ m2
  -- f
  , EquivalentNPOfFunction f (x:xs) btpl
  -- x:xs
  , ConvertibleNPtoTupleN (NP (MapList m1 (x:xs)))
  , LinearDistributiveNP m1 (x:xs)
  , UncurriableNP f (x:xs) btpl m2 m2 m2 m2 Many
  -- btpl, bs
  , TupleNtoNP btpl ~ NP bs
  , ConvertibleNPtoTupleN (NP (MapList m1 bs))
  , SingleCasePattern m1 btpl (NPtoTupleN (NP (MapList m1 bs))) YulCatObj One
  ) =>
  NPtoTupleN (NP (MapList m1 (x:xs))) ⊸
  PureY f ->
  NPtoTupleN (NP (MapList m1 bs))
with'l xxs f = is (encodeP'x cat' sxxs)
  where !(x, xs) = splitNonEmptyNP (fromTupleNtoNP xxs)
        !(x', u) = mkUnit'l x
        sxxs = linearDistributeNP (x' :* xs) u
        cat = uncurryNP @f @(x:xs) @btpl @m2 @m2 @m2 @m2 f YulId
        cat' = YulUnsafeCoerceEffect cat

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

instance YulO2 a r =>
         SingleCasePattern (P'x eff r) (Solo a) (Solo (P'x eff r a))
         YulCatObj One where
  is x = MkSolo (coerceType'l x)
instance YulO2 a r =>
         PatternMatchable (P'x eff r) (Solo a) (Solo (P'x eff r a))
         YulCatObj One where
  couldBe (MkSolo x) = coerceType'l x
-- Make injective pattern free from MkSolo.
instance YulO2 a r =>
         InjectivePattern (P'x eff r) (Solo a) (P'x eff r a)
         YulCatObj One where
  -- be (MkSolo x) = coerceType'l x
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
            -- NOTE! lots of let expression to workaround a GHC faulty warning related to unused variables.
            let mxxs_ = (coerceType'l . reduceType'l) mtpl_ in
            let !(mx1_, mxs_) = split'l mxxs_ in
            let mxs_' = extendType'l mxs_ :: $(BasePrelude.pure m) $(tupleNFromVarsT as) in
            let $(TH.bangP (TH.tupP (BasePrelude.fmap TH.varP xs))) = is mxs_'
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
