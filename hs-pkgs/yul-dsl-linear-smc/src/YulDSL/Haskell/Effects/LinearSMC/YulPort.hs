{-# LANGUAGE UndecidableInstances #-}
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
  , P'x (MkP'x), unP'x, P'V, P'P
  , VersionableYulPort (ver'l)
  , encodeP'x, decodeP'x
  , unsafeCoerceYulPort, unsafeCoerceYulPortDiagram
    -- $TypeOps
  , coerceType'l, reduceType'l, extendType'l
    -- $GeneralOps
  , discard'l, ignore'l, mkunit'l, emb'l, const'l, dup'l, merge'l, split'l
    -- $PureLam
  , PureLamNP_L, purelamNP'l, PureLamN_L, purelamN'l
    -- control flows
  , bool'l
    -- $VersionThread
  , VersionThread, vtstart, vtstart_, vtstop, vtreturn, vtmkunit, vtgulp, vtseq
  ) where
-- base
import Control.Monad                       (replicateM)
import GHC.TypeLits                        (type (<=))
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
-- * Yul Port Definitions
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

-- | Yul port that can be versioned to its compatible version.
class VersionableYulPort ioe v where
  -- | Version a yul port to a compatible versioned port.
  ver'l :: forall a r. YulO2 a r => P'x ioe r a ⊸ P'V v r a
-- ^ A versioned port is stuck with it version.
instance VersionableYulPort (VersionedPort v) v where ver'l = id
-- ^ A pure port can be versioned to any other version.
instance VersionableYulPort PurePort v where ver'l = unsafeCoerceYulPort

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

-- | Unsafe coerce yul port' effects.
unsafeCoerceYulPort :: forall (eff1 :: PortEffect) (eff2 :: PortEffect) r a.
  P'x eff1 r a ⊸ P'x eff2 r a
unsafeCoerceYulPort = MkP'x . unP'x

-- | Unsafe coerce yul port diagram's effects.
unsafeCoerceYulPortDiagram :: forall (eff1 :: PortEffect) (eff2 :: PortEffect) (eff3 :: PortEffect) r a b.
  (P'x eff1 r a ⊸ P'x eff2 r b) ⊸ (P'x eff3 r a ⊸ P'x eff3 r b)
unsafeCoerceYulPortDiagram f x = unsafeCoerceYulPort (f (unsafeCoerceYulPort x))

------------------------------------------------------------------------------------------------------------------------
-- $TypeOps
-- * Yul Port Type Operations
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

------------------------------------------------------------------------------------------------------------------------
-- $GeneralOps
-- * General Yul Port Operations
--
-- Note: Yul ports are defined above as "P'*", and a "yul port diagram" is a linear function from input yul port to a
-- output yul port.
------------------------------------------------------------------------------------------------------------------------

-- | Discard a yul port.
discard'l :: forall a eff r.
  YulO2 r a =>
  P'x eff r a ⊸ P'x eff r ()
discard'l = MkP'x . discard . unP'x

-- | Ignore a unit yul port by returning an actual yul port.
ignore'l :: forall a eff r.
  YulO2 r a =>
  P'x eff r () ⊸ P'x eff r a ⊸ P'x eff r a
ignore'l u a = MkP'x $ ignore (unP'x u) (unP'x a)

-- | Create a unit yul port with the help of another yul port.
mkunit'l :: forall a eff r.
  YulO2 r a =>
  P'x eff r a ⊸ (P'x eff r a, P'x eff r ())
mkunit'l a = mkUnit (unP'x a) & \ (a', u) -> (MkP'x a', MkP'x u)

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

-- | Duplicate the input yul port.
dup'l :: forall a eff r.
  YulO2 a r =>
  P'x eff r a ⊸ (P'x eff r a, P'x eff r a)
dup'l a = let !(a1, a2) = (split . copy . unP'x) a in (MkP'x a1, MkP'x a2)

-- | Merge two yul ports into one yul port of their product.
merge'l :: forall a b eff r.
  YulO3 r a b =>
  (P'x eff r a, P'x eff r b) ⊸ P'x eff r (a, b)
merge'l (a, b) = MkP'x $ merge (unP'x a, unP'x b)

-- | Split a yul port of product into two separated ports.
split'l :: forall a b eff r.
  YulO3 r a b =>
  P'x eff r (a, b) ⊸ (P'x eff r a, P'x eff r b)
split'l ab = let !(a, b) = split (unP'x ab) in (MkP'x a, MkP'x b)

------------------------------------------------------------------------------------------------------------------------
-- $PureLam
-- * Process Yul Ports In Pure Lambdas
--
-- Using yul port APIs involves threading (linearly, metaphorically speaking) of the ports. Manually doing such
-- threading can quickly becomes a toll on the users. The family of "with" functions are provided to capture some ports
-- in a continuation of pure yul function, which provides a greater syntactical freedom to the users without sacrificing
-- any safety, then eventually returns a set of new yul ports.
------------------------------------------------------------------------------------------------------------------------

-- | Constraint alias required for 'purelamNP\'l'.
type PureLamNP_L x xs b bs m1 m2 r ioe =
  ( YulO5 x (NP I xs) b (NP I bs) r
    -- m1, m2
  , P'x ioe r ~ m1
  , YulCat Pure (NP I (x:xs)) ~ m2
    -- x:xs
  , LinearTraversableNP m1 (x:xs)
  , DistributiveNP m2 (x:xs)
    -- b:bs
  , LinearDistributiveNP m1 (b:bs)
  )

-- | Process a NP of yul ports with a pure yul lambda.
purelamNP'l :: forall x xs b bs m1 m2 r ioe.
  PureLamNP_L x xs b bs m1 m2 r ioe =>
  NP m1 (x:xs) ⊸
  (NP m2 (x:xs) -> m2 (NP I (b:bs))) ->
  NP m1 (b:bs)
purelamNP'l xxs_np f =
  let sxxs = lsequence_NonEmptyNP xxs_np
      sbbs = encodeP'x (YulUnsafeCoerceEffect (f (distribute_NP YulId))) sxxs
  in ldistribute_NonEmptyNP sbbs

-- | Constraint alias required for 'purelamN\'l'.
type PureLamN_L x xs b bs m1 m2 r ioe =
  ( YulO1 (TupleN (b:bs))
  , PureLamNP_L x xs b bs m1 m2 r ioe
  , ConvertibleNPtoTupleN m1 (NP m1 (x:xs))
  , ConvertibleNPtoTupleN m1 (NP m1 (b:bs))
  , UncurriableNPDistributed (x:xs) (TupleN (b:bs)) m2 m2 m2 m2 Many
  , NP I (b:bs) ~ ABITypeDerivedOf (TupleN (b:bs))
  )

-- | Process a tupleN of yul ports with a pure yul lambda.
purelamN'l :: forall x xs b bs m1 m2 r ioe.
  PureLamN_L x xs b bs m1 m2 r ioe =>
  TupleN_M m1 (x:xs) ⊸
  CurryNP (NP m2 (x:xs)) (m2 (TupleN (b:bs))) Many ->
  TupleN_M m1 (b:bs)
purelamN'l xxs_tpl f = fromNPtoTupleN (purelamNP'l (fromTupleNtoNP xxs_tpl) f')
  where f' xxs_np = uncurryNPDistributed @m2 @m2 @m2 @m2 @Many @(x:xs) @(TupleN (b:bs)) f xxs_np
          >.> YulReduceType

------------------------------------------------------------------------------------------------------------------------
-- $ControlFlows
------------------------------------------------------------------------------------------------------------------------

-- | Yul port boolean switch.
bool'l :: forall xs b ioe r.
  ( YulO3 (NP I xs) b r
  , LinearTraversableNP (P'x ioe r) xs
  )=>
  P'x ioe r BOOL ⊸
  NP (P'x ioe r) xs ⊸
  (forall r1. YulO1 r1 => P'x ioe r1 (NP I xs) ⊸ P'x ioe r1 b) ->
  (forall r2. YulO1 r2 => P'x ioe r2 (NP I xs) ⊸ P'x ioe r2 b) ->
  P'x ioe r b
bool'l b xs ga gb =
  encodeP'x g (lsequence_NonEmptyNP (b :* xs))
  where
    gc :: forall r3. YulO1 r3 =>
      P'x ioe r3 (NP I (BOOL:xs)) ⊸ P'x ioe r3 BOOL
    gc bxs = let !(b', xs') = luncons_NP bxs in ignore'l (discard'l xs') b'
    gh :: forall r1. YulO1 r1 =>
      (P'x ioe r1 (NP I xs) ⊸ P'x ioe r1 b) ->
      (P'x ioe r1 (NP I (BOOL:xs)) ⊸ P'x ioe r1 b)
    gh h bxs = let !(b', xs') = luncons_NP bxs in h (ignore'l (discard'l b') xs')
    g = YulSwitch ((decodeP'x gc) >.> yulSafeCast) [(1, decodeP'x (gh ga)), (0, decodeP'x (gh gb))] yulRevert

------------------------------------------------------------------------------------------------------------------------
-- $VersionThread
-- * Yul Port Version Thread
--
-- A convenient device to threading yul ports.
------------------------------------------------------------------------------------------------------------------------

-- | A machinery to work with yul port units.
newtype VersionThread r = MkVersionThread (P'P r ())
type role VersionThread nominal

-- | Start a version thread from a catalytic input port and replicate the input too.
vtstart :: forall ie a r. YulO2 a r => P'x ie r a ⊸ (VersionThread r, P'x ie r a)
vtstart a = let !(a1, a2) = dup'l a in (MkVersionThread (unsafeCoerceYulPort (discard'l a1)), a2)

-- | Start a version thread from a catalytic input port and discard the input.
vtstart_ :: forall ie a r. YulO2 a r => P'x ie r a ⊸ VersionThread r
vtstart_ a = MkVersionThread (unsafeCoerceYulPort (discard'l a))

-- | Stop the version thread and return a waste port to be collected.
vtstop :: forall r. VersionThread r ⊸ P'P r ()
vtstop (MkVersionThread u) = u

-- | Stop the version thread and replace the waste port with a port to be returned.
vtreturn :: forall a oe r. YulO2 a r => VersionThread r ⊸ P'x oe r a ⊸ P'x oe r a
vtreturn vt a = const'l a (unsafeCoerceYulPort (vtstop vt))

-- | Create a new yul port unit from the version thread, which can be used to thread other ports.
vtmkunit :: forall eff r. YulO1 r => VersionThread r ⊸ (VersionThread r, P'x eff r ())
vtmkunit (MkVersionThread u) = let !(u1, u2) = dup'l u in (MkVersionThread u1, unsafeCoerceYulPort u2)

-- | Gulp an input yul port into a version thread.
vtgulp :: forall eff r a. YulO2 r a => VersionThread r ⊸ P'x eff r a ⊸ VersionThread r
vtgulp (MkVersionThread u) x = MkVersionThread (ignore'l u (unsafeCoerceYulPort (discard'l x)))

-- | Thread the yul port @a@ before the yul port @b, where "@a <= b@"
--
-- Note:
--
-- * Its name is inspired by the family of "seq": seq, pseq, lseq, etc.
--
-- * Threading is important when dealing with ports generated from side effects.
vtseq :: forall a b va vb r.
  (va <= vb, YulO3 a b r) =>
  VersionThread r ⊸ P'V va r a ⊸ P'V vb r b ⊸ (VersionThread r, P'V vb r b)
vtseq vt a b =
  let vt' = vtgulp vt a
      !(vt'', u) = vtmkunit vt'
  in (vt'', ignore'l u b)

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
-- NP
--

instance YulO1 r => LinearlyConstructibleNP (P'x eff r) YulCatObj where
  lunit2nil_NP = coerceType'l
  ldiscard_NP = discard'l
  lignore_NP = ignore'l
  lmkunit_NP = mkunit'l
  lcons_NP x xs = coerceType'l (merge'l (x, xs))
  luncons_NP = split'l . coerceType'l

--
-- TupleN
--

-- Tuple1 is Solo and special.

instance YulO2 a r =>
         SingleCasePattern (P'x eff r) (Solo a) (P'x eff r a)
         YulCatObj One where
  is = coerceType'l
instance YulO2 a r =>
         PatternMatchable (P'x eff r) (Solo a) (P'x eff r a)
         YulCatObj One where
-- Make injective pattern free from MkSolo.
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
         SingleCasePattern
         (P'x eff r)
         (a1, a2, a3)
         (P'x eff r a1, P'x eff r a2, P'x eff r a3)
         YulCatObj One where
  is mtpl =
    let mxxs = (coerceType'l . reduceType'l) mtpl
        !(mx1, mxs) = split'l mxxs
        mxs' = extendType'l mxs :: P'x eff r (a2, a3)
        !(mx2, mx3) = is mxs'
    in (mx1, mx2, mx3)
instance (YulO4 a1 a2 a3 r) =>
         PatternMatchable
         (P'x eff r)
         (a1, a2, a3)
         (P'x eff r a1, P'x eff r a2, P'x eff r a3)
         YulCatObj One
instance (YulO4 a1 a2 a3 r) =>
         InjectivePattern
         (P'x eff r)
         (a1, a2, a3)
         (P'x eff r a1, P'x eff r a2, P'x eff r a3)
         YulCatObj One where
  be (mx1, mx2, mx3) =
    let mxs = be (mx2, mx3) :: P'x eff r (a2, a3)
        mxs' = reduceType'l mxs
    in (extendType'l . coerceType'l . merge'l) (mx1, mxs')

-- Tuple{[4..15]} instances

do
  let mkT_YulO1 = (TH.conT ''YulO1 `TH.appT`)
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
    [d| instance ( $(tupleNFromVarsTWith mkT_YulO1 (r : a : as))
                 , SingleCasePattern $(BasePrelude.pure m)
                                     $(tupleNFromVarsT (a:as))
                                     $(tupleNFromVarsTWith (BasePrelude.pure m `TH.appT`) (a:as))
                                     YulCatObj One
                 ) =>
                 SingleCasePattern $(BasePrelude.pure m)
                                   $(tupleNFromVarsT (a:as))
                                   $(tupleNFromVarsTWith (BasePrelude.pure m `TH.appT`) (a:as))
                                   YulCatObj One where
          is mtpl_ =
            -- NOTE! lots of let expression to workaround a GHC faulty warning related to unused variables.
            let mxxs_ = (coerceType'l . reduceType'l) mtpl_ in
            let !(mx1_, mxs_) = split'l mxxs_ in
            let mxs_' = extendType'l mxs_ :: $(BasePrelude.pure m) $(tupleNFromVarsT as) in
            let $(TH.bangP (TH.tupP (BasePrelude.fmap TH.varP xs))) = is mxs_'
            in $(TH.tupE (TH.varE 'mx1_ : BasePrelude.fmap TH.varE xs))

        instance $(tupleNFromVarsTWith mkT_YulO1 (r : a : as)) =>
                 PatternMatchable $(BasePrelude.pure m)
                                  $(tupleNFromVarsT (a : as))
                                  $(tupleNFromVarsTWith (BasePrelude.pure m `TH.appT`) (a : as))
                                  YulCatObj One

        instance $(tupleNFromVarsTWith mkT_YulO1 (r : a : as)) =>
                 InjectivePattern $(BasePrelude.pure m)
                                  $(tupleNFromVarsT (a : as))
                                  $(tupleNFromVarsTWith (BasePrelude.pure m `TH.appT`) (a : as))
                                  YulCatObj One where
          be $(TH.tupP (BasePrelude.fmap TH.varP (x : xs))) =
            let mxs_ = $(TH.varE 'be `TH.appE` TH.tupE (BasePrelude.fmap TH.varE xs))
                      :: $(BasePrelude.pure m) $(tupleNFromVarsT as)
                mxs_' = reduceType'l mxs_
            in (extendType'l . coerceType'l . merge'l) ($(TH.varE x), mxs_')
      |]) [4..16]
  BasePrelude.pure (concat insts)
