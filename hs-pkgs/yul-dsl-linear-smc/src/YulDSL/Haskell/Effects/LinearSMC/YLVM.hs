{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances   #-}
{-|

Copyright   : (c) 2024-2025 Miao, ZhiCheng
License     : LGPL-3
Maintainer  : hellwolf@yolc.dev
Stability   : experimental

= Description

This module provides the linearly-versioned monad (LVM) for yul ports, aka. YLVM.

-}
module YulDSL.Haskell.Effects.LinearSMC.YLVM
  ( -- * YLVM: A Linearly Versioned Monad for Yul Ports
    -- $YLVM
    YLVM, runYLVM
  , ygulp, yrunvt
    -- * Yul Variable Reference's API
    -- $YulVarRefAPI
  , LinearlyVersionRestrictedYulPort, DereferenceYulVarRef, ReferenciableYulVar
  , Ur (Ur), unur, Uv, Rv
  , VersionableYulVarRef (ver)
    -- ** Make And Take Of Yul Variables
  , YulVarRef (ymkvar, ytkvar, ytkvarv), YulVarRefNP (ymkvarNP, ytkvarNP), ytkuvN, ytkrvN
  , yembed, yreturn
    -- ** Process With Pure Functions
  , ywithuv, ywithuv_1, ywithrv, ywithrv_1
    -- * Control Flow With YLVM
    -- $ControlFlows
  , ywhen
    -- $YLVMDiagrams
    -- * Create YLVM Monadic Diagrams
  , YulCat'LPPM (MkYulCat'LPPM), YulCat'LPVM (MkYulCat'LPVM), YulCat'LVVM (MkYulCat'LVVM)
  , ylvm'pp, ylvm'pv, ylvm'vv
    -- * Re-export LVM Primitives
  , module Control.LinearlyVersionedMonad.Combinators
  , module Control.LinearlyVersionedMonad.LVMVar
  ) where
-- base
import GHC.TypeError                                 qualified as TypeError
import GHC.TypeLits                                  (type (<=))
-- linear-base
import Prelude.Linear
import Unsafe.Linear                                 qualified as UnsafeLinear
-- constraints
import Data.Constraint                               (Dict (Dict))
-- yul-dsl-pure
import YulDSL.Haskell.LibPure
-- linearly-versioned-monad
import Control.LinearlyVersionedMonad.Combinators
import Control.LinearlyVersionedMonad.LVM            (LVM (MkLVM), runLVM, unLVM)
import Control.LinearlyVersionedMonad.LVM            qualified as LVM
import Control.LinearlyVersionedMonad.LVMVar
import Data.LinearContext
--
import YulDSL.Haskell.Effects.LinearSMC.LinearYulCat
import YulDSL.Haskell.Effects.LinearSMC.YulPort


------------------------------------------------------------------------------------------------------------------------
-- $YLVM
------------------------------------------------------------------------------------------------------------------------

-- | YLVM is a linear versioned monad with 'YLVMCtx' as its context data.
type YLVM va vb r = LVM (YLVMCtx r) va vb

-- | Run a YLVM with an initial unit yul port and returns a versioned yul port.
runYLVM :: forall b vb r ie.
  (KnownNat vb, YulO2 r b) =>
  P'x ie r () ⊸ YLVM 0 vb r (P'V vb r b) ⊸ P'V vb r b
runYLVM u m =
  let ctx = mk_ylvm_ctx u
      !(ctx', b) = runLVM ctx mWrapper
      u' = rm_ylvm_ctx ctx'
  in const'l b u'
  where -- wrap given monad with var registry init/consume block
    mWrapper = LVM.do
      initRgstr :: YLVM 0 0 r (Ur ())
      b <- m
      consumeRgstr
      LVM.pure b
    -- initialize the var registry
    initRgstr = MkLVM \(MkYLVMCtx vt mbRgstr) ->
      let rgstr = case mbRgstr of
            Nothing -> initLVMVarRegistry
            err     -> lseq (error "nonsense" :: Ur ()) (UnsafeLinear.coerce err)
      in (Dict, MkYLVMCtx vt (Just rgstr), Ur ())
      -- consume the var registry
    consumeRgstr = with_yulvar_registry \rgstr -> LVM.do
      consumeLVMVarRegistry rgstr
      LVM.pure (Nothing, Ur ())

-- | Gulp a yul port and produce a haskell unit.
ygulp :: forall a v r ie.
  (KnownNat v, YulO2 a r) =>
  P'x ie r a ⊸  YLVM v v r ()
ygulp a = MkLVM \(MkYLVMCtx vt mbRgstr) -> let vt' = vtgulp vt a in (Dict, MkYLVMCtx vt' mbRgstr, ())

-- | Run a version-thread function inside the 'YLVM'.
yrunvt :: forall b va vb r.
  (KnownNat va, KnownNat vb, va <= vb) =>
  (VersionThread r ⊸ (VersionThread r, b)) ⊸ YLVM va vb r b
yrunvt f = MkLVM \(MkYLVMCtx vt mbRgstr) -> let !(vt', b) = f vt in (Dict, MkYLVMCtx vt' mbRgstr, b)

--
-- Working with YLVM Context
--

-- YLVMCtx
--

-- | Context needed for the LVM to be a 'YLVM'.
data YLVMCtx r where
  -- ^ All arrows are linear so that no yul ports can escape.
  MkYLVMCtx ::
    VersionThread r          ⊸ -- ^ A version thread for the yul ports.
    Maybe (YulVarRegistry r) ⊸ -- ^ An operating (Just) or consumed (Nothing) YulVar registry.
    YLVMCtx r

mk_ylvm_ctx :: forall ioe r. YulO1 r => P'x ioe r () ⊸ YLVMCtx r
mk_ylvm_ctx u = MkYLVMCtx (vtstart_ u) Nothing

rm_ylvm_ctx :: forall ioe r. YulO1 r => YLVMCtx r ⊸ P'x ioe r ()
rm_ylvm_ctx (MkYLVMCtx vt mbRgstr) =
  case mbRgstr of
    Nothing -> ()
    err     -> lseq (error "rm_ylvm_ctx: registry not consumed" :: ()) (UnsafeLinear.coerce err)
  `lseq` unsafeCoerceYulPort (vtstop vt)

-- YulVarRegistry
--

type YulVarRegistry r = LVMVarRegistry (YLVMCtx r)

-- The internal api to handle yulvar registry in a continuation.
with_yulvar_registry :: forall b v r.
  (KnownNat v, YulO1 r) =>
  (YulVarRegistry r ⊸ YLVM v v r (Maybe (YulVarRegistry r), b)) ⊸
  YLVM v v r b
with_yulvar_registry f = MkLVM \(MkYLVMCtx vt mbRgstr) ->
  let ctx' = MkYLVMCtx vt Nothing {- passing the registry to the continuation directly -}
      !(dict, ctx'', (mbRgstr', b)) = case mbRgstr of
        Just rgstr -> unLVM (f rgstr) ctx'
        Nothing    -> lseq (error "registry was destroyed" :: ()) (UnsafeLinear.coerce (f, ctx'))
      vt' = case ctx'' of
        (MkYLVMCtx vt'' Nothing) -> vt''
        err                      -> lseq (error "nonsense" :: ()) (UnsafeLinear.coerce err)
  in (dict, MkYLVMCtx vt' mbRgstr', b)

-- ContextualConsumable
--

instance YulO2 r a => ContextualConsumable (YLVMCtx r) (P'x eff r) (P'x eff r a) where
  contextualConsume (MkYLVMCtx vt rgstr) x = MkYLVMCtx (vtgulp vt x) rgstr

-- Fine-grained ContextualSeqable specializations.
--

instance (YulO3 r a b) => ContextualSeqable (YLVMCtx r) (P'P r) (P'P r a) (P'P r) (P'P r b) where
  contextualSeq ctx a b = (ctx, const'l b a)

instance (YulO3 r a b) => ContextualSeqable (YLVMCtx r) (P'P r) (P'P r a) (P'V vb r) (P'V vb r b) where
  contextualSeq ctx a b = (ctx, const'l b (unsafeCoerceYulPort a))

instance (YulO3 r a b) => ContextualSeqable (YLVMCtx r) (P'V va r) (P'V va r a) (P'P r) (P'P r b) where
  contextualSeq ctx a b = (ctx, const'l b (unsafeCoerceYulPort a))

-- When both ports are versioned, it is important to thread them in the right sequence to avoid unsound out-of-order
-- side effects.
instance (KnownNat va, KnownNat vb, va <= vb, YulO3 r a b) =>
         ContextualSeqable (YLVMCtx r) (P'V va r) (P'V va r a) (P'V vb r) (P'V vb r b) where
  contextualSeq (MkYLVMCtx vt mbRgstr) a b =
    let !(vt', b') = vtseq vt a b
    in (MkYLVMCtx vt' mbRgstr, b')

-- ContextualDupable
--

instance YulO2 r a => ContextualDupable (YLVMCtx r) (P'x eff r) (P'x eff r a) where
  contextualDup ctx x = (ctx, dup'l x)

-- ContextualEmbeddable
--

instance YulO2 r a => ContextualEmbeddable (YLVMCtx r) (P'x eff r) a where
  contextualEmbed (MkYLVMCtx vt mbRgstr) x'p =
    let !(vt', u') = vtmkunit vt
        x'v = emb'l x'p u'
    in (MkYLVMCtx vt' mbRgstr, x'v)

-- LinearlyVersionRestrictable
--

instance (KnownNat v, YulO2 a r) => LinearlyVersionRestrictable v (YLVMCtx r) (P'P r a) where
  type instance VersionRestrictedData v (YLVMCtx r) (P'P r a) = P'V v r a
  restrictVersion = LVM.pure . unsafeCoerceYulPort

instance (KnownNat v, YulO2 a r) => LinearlyVersionRestrictable v (YLVMCtx r) (P'V v r a) where
  type instance VersionRestrictedData v (YLVMCtx r) (P'V v r a) = P'V v r a
  restrictVersion = LVM.pure

------------------------------------------------------------------------------------------------------------------------
-- $YulVarRefAPI
------------------------------------------------------------------------------------------------------------------------

type LinearlyVersionRestrictedYulPort v r port = VersionRestrictedData v (YLVMCtx r) port

type family DereferenceYulVarRef vref = port | port -> vref where
  DereferenceYulVarRef (Uv r a)   = P'P r a
  DereferenceYulVarRef (Rv v r a) = P'V v r a

type ReferenciableYulVar v r vref = (ReferenciableLVMVar v vref (YLVMCtx r) (DereferenceYulVarRef vref))

--
-- Uv
--

type UvYulVarRef r a = UvLVMVarRef (YLVMCtx r) (P'P r) (P'P r a)

-- | Unrestricted wrapper of 'UvYulVarRef' in two letters.
data Uv r a where
  Uv :: forall r a. UvYulVarRef r a -> Uv r a
type role Uv nominal nominal

instance (KnownNat v, YulO2 r a) => ReferenciableLVMVar v (Uv r a) (YLVMCtx r) (P'P r a) where
  takeLVMVarRef (Uv var) = takeLVMVarRef var

--
-- Rv
--

type RvYulVarRef v r a = RvLVMVarRef (YLVMCtx r) (P'V v r) v (P'V v r a)

-- | Unrestricted wrapper of 'RvYulVarRef' in two letters.
data Rv v r a where
  Rv  :: forall v r a. RvYulVarRef v r a -> Rv v r a
type role Rv nominal nominal nominal

instance (KnownNat v, YulO2 r a) => ReferenciableLVMVar v (Rv v r a) (YLVMCtx r) (P'V v r a) where
  takeLVMVarRef (Rv vref)       = takeLVMVarRef vref

--
-- VersionableYulVar (ver)
--

class (KnownNat v, YulO1 r) => VersionableYulVarRef v r vref_ | vref_ -> r where
  ver :: forall a. YulO1 a => vref_ a -> Rv v r a

instance (KnownNat v, YulO1 r) => VersionableYulVarRef v r (Uv r) where
  ver (Uv vref) = Rv (VerUvLVMVarRef vref)

instance (KnownNat v, YulO1 r) => VersionableYulVarRef v r (Rv v r) where
  ver = id

--
-- YulVarRef
--

-- | A unified interface to work with both 'Uv' and 'Rv'.
class (KnownNat v, YulO1 r) =>
      YulVarRef v r port_ vref_ | v port_ -> vref_, vref_ -> port_ where
  -- | Make a variable reference from a yul port.
  ymkvar :: forall a. YulO1 a => port_ a ⊸ YLVM v v r (Ur (vref_ a))
  -- | Take a yul port from a variable reference.
  ytkvar :: forall a. YulO1 a => vref_ a -> YLVM v v r (port_ a)
  -- | Take a version-restricted yul port from a variable reference.
  ytkvarv :: forall a. YulO1 a => vref_ a -> YLVM v v r (P'V v r a)

instance (KnownNat v, YulO1 r) => YulVarRef v r (P'P r) (Uv r) where
  ymkvar x = with_yulvar_registry \rgstr ->
    let !(Ur var, rgstr') = registerUvLVMVar x rgstr
    in LVM.pure (Just rgstr', Ur (Uv var))
  ytkvar (Uv vref) = with_yulvar_registry \rgstr -> LVM.do
    (port, rgstr') <- takeLVMVarRef vref rgstr
    LVM.pure (Just rgstr', port)
  ytkvarv uv = ytkvar (ver uv)

instance {-# OVERLAPPABLE #-}
  ( KnownNat va, YulO1 r
  , TypeError.Unsatisfiable (TypeError.Text "Outdated data version")
  ) =>
  YulVarRef va r (P'V v r) (Rv v r)

instance (KnownNat v, YulO1 r) => YulVarRef v r (P'V v r) (Rv v r) where
  ymkvar x = with_yulvar_registry \rgstr ->
    let !(Ur var, rgstr') = registerRvLVMVar x rgstr
    in LVM.pure (Just rgstr', Ur (Rv var))
  ytkvar (Rv vref) = with_yulvar_registry \rgstr -> LVM.do
    (port, rgstr') <- takevLVMVarRef vref rgstr
    LVM.pure (Just rgstr', port)
  ytkvarv = ytkvar

--
-- YulVarRefNP
--

class (YulVarRef v r port_ vref_, YulO1 (NP I xs)) => YulVarRefNP xs v r port_ vref_ where
  ymkvarNP :: forall. NP port_ xs ⊸ YLVM v v r (Ur (NP vref_ xs))
  ytkvarNP :: forall. NP vref_ xs -> YLVM v v r (NP port_ xs)

instance YulVarRef v r port_ vref_ => YulVarRefNP '[] v r port_ vref_ where
  ymkvarNP Nil = LVM.pure (Ur Nil)
  ytkvarNP Nil = LVM.pure Nil

instance ( YulO2 x (NP I xs)
         , YulVarRefNP xs v r port_ vref_
         ) => YulVarRefNP (x:xs) v r port_ vref_ where
  ymkvarNP (x :* xs) = LVM.do
    Ur xVar <- ymkvar x
    Ur xsVars <- ymkvarNP @xs @v @r @port_ @vref_ xs
    LVM.pure (Ur (xVar :* xsVars))

  ytkvarNP (xVar :* xsVars) = LVM.do
    x <- ytkvar xVar
    xs <- ytkvarNP @xs @v @r @port_ @vref_ xsVars
    LVM.pure (x :* xs)

--
-- ytkuvN, ytkrvN
--

ytkuvN :: forall xs v r m1 m2.
  ( Uv r ~ m1
  , P'P r ~ m2
  , ConvertibleNPtoTupleN m1 (NP m1 xs)
  , ConvertibleNPtoTupleN m2 (NP m2 xs)
  , YulVarRefNP xs v r m2 m1
  ) =>
  TupleN_M m1 xs ->
  YLVM v v r (TupleN_M m2 xs)
ytkuvN tpl = LVM.do
  aNP <- ytkvarNP (fromTupleNtoNP tpl)
  LVM.pure (fromNPtoTupleN aNP)

ytkrvN :: forall xs v r m1 m2.
  ( Rv v r ~ m1
  , P'V v r ~ m2
  , ConvertibleNPtoTupleN m1 (NP m1 xs)
  , ConvertibleNPtoTupleN m2 (NP m2 xs)
  , YulVarRefNP xs v r m2 m1
  ) =>
  TupleN_M m1 xs ->
  YLVM v v r (TupleN_M m2 xs)
ytkrvN tpl = LVM.do
  aNP <- ytkvarNP (fromTupleNtoNP tpl)
  LVM.pure (fromNPtoTupleN aNP)

--
-- yembed, yreturn
--

-- | Embed a value into a yul variable.
yembed :: forall a v r ie vref_.
  ( YulO1 a
  , YulVarRef v r (P'x ie r) vref_
  ) =>
  a -> YLVM v v r (Ur (vref_ a))
yembed a = embed a LVM.>>= ymkvar

-- | Return a yul variable unrestricted.
yreturn :: forall a v r ie vref_.
  ( YulO1 a
  , YulVarRef v r (P'x ie r) vref_
  ) =>
  vref_ a -> YLVM v v r (Ur (vref_ a))
yreturn a = LVM.pure (Ur a)

--
-- ywithuv{_1}, ywithrv{_1}
--

type ConstraintForYWith f x xs b bs bret f' v r m1 m2 mp =
  ( KnownNat v, YulO6 x (NP I xs) b (NP I bs) bret r
    -- m2
  , YulCat Pure (NP I (x:xs)) ~ m2
    -- f
  , UncurriableNP f (x:xs) bret m2 m2 Many m2 m2 Many
    -- f'
  , EquivalentNPOfFunction f' (x:xs) (NP I (b:bs))
    -- x:xs
  , TupleNWithSameM (TupleN_M m1 (x:xs))
  , ConvertibleNPtoTupleN mp (NP mp (x:xs))
  , ConvertibleNPtoTupleN m1 (NP m1 (x:xs))
  , ConvertibleNPtoTupleN m2 (NP m2 (x:xs))
  , YulVarRefNP xs v r mp m1
  , LinearDistributiveNP mp (x:xs)
  , DistributiveNP m2 (x:xs)
  , TraversableNP m2 (x:xs)
    -- b:bs
  , ConvertibleNPtoTupleN m1 (NP m1 (b:bs))
  , LinearTraversableNP mp (b:bs)
  , YulVarRefNP (b:bs) v r mp m1
  )

ywithuv :: forall f x xs b bs btpl f' v r m1 m2.
  ( ConstraintForYWith f x xs b bs btpl f' v r m1 m2 (P'P r)
    -- m1
  , Uv r ~ m1
    -- btpl
  , TupleN (b:bs) ~ btpl
  , NP I (b:bs) ~ ABITypeDerivedOf btpl
  ) =>
  NP (Uv r) (x:xs) ->
  LiftFunction f m2 m2 Many ->
  YLVM v v r (Ur (TupleN_M (Uv r) (b:bs)))
ywithuv xxs_uvs f = LVM.do
  xxs <- ytkvarNP @(x:xs) xxs_uvs
  let bbs = with'l @f' xxs f'
  Ur bbsrefs <- ymkvarNP @(b:bs) bbs
  LVM.pure $ Ur (fromNPtoTupleN bbsrefs)
  where f' txxs = uncurryNP @f @(x:xs) @btpl @m2 @m2 @Many @m2 @m2 @Many f (distributeNP txxs)
                  >.> YulReduceType

ywithuv_1 :: forall f x xs b v r m1 m2 f'.
  ( ConstraintForYWith f x xs b '[] b f' v r m1 m2 (P'P r)
    -- m1
  , Uv r ~ m1
  ) =>
  TupleN_M (Uv r) (x:xs) ->
  LiftFunction f m2 m2 Many ->
  YLVM v v r (Ur (Uv r b))
ywithuv_1 xxs_tpl f = LVM.do
  xxs_tpl' <- ytkuvN @(x:xs) xxs_tpl
  let !(b :* Nil) = with'l @f' (fromTupleNtoNP xxs_tpl') f'
  ymkvar b
  where f' txxs = uncurryNP @f @(x:xs) @b @m2 @m2 @Many @m2 @m2 @Many f (distributeNP txxs)
                  >.> YulCoerceType @_ @b @(NP I '[b]) >.> YulReduceType

ywithrv :: forall f x xs b bs btpl v r m1 m2 f'.
  ( ConstraintForYWith f x xs b bs btpl f' v r m1 m2 (P'V v r)
    -- m1
  , Rv v r ~ m1
    -- btpl
  , TupleN (b:bs) ~ btpl
  , NP I (b:bs) ~ ABITypeDerivedOf btpl
  ) =>
  TupleN_M (Rv v r) (x:xs) ->
  LiftFunction f m2 m2 Many ->
  YLVM v v r (Ur (TupleN_M m1 (b:bs)))
ywithrv xxs_tpl f = LVM.do
  xxs_tpl' <- ytkrvN @(x:xs) xxs_tpl
  let bbs = with'l @f' (fromTupleNtoNP xxs_tpl') f'
  Ur bbsrefs <- ymkvarNP @(b:bs) bbs
  LVM.pure $ Ur (fromNPtoTupleN bbsrefs)
  where f' txxs = uncurryNP @f @(x:xs) @btpl @m2 @m2 @Many @m2 @m2 @Many f (distributeNP txxs)
                  >.> YulReduceType

ywithrv_1 :: forall f x xs b v r m1 m2 f'.
  ( ConstraintForYWith f x xs b '[] b f' v r m1 m2 (P'V v r)
    -- m1
  , Rv v r ~ m1
  ) =>
  TupleN_M (Rv v r) (x:xs) ->
  LiftFunction f m2 m2 Many ->
  YLVM v v r (Ur (Rv v r b))
ywithrv_1 xxs_tpl f = LVM.do
  xxs_tpl' <- ytkrvN @(x:xs) xxs_tpl
  let !(b :* Nil) = with'l @f' (fromTupleNtoNP xxs_tpl') f'
  ymkvar b
  where f' txxs = uncurryNP @f @(x:xs) @b @m2 @m2 @Many @m2 @m2 @Many f (distributeNP txxs)
                  >.> YulCoerceType @_ @b @(NP I '[b]) >.> YulReduceType

------------------------------------------------------------------------------------------------------------------------
-- $ControlFlows
------------------------------------------------------------------------------------------------------------------------

ywhen :: forall va vb r.
  Rv va r BOOL ->
  YLVM va vb r (Ur (Rv vb r ())) ->
  YLVM va vb r (Ur (Rv vb r ()))
ywhen = error "ywhen"
-- ywhen rv action = LVM.do
--   b <- ytkvar rv
--   ymkvar $ (bool'l (ylvm'vv @'[BOOL] action) (ylvm'vv @'[BOOL] (yembed ()))) (coerceType'l b)

------------------------------------------------------------------------------------------------------------------------
-- $YLVMDiagrams
------------------------------------------------------------------------------------------------------------------------

--
-- uncurry helpers
--

yuncurry_nil :: forall a b r ie m1 va vb.
  ( KnownNat va, KnownNat vb
  , YulO2 a r
  ) =>
  YLVM va vb r (Ur b) ⊸
  (m1 a ⊸ P'x ie r (NP I '[])) ⊸
  (m1 a ⊸ YLVM va vb r (Ur b))
yuncurry_nil b h a = h a & eject . unsafeCoerceYulPort . coerceType'l @_ @() LVM.>> b

yuncurry_xs :: forall m1 m2_ m2b_ m2 mb g x xs b r a ie v1 vn.
  ( YulO4 x (NP I xs) r a
  , UncurriableNP g xs b m1 mb Many (m2_ a) (m2b_ a) One
  --
  , KnownNat v1, KnownNat vn
  , YulVarRef v1 r m2 m1 -- m1 |- m2 ∧ m2 |- m1
  , YLVM v1 vn r ~ mb    -- mb
  , P'x ie r ~ m2 -- m2
  ) =>
  (m1 x -> LiftFunction g m1 mb Many) ⊸       -- ^ f: m1 x ⊸ m1 (xs ⊸...) ⊸ m1b b; the function to be uncurried
  (m2 a ⊸ m2 (NP I (x : xs))) ⊸               -- ^ h: m2 (a ⊸ NP xxs)
  ((m2 a ⊸ m2 (NP I xs)) ⊸ m2_ a (NP I xs)) ⊸ -- ^ mk: m2 (a ⊸ NP I xs) ⊸ m2_ a (NP I xs)
  (m2b_ a b ⊸ (m2 a ⊸ mb b)) ⊸                -- ^ un: m2b_ a b ⊸ (m2 a ⊸ m2b b)
  (m2 a ⊸ mb b)
yuncurry_xs f h mk un a =
  let !(a1, a2) = dup'l a
      !(x, xs) = unconsNP (h a1)
  in ymkvar x LVM.>>= \(Ur xVar) ->
    let g = uncurryNP @g @xs @b @m1 @mb @Many @(m2_ a) @(m2b_ a) @One
            (f xVar)
            (mk (const'l xs))
    in (un g) a2

--
-- ylvm'pp
--

-- | Monadic yul port diagrams for pure input and yul monad output.
newtype YulCat'LPPM v r a b = MkYulCat'LPPM (P'P r a ⊸ YLVM v v r b)

instance forall b v r a.
         ( KnownNat v
         , YulO3 b r a
         ) =>
         UncurriableNP (Ur (Uv r b)) '[] (Ur (Uv r b))
         (Uv r) (YLVM v v r) Many (YulCat'LPP r a) (YulCat'LPPM v r a) One where
  uncurryNP b (MkYulCat'LPP h) = MkYulCat'LPPM (yuncurry_nil b h)

instance forall x xs b g v r a.
         ( KnownNat v
         , YulO5 x (NP I xs) b r a
         , UncurriableNP g xs (Ur (Uv r b)) (Uv r) (YLVM v v r) Many (YulCat'LPP r a) (YulCat'LPPM v r a) One
         ) =>
         UncurriableNP (x -> g) (x:xs) (Ur (Uv r b))
         (Uv r) (YLVM v v r) Many (YulCat'LPP r a) (YulCat'LPPM v r a) One where
  uncurryNP f (MkYulCat'LPP h) = MkYulCat'LPPM $ yuncurry_xs f h MkYulCat'LPP (\(MkYulCat'LPPM g) -> g)

ylvm'pp :: forall xs b f m1 m1b m2 m2b r b'.
  ( YulO3 (NP I xs) b r
  , Uv r ~ m1
  , YLVM 0 0 r ~ m1b
  , YulCat'LPP    r (NP I xs) ~ m2
  , YulCat'LPPM 0 r (NP I xs) ~ m2b
  -- b'
  , Ur (Uv r b) ~ b'
  -- f'
  , UncurriableNP f xs b' m1 m1b Many m2 m2b One
  ) =>
  LiftFunction f (Uv r) (YLVM 0 0 r) Many ->
  (P'P r (NP I xs) ⊸ P'P r b)
ylvm'pp f =
  let !(MkYulCat'LPPM f') = uncurryNP @f @xs @b' @m1 @m1b @_ @m2 @m2b @_ f (MkYulCat'LPP id)
  in \xs -> let !(xs', u) = mkunit'l xs in unsafeCoerceYulPort $ runYLVM u $ LVM.do
    Ur bref <- f' xs'
    ytkvar (ver bref)

instance forall b v r a.
         YulO2 r a =>
         CurriableNP '[] (Ur (Uv r b)) (YulCat'LPP r a) (YLVM v v r) One (Uv r) Many where
  curryNP fNP = fNP (MkYulCat'LPP (\a -> coerceType'l (discard'l a)))

instance forall x xs b r a v.
         ( KnownNat v, YulO4 x (NP I xs) r a
         , CurriableNP xs (Uv r b) (YulCat'LPP r a) (YLVM v v r) One (Uv r) Many
         ) =>
         CurriableNP (x:xs) (Uv r b) (YulCat'LPP r a) (YLVM v v r) One (Uv r) Many where
  curryNP fNP xVar = curryNP @xs @(Uv r b) @(YulCat'LPP r a) @(YLVM v v r) @_ @(Uv r) @_
    (\(MkYulCat'LPP fxs) -> ytkvar xVar LVM.>>= \x -> fNP (MkYulCat'LPP (\a -> consNP x (fxs a))))

--
-- ylvm'pv
--

-- | Monadic yul port diagrams for pure input and yul monad output.
newtype YulCat'LPVM v1 vn r a b = MkYulCat'LPVM (P'P r a ⊸ YLVM v1 vn r b)

instance forall b v1 vn r a.
         (KnownNat v1, KnownNat vn , YulO3 b r a) =>
         UncurriableNP (Ur (Rv vn r b)) '[] (Ur (Rv vn r b))
         (Uv r) (YLVM v1 vn r) Many (YulCat'LPP r a) (YulCat'LPVM v1 vn r a) One where
  uncurryNP b (MkYulCat'LPP h) = MkYulCat'LPVM (yuncurry_nil b h)

instance forall x xs g b v1 vn r a.
         ( KnownNat v1, KnownNat vn, YulO5 x (NP I xs) b r a
         , UncurriableNP g xs (Ur (Rv vn r b))
           (Uv r) (YLVM v1 vn r) Many (YulCat'LPP r a) (YulCat'LPVM v1 vn r a) One
         ) =>
         UncurriableNP (x -> g) (x:xs) (Ur (Rv vn r b))
         (Uv r) (YLVM v1 vn r) Many (YulCat'LPP r a) (YulCat'LPVM v1 vn r a) One where
  uncurryNP f (MkYulCat'LPP h) = MkYulCat'LPVM $ yuncurry_xs f h MkYulCat'LPP (\(MkYulCat'LPVM g) -> g)

ylvm'pv :: forall xs b r vd m1 m1b m2 m2b f b'.
  ( KnownNat vd
  , YulO3 (NP I xs) b r
    -- m1, m1b, m2, m2b
  , Uv          r ~ m1
  , YLVM 0 vd r ~ m1b
  , YulCat'LPP       r (NP I xs) ~ m2
  , YulCat'LPVM 0 vd r (NP I xs) ~ m2b
    -- b'
  , Ur (Rv vd r b) ~ b'
    -- f'
  , UncurriableNP f xs b' m1 m1b Many m2 m2b One
  ) =>
  LiftFunction f m1 m1b Many ->
  (P'P r (NP I xs) ⊸ P'V vd r b)
ylvm'pv f =
  let !(MkYulCat'LPVM f') = uncurryNP @f @xs @b' @m1 @m1b @_ @m2 @m2b @_ f (MkYulCat'LPP id)
  in \xs -> let !(xs', u) = mkunit'l xs in unsafeCoerceYulPort $ runYLVM u $ LVM.do
    Ur bref <- f' xs'
    ytkvar bref

instance forall b v1 vn r a.
         YulO2 r a =>
         CurriableNP '[] (Ur (Rv vn r b)) (YulCat'LPP r a) (YLVM v1 vn r) One (Uv r) Many where
  curryNP fNP = fNP (MkYulCat'LPP (\a -> coerceType'l (discard'l a)))

instance forall x xs b r a v1 vn.
         ( YulO4 x (NP I xs) r a
         , CurriableNP xs (Ur (Rv vn r b)) (YulCat'LPP r a) (YLVM v1 vn r) One (Uv r) Many
           --
         , KnownNat v1, KnownNat vn
         ) =>
         CurriableNP (x:xs) (Ur (Rv vn r b)) (YulCat'LPP r a) (YLVM v1 vn r) One (Uv r) Many where
  curryNP fNP xVar = curryNP @xs @(Ur (Rv vn r b)) @(YulCat'LPP r a) @(YLVM v1 vn r) @_ @(Uv r) @_
    (\(MkYulCat'LPP fxs) -> ytkvar xVar LVM.>>= \x -> fNP (MkYulCat'LPP (\a -> consNP x (fxs a))))

--
-- ylvm'vv
--

-- | Monadic yul port diagrams for pure input and yul monad output.
newtype YulCat'LVVM v1 vn r a b = MkYulCat'LVVM (P'V v1 r a ⊸ YLVM v1 vn r b)

instance forall b v1 vn r a.
         ( KnownNat v1, KnownNat vn
         , YulO3 b r a
         ) =>
         UncurriableNP (Ur (Rv vn r b)) '[] (Ur (Rv vn r b))
         (Rv v1 r) (YLVM v1 vn r) Many (YulCat'LVV v1 v1 r a) (YulCat'LVVM v1 vn r a) One where
  uncurryNP b (MkYulCat'LVV h) = MkYulCat'LVVM (yuncurry_nil b h)

instance forall x xs b g v1 vn r a.
         ( UncurriableNP g xs (Ur (Rv vn r b))
           (Rv v1 r) (YLVM v1 vn r) Many (YulCat'LVV v1 v1 r a) (YulCat'LVVM v1 vn r a) One
           --
         , YulO5 x (NP I xs) b r a
         , KnownNat v1, KnownNat vn
         ) =>
         UncurriableNP (x -> g) (x:xs) (Ur (Rv vn r b))
         (Rv v1 r) (YLVM v1 vn r) Many (YulCat'LVV v1 v1 r a) (YulCat'LVVM v1 vn r a) One where
  uncurryNP f (MkYulCat'LVV h) = MkYulCat'LVVM $ yuncurry_xs f h MkYulCat'LVV (\(MkYulCat'LVVM g) -> g)

ylvm'vv :: forall xs b r vd m1 m1b m2 m2b f b'.
  ( KnownNat vd
  , YulO3 (NP I xs) b r
  -- m1, m1b, m2, m2b
  , Rv          0 r ~ m1
  , YLVM   0 vd r ~ m1b
  , YulCat'LVV  0 0  r (NP I xs) ~ m2
  , YulCat'LVVM 0 vd r (NP I xs) ~ m2b
  -- b'
  , Ur (Rv vd r b) ~ b'
  -- f'
  , UncurriableNP f xs b' m1 m1b Many m2 m2b One
  ) =>
  LiftFunction f m1 m1b Many ->
  (P'V 0 r (NP I xs) ⊸ P'V vd r b)
ylvm'vv f =
  let !(MkYulCat'LVVM f') = uncurryNP @f @xs @b' @m1 @m1b @_ @m2 @m2b @_ f (MkYulCat'LVV id)
  in \xs -> let !(xs', u) = mkunit'l xs in unsafeCoerceYulPort $ runYLVM u $ LVM.do
    Ur bref <- f' xs'
    ytkvar bref

instance forall b v1 vn r a.
         YulO2 r a =>
         CurriableNP '[] (Ur (Rv vn r b)) (YulCat'LVV v1 v1 r a) (YLVM v1 vn r) One (Rv v1 r) Many where
  curryNP fNP = fNP (MkYulCat'LVV (\a -> coerceType'l (discard'l a)))

instance forall x xs b r a v1 vn.
         ( YulO4 x (NP I xs) r a
         , CurriableNP xs (Ur (Rv vn r b)) (YulCat'LVV v1 v1 r a) (YLVM v1 vn r) One (Rv v1 r) Many
           --
         , KnownNat v1, KnownNat vn
         ) =>
         CurriableNP (x:xs) (Ur (Rv vn r b)) (YulCat'LVV v1 v1 r a) (YLVM v1 vn r) One (Rv v1 r) Many where
  curryNP fNP xVar = curryNP @xs @(Ur (Rv vn r b)) @(YulCat'LVV v1 v1 r a) @(YLVM v1 vn r) @_ @(Rv v1 r) @_
    (\(MkYulCat'LVV fxs) -> ytkvar xVar LVM.>>= \x -> fNP (MkYulCat'LVV (\a -> consNP x (fxs a))))
