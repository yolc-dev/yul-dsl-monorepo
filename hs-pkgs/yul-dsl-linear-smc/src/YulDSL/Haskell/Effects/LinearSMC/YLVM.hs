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
  ( -- $YLVM
    YLVM, runYLVM
  , ygulp, yrunvt
    -- $YulVarRefAPI
  , LinearlyVersionRestrictedYulPort
  , DereferenceYulVarRef, ReferenciableYulVar
  , DereferenceXv, ReferenciableXv

  , Uv (Uv), Rv (Rv) -- hide
  , VersionableYulVarRef (ver)

  , YulVarRef (ymkref, ytkref), YulVarRefNP (ymkrefNP)
  , ytake1, ytakev1
  , YTakeableVarRefNP (ytakeuvNP, ytakervNP), ytakeuvN, ytakervN

  , ywithuvN, ywithuvN_1, ywithrvN, ywithrvN_1
  , yembed
    -- $YLVMDiagrams
  , YulCat'LPPM (MkYulCat'LPPM), YulCat'LPVM (MkYulCat'LPVM), YulCat'LVVM (MkYulCat'LVVM)
  , ylvm'pp, ylvm'pv, ylvm'vv
    -- * Re-export LVM Primitives
  , module Control.LinearlyVersionedMonad.Combinators
  , module Control.LinearlyVersionedMonad.LVMVar
  ) where
-- base
import GHC.TypeLits                                  (KnownNat, type (<=))
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
-- * YLVM: A Linearly Versioned Monad for Yul Ports
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
      initRgstr :: YLVM 0 0 r ()
      b <- m
      consumeRgstr
      LVM.pure b
    -- initialize the var registry
    initRgstr = MkLVM \(MkYLVMCtx vt mbRgstr) ->
      let rgstr = case mbRgstr of
            Nothing -> initLVMVarRegistry
            err     -> lseq (error "nonsense" :: ()) (UnsafeLinear.coerce err)
      in (Dict, MkYLVMCtx vt (Just rgstr), ())
      -- consume the var registry
    consumeRgstr = with_yulvar_registry \rgstr -> LVM.do
      consumeLVMVarRegistry rgstr
      LVM.pure (Nothing, ())

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

instance YulO1 r => ContextualConsumable (YLVMCtx r) (Ur a) where
  contextualConsume ctx (Ur _) = ctx

instance YulO2 r a => ContextualConsumable (YLVMCtx r) (P'x eff r a) where
  contextualConsume (MkYLVMCtx vt rgstr) x = MkYLVMCtx (vtgulp vt x) rgstr

-- Fine-grained ContextualSeqable specializations.
--

instance (YulO3 r a b) => ContextualSeqable (YLVMCtx r) (P'P r a) (P'P r b) where
  contextualSeq ctx a b = (ctx, const'l b a)

instance (YulO3 r a b) => ContextualSeqable (YLVMCtx r) (P'P r a) (P'V vb r b) where
  contextualSeq ctx a b = (ctx, const'l b (unsafeCoerceYulPort a))

instance (YulO3 r a b) => ContextualSeqable (YLVMCtx r) (P'V va r a) (P'P r b) where
  contextualSeq ctx a b = (ctx, const'l b (unsafeCoerceYulPort a))

-- When both ports are versioned, it is important to thread them in the right sequence to avoid unsound out-of-order
-- side effects.
instance (KnownNat va, KnownNat vb, va <= vb, YulO3 r a b) =>
         ContextualSeqable (YLVMCtx r) (P'V va r a) (P'V vb r b) where
  contextualSeq (MkYLVMCtx vt mbRgstr) a b =
    let !(vt', b') = vtseq vt a b
    in (MkYLVMCtx vt' mbRgstr, b')

-- ContextualDupable
--

instance YulO2 r a => ContextualDupable (YLVMCtx r) (P'x eff r a) where
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
-- * Yul Variable Reference's API
------------------------------------------------------------------------------------------------------------------------

type LinearlyVersionRestrictedYulPort v r port = VersionRestrictedData v (YLVMCtx r) port

--
-- ReferenciableYulVar (FIXME: remove this)
--

type family DereferenceYulVarRef ref = port | port -> ref where
  DereferenceYulVarRef (UvYulVarRef r a)   = P'P r a
  DereferenceYulVarRef (RvYulVarRef v r a) = P'V v r a

type ReferenciableYulVar v r ref = ReferenciableLVMVar v ref (YLVMCtx r) (DereferenceYulVarRef ref)

--
-- ReferenciableXv
--

-- type family YulVarRefToXRef ref = xref | xref -> ref where
--   YulVarRefToXRef (UvYulVarRef r a)   = Uv r a
--   YulVarRefToXRef (RvYulVarRef v r a) = Rv v r a

type family DereferenceXv ref = port | port -> ref where
  DereferenceXv (Uv r a)   = P'P r a
  DereferenceXv (Rv v r a) = P'V v r a

type family XRefToYulVarRef xref = ref | ref -> xref where
  XRefToYulVarRef (Uv r a) = UvYulVarRef r a
  XRefToYulVarRef (Rv v r a) = RvYulVarRef v r a

type ReferenciableXv v r xref = ReferenciableYulVar v r (XRefToYulVarRef xref)

--
-- Uv
--

type UvYulVarRef r a = UvLVMVarRef (YLVMCtx r) (P'P r a)

-- | Unrestricted wrapper of 'UvYulVarRef' in two letters.
data Uv r a where
  Uv :: forall r a. UvYulVarRef r a -> Uv r a
type role Uv nominal nominal

instance (KnownNat v, YulO2 r a) => ReferenciableLVMVar v (Uv r a) (YLVMCtx r) (P'P r a) where
  takeLVMVarRef (Uv var) = takeLVMVarRef var

-- !FIXME! remove, do not expose
instance YulO2 r a => ContextualConsumable (YLVMCtx r) (Uv r a) where
  contextualConsume ctx (Uv _) = ctx

--
-- Rv
--

type RvYulVarRef v r a = RvLVMVarRef (YLVMCtx r) v (P'V v r a)

-- | Unrestricted wrapper of 'RvYulVarRef' in two letters.
data Rv v r a where
  Rv :: forall v r a. RvYulVarRef v r a -> Rv v r a
type role Rv nominal nominal nominal

instance (KnownNat v, YulO2 r a) => ReferenciableLVMVar v (Rv v r a) (YLVMCtx r) (P'V v r a) where
  takeLVMVarRef (Rv vref) = takeLVMVarRef vref

-- !FIXME! remove, do not expose
instance YulO2 r a => ContextualConsumable (YLVMCtx r) (Rv v r a) where
  contextualConsume ctx (Rv _) = ctx

--
-- VersionableYulVar (ver)
--

class VersionableYulVarRef v r a vref | vref -> a r where
  ver :: forall. vref -> Rv v r a

instance (KnownNat v, YulO2 r a) => VersionableYulVarRef v r a (Uv r a) where
  ver (Uv uvref) = Rv (VerUvLVMVarRef uvref)

instance (KnownNat v, YulO2 r a) => VersionableYulVarRef v r a (UvYulVarRef r a) where
  ver ref = Rv (VerUvLVMVarRef ref)

instance VersionableYulVarRef v r a (RvYulVarRef v r a) where
  ver = Rv

--
-- YulVarRef
--

-- | A unified interface to work with both 'Uv' and 'Rv'.
class YulVarRef v r port_ vref_ | v port_ -> vref_, vref_ -> port_ where
  -- | Make a variable reference from a yul port.
  ymkref :: forall a. (KnownNat v, YulO2 a r) => port_ a ⊸ YLVM v v r (Ur (vref_ a))
  -- | Take a yul port from a variable reference.
  ytkref :: forall a. (KnownNat v, YulO2 a r) => vref_ a ⊸ YLVM v v r (port_ a)

instance YulVarRef v r (P'P r) (Uv r) where
  ymkref x = with_yulvar_registry \rgstr ->
    let !(Ur var, rgstr') = registerUvLVMVar x rgstr
    in LVM.pure (Just rgstr', Ur (Uv var))
  ytkref (Uv ref) = with_yulvar_registry \rgstr -> LVM.do
    (port, rgstr') <- takeLVMVarRef ref rgstr
    LVM.pure (Just rgstr', port)

instance YulVarRef v r (P'V v r) (Rv v r) where
  ymkref x = with_yulvar_registry \rgstr ->
    let !(Ur var, rgstr') = registerRvLVMVar x rgstr
    in LVM.pure (Just rgstr', Ur (Rv var))
  ytkref (Rv ref) = with_yulvar_registry \rgstr -> LVM.do
    (port, rgstr') <- takeLVMVarRef ref rgstr
    LVM.pure (Just rgstr', port)

--
-- YulVarRefNP
--

class YulVarRef v r port_ ref_ =>
      YulVarRefNP xs v r port_ ref_ where
  ymkrefNP :: forall. (KnownNat v, YulO2 r (NP xs)) => NP (MapList port_ xs) ⊸ YLVM v v r (Ur (NP (MapList ref_ xs)))

instance YulVarRef v r port_ vref_ =>
         YulVarRefNP '[] v r port_ vref_ where
  ymkrefNP Nil = LVM.pure (Ur Nil)

instance ( YulVarRef v r port_ vref_
         , YulO2 x (NP xs)
         , YulVarRefNP xs v r port_ ref_
         ) => YulVarRefNP (x:xs) v r port_ ref_ where
  ymkrefNP (x :* xs) = LVM.do
    Ur xref <- ymkref x
    Ur xsrefs <- ymkrefNP @xs @v @r @port_ @ref_ xs
    LVM.pure (Ur (xref :* xsrefs))

--
-- yembed
--

-- | Generate a unit monadically.
yembed :: forall a v r ie xv_.
  ( KnownNat v, YulO2 r a
  , DereferenceXv (xv_ a) ~ P'x ie r a
  , YulVarRef v r (P'x ie r) xv_
  ) =>
  a -> YLVM v v r (Ur (xv_ a))
yembed a = embed a LVM.>>= ymkref

--
-- ytake1, ytakev1
--

-- FIXME DELETE!
ytake1 :: forall ref v r ioe a.
  ( YulO2 a r
  , ReferenciableYulVar v r ref
  , DereferenceYulVarRef ref ~ P'x ioe r a
  ) =>
  ref ->
  YLVM v v r (P'x ioe r a)
ytake1 ref = with_yulvar_registry \rgstr -> LVM.do
  (x, rgstr') <- takeLVMVarRef ref rgstr
  LVM.pure (Just rgstr', x)

-- FIXME DELETE!
ytakev1 :: forall ref v a r.
  ( YulO2 a r
  , ReferenciableYulVar v r ref
  , LinearlyVersionRestrictedYulPort v r (DereferenceYulVarRef ref) ~ P'V v r a
  ) =>
  ref ->
  YLVM v v r (P'V v r a)
ytakev1 ref = with_yulvar_registry \rgstr -> LVM.do
  (x, rgstr') <- takevLVMVarRef ref rgstr
  LVM.pure (Just rgstr', x)

--
-- ytakeUvN, ytakeAnyN
--

class YTakeableVarRefNP v xs r where
  ytakeuvNP :: forall m1 m2.
    ( KnownNat v
    , Uv r ~ m1
    , P'P r ~ m2
    ) =>
    NP (MapList m1 xs) ⊸
    YLVM v v r (NP (MapList m2 xs))

  ytakervNP :: forall m1 m2.
    ( KnownNat v
    , Rv v r ~ m1
    , P'V v r ~ m2
    ) =>
    NP (MapList m1 xs) ⊸
    YLVM v v r (NP (MapList m2 xs))

instance YTakeableVarRefNP v '[] r where
  ytakeuvNP Nil = LVM.pure Nil
  ytakervNP Nil = LVM.pure Nil

instance (YulO2 x r, YTakeableVarRefNP v xs r) => YTakeableVarRefNP v (x:xs) r where
  ytakeuvNP np = LVM.do
    (x', xsref') <- with_yulvar_registry \rgstr -> LVM.do
      let !(Uv xref, xsref) = splitNonEmptyNP np
      (x, rgstr') <- takeLVMVarRef xref rgstr
      LVM.pure (Just rgstr', (x, xsref))
    xs <- ytakeuvNP @v @xs xsref'
    LVM.pure (x' :* xs)

  ytakervNP np = LVM.do
    (x', xsref') <- with_yulvar_registry \rgstr -> LVM.do
      let !(Rv xref, xsref) = splitNonEmptyNP np
      (x, rgstr') <- takevLVMVarRef xref rgstr
      LVM.pure (Just rgstr', (x, xsref))
    xs <- ytakervNP @v @xs xsref'
    LVM.pure $ (x' :* xs)

ytakeuvN :: forall v xs r m1 m2.
  ( KnownNat v
  , Uv r ~ m1
  , P'P r ~ m2
  , ConvertibleNPtoTupleN (NP (MapList m1 xs))
  , ConvertibleNPtoTupleN (NP (MapList m2 xs))
  , YTakeableVarRefNP v xs r
  ) =>
  NPtoTupleN (NP (MapList m1 xs)) ->
  YLVM v v r (NPtoTupleN (NP (MapList m2 xs)))
ytakeuvN tpl = LVM.do
  aNP <- ytakeuvNP @v @xs (fromTupleNtoNP tpl)
  LVM.pure (fromNPtoTupleN aNP)

ytakervN :: forall v xs r m1 m2.
  ( KnownNat v
  , Rv v r ~ m1
  , P'V v r ~ m2
  , ConvertibleNPtoTupleN (NP (MapList m1 xs))
  , ConvertibleNPtoTupleN (NP (MapList m2 xs))
  , YTakeableVarRefNP v xs r
  ) =>
  NPtoTupleN (NP (MapList m1 xs)) ->
  YLVM v v r (NPtoTupleN (NP (MapList m2 xs)))
ytakervN tpl = LVM.do
  aNP <- ytakervNP @v @xs (fromTupleNtoNP tpl)
  LVM.pure (fromNPtoTupleN aNP)

--
-- ywithuv_N, ywithrv_N
--

type ConstraintForYWith f x xs b bs brst f' v r m1 m1b m2 mp =
  ( KnownNat v
  , YulO6 x (NP xs) b (NP bs) brst r
    -- f
  , EquivalentNPOfFunction f (x:xs) brst
  , UncurriableNP f (x:xs) brst m2 m2 m2 m2 Many
    -- f'
  , EquivalentNPOfFunction f' (x:xs) (NP (b:bs))
    -- x:xs
  , ConvertibleNPtoTupleN (NP (MapList m1 (x:xs)))
  , ConvertibleNPtoTupleN (NP (MapList mp (x:xs)))
  , YTakeableVarRefNP v (x:xs) r
  , LinearDistributiveNP mp (x:xs)
  , DistributiveNP m2 (x:xs)
  , TraversableNP m2 (x:xs)
    -- b:bs
  , ConvertibleNPtoTupleN (NP (MapList m1b (b:bs)))
  , LinearTraversableNP mp (b:bs)
  , YulVarRefNP (b:bs) v r mp m1b
  )

ywithuvN :: forall f x xs b bs btpl f' v r m1 m1b m2.
  ( ConstraintForYWith f x xs b bs btpl f' v r m1 m1b m2 (P'P r)
    -- m1, m1b, m2
  , Uv r ~ m1
  , Uv r ~ m1b
  , YulCat Pure (NP (x:xs)) ~ m2
    -- btpl
  , NP (b:bs) ~ ABITypeDerivedOf btpl
  ) =>
  NPtoTupleN (NP (MapList (Uv r) (x:xs))) ⊸
  PureY f ->
  YLVM v v r (Ur (NPtoTupleN (NP (MapList (Uv r) (b:bs)))))
ywithuvN xxstpl f = LVM.do
  xxstpl' <- ytakeuvN @v @(x:xs) xxstpl
  let bbs = withNP'l @f' (fromTupleNtoNP xxstpl') f'
  Ur bbsrefs <- ymkrefNP @(b:bs) bbs
  LVM.pure $ Ur (fromNPtoTupleN bbsrefs)
  where f' txxs = uncurryNP @f @(x:xs) @btpl @m2 @m2 @m2 @m2 @Many f (distributeNP txxs)
                  >.> YulReduceType

ywithuvN_1 :: forall f x xs b v r m1 m1b m2 f'.
  ( ConstraintForYWith f x xs b '[] b f' v r m1 m1b m2 (P'P r)
    -- m1, m2
  , Uv r ~ m1
  , Uv r ~ m1b
  , YulCat Pure (NP (x:xs)) ~ m2
  ) =>
  NPtoTupleN (NP (MapList (Uv r) (x:xs))) ⊸
  PureY f ->
  YLVM v v r (Ur (Uv r b))
ywithuvN_1 xxstpl f = LVM.do
  xxstpl' <- ytakeuvN @v @(x:xs) xxstpl
  let !(b :* Nil) = withNP'l @f' (fromTupleNtoNP xxstpl') f'
  ymkref b
  where f' txxs = uncurryNP @f @(x:xs) @b @m2 @m2 @m2 @m2 @Many f (distributeNP txxs)
                  >.> YulCoerceType @_ @b @(NP '[b]) >.> YulReduceType

ywithrvN :: forall f x xs b bs btpl v r m1 m1b m2 f'.
  ( ConstraintForYWith f x xs b bs btpl f' v r m1 m1b m2 (P'V v r)
    -- m1, m2
  , Rv v r ~ m1
  , Rv v r ~ m1b
  , YulCat Pure (NP (x:xs)) ~ m2
    -- btpl
  , NP (b:bs) ~ ABITypeDerivedOf btpl
  ) =>
  NPtoTupleN (NP (MapList (Rv v r) (x:xs))) ⊸
  PureY f ->
  YLVM v v r (Ur (NPtoTupleN (NP (MapList (Rv v r) (b:bs)))))
ywithrvN xxstpl f = LVM.do
  xxstpl' <- ytakervN @v @(x:xs) xxstpl
  let bbs = withNP'l @f' (fromTupleNtoNP xxstpl') f'
  Ur bbsrefs <- ymkrefNP @(b:bs) bbs
  LVM.pure $ Ur (fromNPtoTupleN bbsrefs)
  where f' txxs = uncurryNP @f @(x:xs) @btpl @m2 @m2 @m2 @m2 @Many f (distributeNP txxs)
                  >.> YulReduceType

ywithrvN_1 :: forall f x xs b v r m1 m1b m2 f'.
  ( ConstraintForYWith f x xs b '[] b f' v r m1 m1b m2 (P'V v r)
    -- m1, m2
  , Rv v r ~ m1
  , Rv v r ~ m1b
  , YulCat Pure (NP (x:xs)) ~ m2
  ) =>
  NPtoTupleN (NP (MapList (Rv v r) (x:xs))) ⊸
  PureY f ->
  YLVM v v r (Ur (Rv v r b))
ywithrvN_1 xxstpl f = LVM.do
  xxstpl' <- ytakervN @v @(x:xs) xxstpl
  let !(b :* Nil) = withNP'l @f' (fromTupleNtoNP xxstpl') f'
  ymkref b
  where f' txxs = uncurryNP @f @(x:xs) @b @m2 @m2 @m2 @m2 @Many f (distributeNP txxs)
                  >.> YulCoerceType @_ @b @(NP '[b]) >.> YulReduceType

------------------------------------------------------------------------------------------------------------------------
-- $YLVMDiagrams
-- * YLVM Monadic Diagrams
------------------------------------------------------------------------------------------------------------------------

--
-- uncurry helpers
--

yuncurry_nil :: forall a b r ie m1 va vb.
  ( KnownNat va, KnownNat vb
  , YulO2 a r
  ) =>
  YLVM va vb r (Ur b) ⊸
  (m1 a ⊸ P'x ie r (NP '[])) ⊸
  (m1 a ⊸ YLVM va vb r (Ur b))
yuncurry_nil b h a = h a & eject . unsafeCoerceYulPort . coerceType'l @_ @() LVM.>> b

yuncurry_xs :: forall m1 m1b m2_ m2b_ m2' m2b' g x xs b r a ie v1 vn.
  ( YulO4 x (NP xs) r a
  , UncurriableNP g xs b m1 m1b (m2_ a) (m2b_ a) One
  --
  , KnownNat v1, KnownNat vn
  , YulVarRef v1 r m2' m1 -- m1 |- m2' ∧ m2' |- m1
  , YLVM v1 vn r ~ m1b -- m1b
  , P'x ie r ~ m2' -- m2'
  , m1b ~ m2b' -- m1b |- m2b'
  ) =>
  (m1 x ⊸ LiftFunction g m1 m1b One) ->      -- ^ f: m1 x ⊸ m1 (xs ⊸...) ⊸ m1b b; the function to be uncurried
  (m2' a ⊸ m2' (NP (x : xs))) ->             -- ^ h: m2' (a ⊸ NP xxs)
  ((m2' a ⊸ m2' (NP xs)) ⊸ m2_ a (NP xs)) -> -- ^ mk: m2' (a ⊸ NP xs) ⊸ m2_ a (NP xs)
  (m2b_ a b ⊸ (m2' a ⊸ m2b' b)) ->           -- ^ un: m2b_ a b ⊸ (m2' a ⊸ m2b' b)
  (m2' a ⊸ m2b' b)
yuncurry_xs f h mk un a =
  let !(a1, a2) = dup'l a
      !(x, xs) = unconsNP (h a1)
  in ymkref x LVM.>>= \(Ur xref) ->
    let g = uncurryNP @g @xs @b @m1 @m1b @(m2_ a) @(m2b_ a) @One
            (f xref)
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
         (Uv r) (YLVM v v r) (YulCat'LPP r a) (YulCat'LPPM v r a) One where
  uncurryNP b (MkYulCat'LPP h) = MkYulCat'LPPM (yuncurry_nil b h)

instance forall x xs b g v r a.
         ( KnownNat v
         , YulO5 x (NP xs) b r a
         , UncurriableNP g xs (Ur (Uv r b)) (Uv r) (YLVM v v r) (YulCat'LPP r a) (YulCat'LPPM v r a) One
         ) =>
         UncurriableNP (x -> g) (x:xs) (Ur (Uv r b))
         (Uv r) (YLVM v v r) (YulCat'LPP r a) (YulCat'LPPM v r a) One where
  uncurryNP f (MkYulCat'LPP h) = MkYulCat'LPPM $ yuncurry_xs f h MkYulCat'LPP (\(MkYulCat'LPPM g) -> g)

ylvm'pp :: forall xs b f m1 m1b m2 m2b r b'.
  ( YulO3 (NP xs) b r
  , Uv             r ~ m1
  , YLVM   0 0 r ~ m1b
  , YulCat'LPP    r (NP xs) ~ m2
  , YulCat'LPPM 0 r (NP xs) ~ m2b
  -- b'
  , Ur (Uv r b) ~ b'
  -- f'
  , UncurriableNP f xs b' m1 m1b m2 m2b One
  ) =>
  LiftFunction f m1 m1b One ->
  (P'P r (NP xs) ⊸ P'P r b)
ylvm'pp f =
  let !(MkYulCat'LPPM f') = uncurryNP @f @xs @b' @m1 @m1b @m2 @m2b @One f (MkYulCat'LPP id)
  in \xs -> let !(xs', u) = mkunit'l xs in unsafeCoerceYulPort $ runYLVM u $ LVM.do
    Ur (Uv bvar) <- f' xs'
    ytakev1 bvar

instance forall b v r a.
         YulO2 r a =>
         CurriableNP (Uv r b) '[] (Uv r b)
         (Uv r) (YLVM v v r) (YulCat'LPP r a) One where
  curryNP fNP = fNP (MkYulCat'LPP (\a -> coerceType'l (discard'l a)))

instance forall x xs b g r a v.
         ( YulO4 x (NP xs) r a
         , CurriableNP g xs (Uv r b) (Uv r) (YLVM v v r) (YulCat'LPP r a) One
           --
         , KnownNat v
         , ReferenciableYulVar v r (UvYulVarRef r b)
         ) =>
         CurriableNP (x -> g) (x:xs) (Uv r b)
         (Uv r) (YLVM v v r) (YulCat'LPP r a) One where
  curryNP fNP (Uv xref) = curryNP @g @xs @(Uv r b) @(Uv r) @(YLVM v v r) @(YulCat'LPP r a) @One
    (\(MkYulCat'LPP fxs) -> ytake1 xref LVM.>>= \x -> fNP (MkYulCat'LPP (\a -> consNP x (fxs a))))

--
-- ylvm'pv
--

-- | Monadic yul port diagrams for pure input and yul monad output.
newtype YulCat'LPVM v1 vn r a b = MkYulCat'LPVM (P'P r a ⊸ YLVM v1 vn r b)

instance forall b v1 vn r a.
         ( KnownNat v1, KnownNat vn
         , YulO3 b r a
         ) =>
         UncurriableNP (Ur (Rv vn r b)) '[] (Ur (Rv vn r b))
         (Uv r) (YLVM v1 vn r) (YulCat'LPP r a) (YulCat'LPVM v1 vn r a) One where
  uncurryNP b (MkYulCat'LPP h) = MkYulCat'LPVM (yuncurry_nil b h)

instance forall x xs b g v1 vn r a.
         ( KnownNat v1, KnownNat vn
         , YulO5 x (NP xs) b r a
         , UncurriableNP g xs (Ur (Rv vn r b))
           (Uv r) (YLVM v1 vn r) (YulCat'LPP r a) (YulCat'LPVM v1 vn r a) One
         ) =>
         UncurriableNP (x -> g) (x:xs) (Ur (Rv vn r b))
         (Uv r) (YLVM v1 vn r) (YulCat'LPP r a) (YulCat'LPVM v1 vn r a) One where
  uncurryNP f (MkYulCat'LPP h) = MkYulCat'LPVM $ yuncurry_xs f h MkYulCat'LPP (\(MkYulCat'LPVM g) -> g)

ylvm'pv :: forall xs b r vd m1 m1b m2 m2b f b'.
  ( KnownNat vd
  , YulO3 (NP xs) b r
  -- m1, m1b, m2, m2b
  , Uv          r ~ m1
  , YLVM 0 vd r ~ m1b
  , YulCat'LPP       r (NP xs) ~ m2
  , YulCat'LPVM 0 vd r (NP xs) ~ m2b
  -- b'
  , Ur (Rv vd r b) ~ b'
  -- f'
  , UncurriableNP f xs b' m1 m1b m2 m2b One
  ) =>
  LiftFunction f m1 m1b One ->
  (P'P r (NP xs) ⊸ P'V vd r b)
ylvm'pv f =
  let !(MkYulCat'LPVM f') = uncurryNP @f @xs @b' @m1 @m1b @m2 @m2b @One f (MkYulCat'LPP id)
  in \xs -> let !(xs', u) = mkunit'l xs in unsafeCoerceYulPort $ runYLVM u $ LVM.do
    Ur (Rv bvar) <- f' xs'
    ytakev1 bvar

instance forall b v1 vn r a.
         YulO2 r a =>
         CurriableNP (Ur (Rv vn r b)) '[] (Ur (Rv vn r b)) (Uv r) (YLVM v1 vn r) (YulCat'LPP r a) One where
  curryNP fNP = fNP (MkYulCat'LPP (\a -> coerceType'l (discard'l a)))

instance forall x xs b g r a v1 vn.
         ( YulO4 x (NP xs) r a
         , CurriableNP g xs (Ur (Rv vn r b)) (Uv r) (YLVM v1 vn r) (YulCat'LPP r a) One
           --
         , KnownNat v1, KnownNat vn
         , ReferenciableYulVar v1 r (UvYulVarRef r b)
         ) =>
         CurriableNP (x -> g) (x:xs) (Ur (Rv vn r b))
         (Uv r) (YLVM v1 vn r) (YulCat'LPP r a) One where
  curryNP fNP (Uv xref) = curryNP @g @xs @(Ur (Rv vn r b)) @(Uv r) @(YLVM v1 vn r) @(YulCat'LPP r a) @One
    (\(MkYulCat'LPP fxs) -> ytake1 xref LVM.>>= \x -> fNP (MkYulCat'LPP (\a -> consNP x (fxs a))))

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
         (Rv v1 r) (YLVM v1 vn r) (YulCat'LVV v1 v1 r a) (YulCat'LVVM v1 vn r a) One where
  uncurryNP b (MkYulCat'LVV h) = MkYulCat'LVVM (yuncurry_nil b h)

instance forall x xs b g v1 vn r a.
         ( UncurriableNP g xs (Ur (Rv vn r b))
           (Rv v1 r) (YLVM v1 vn r) (YulCat'LVV v1 v1 r a) (YulCat'LVVM v1 vn r a) One
           --
         , YulO5 x (NP xs) b r a
         , KnownNat v1, KnownNat vn
         ) =>
         UncurriableNP (x -> g) (x:xs) (Ur (Rv vn r b))
         (Rv v1 r) (YLVM v1 vn r) (YulCat'LVV v1 v1 r a) (YulCat'LVVM v1 vn r a) One where
  uncurryNP f (MkYulCat'LVV h) = MkYulCat'LVVM $ yuncurry_xs f h MkYulCat'LVV (\(MkYulCat'LVVM g) -> g)

ylvm'vv :: forall xs b r vd m1 m1b m2 m2b f b'.
  ( KnownNat vd
  , YulO3 (NP xs) b r
  -- m1, m1b, m2, m2b
  , Rv          0 r ~ m1
  , YLVM   0 vd r ~ m1b
  , YulCat'LVV  0 0  r (NP xs) ~ m2
  , YulCat'LVVM 0 vd r (NP xs) ~ m2b
  -- b'
  , Ur (Rv vd r b) ~ b'
  -- f'
  , UncurriableNP f xs b' m1 m1b m2 m2b One
  ) =>
  LiftFunction f m1 m1b One ->
  (P'V 0 r (NP xs) ⊸ P'V vd r b)
ylvm'vv f =
  let !(MkYulCat'LVVM f') = uncurryNP @f @xs @b' @m1 @m1b @m2 @m2b @One f (MkYulCat'LVV id)
  in \xs -> let !(xs', u) = mkunit'l xs in unsafeCoerceYulPort $ runYLVM u $ LVM.do
    Ur (Rv bvar) <- f' xs'
    ytakev1 bvar

instance forall b v1 vn r a.
         YulO2 r a =>
         CurriableNP (Ur (Rv vn r b)) '[] (Ur (Rv vn r b))
         (Rv v1 r) (YLVM v1 vn r) (YulCat'LVV v1 v1 r a) One where
  curryNP fNP = fNP (MkYulCat'LVV (\a -> coerceType'l (discard'l a)))

instance forall x xs b g r a v1 vn.
         ( YulO4 x (NP xs) r a
         , CurriableNP g xs (Ur (Rv vn r b)) (Rv v1 r) (YLVM v1 vn r) (YulCat'LVV v1 v1 r a) One
           --
         , KnownNat v1, KnownNat vn
         , ReferenciableYulVar v1 r (RvYulVarRef v1 r b)
         ) =>
         CurriableNP (x -> g) (x:xs) (Ur (Rv vn r b)) (Rv v1 r) (YLVM v1 vn r) (YulCat'LVV v1 v1 r a) One where
  curryNP fNP (Rv xref) = curryNP @g @xs @(Ur (Rv vn r b)) @(Rv v1 r) @(YLVM v1 vn r) @(YulCat'LVV v1 v1 r a) @One
    (\(MkYulCat'LVV fxs) -> ytake1 xref LVM.>>= \x -> fNP (MkYulCat'LVV (\a -> consNP x (fxs a))))

--
-- curryNP'vv instances
--

instance forall b v1 vn r a.
         ( YulO2 r a
         ) =>
         CurriableNP (P'V vn r b) '[] (P'V vn r b)
         (P'V v1 r) (YLVM v1 vn r) (YulCat'LVV v1 v1 r a) One where
  curryNP fNP = fNP (MkYulCat'LVV (\a -> coerceType'l (discard'l a)))

instance forall g x xs b r a v1 vn.
         ( YulO4 x (NP xs) r a
         , CurriableNP g xs b (P'V v1 r) (YLVM v1 vn r) (YulCat'LVV v1 v1 r a) One
         ) =>
         CurriableNP (x -> g) (x:xs) b
         (P'V v1 r) (YLVM v1 vn r) (YulCat'LVV v1 v1 r a) One where
  curryNP fNP x = curryNP @g @xs @b @(P'V v1 r) @(YLVM v1 vn r) @(YulCat'LVV v1 v1 r a) @One
                  (\(MkYulCat'LVV fxs) -> fNP (MkYulCat'LVV (\a -> (consNP x (fxs a)))))
