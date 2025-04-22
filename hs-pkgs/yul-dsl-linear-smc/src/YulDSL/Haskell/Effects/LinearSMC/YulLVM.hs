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

This module provides the linearly-versioned monad (LVM) for yul ports.

-}
module YulDSL.Haskell.Effects.LinearSMC.YulLVM
  ( -- $YulLVM
    YulLVM, runYulLVM
  , ypure, yembed
    -- $YulVarRefAPI
  , Uv (Uv), Rv (Rv)
  , MakeableYulVarRef (ymkref)
  , ReferenciableYulVar, DereferenceYulVar
  , AnyYulVarRef (AnyUv, AnyRv)
  , YTakeableVarRefNP (ytakeUvNP, ytakeAnyNP), ytakeUvN, ytakeAnyN
  , ytake1, ytakev1
  , ywithUv, ywithAny
    -- $YulLVMDiagrams
  , YulCat'LPPM (MkYulCat'LPPM), YulCat'LPVM (MkYulCat'LPVM), YulCat'LVVM (MkYulCat'LVVM)
  , yullvm'pp, yullvm'pv, yullvm'vv
    -- * LVM Primitives
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
-- $YulLVM
-- * YulLVM: A Linearly Versioned Monad for Yul Ports
------------------------------------------------------------------------------------------------------------------------

-- | YulLVM is a linear versioned monad with 'YulLVMCtx' as its context data.
type YulLVM va vb r = LVM (YulLVMCtx r) va vb

-- | Run a YulLVM with an initial unit port and returns a versioned result.
runYulLVM :: forall b vd r ie.
  ( KnownNat vd
  , YulO2 r b
  ) =>
  P'x ie r () ⊸ YulLVM 0 vd r (P'V vd r b) ⊸ P'V vd r b
runYulLVM u m = let ctx = mk_yullvm_ctx u
                    !(ctx', b) = runLVM ctx mWrapper
                    u' = rm_yullvm_ctx ctx'
                in const'l b u'
  where -- wrap given monad with var registry init/consume block
        mWrapper = LVM.do
          initRgstr :: YulLVM 0 0 r ()
          b <- m
          consumeRgstr
          LVM.pure b
        -- initialize the var registry
        initRgstr = MkLVM \(MkYulLVMCtx vt mbRgstr) ->
          let rgstr = case mbRgstr of
                Nothing -> initLVMVarRegistry
                err     -> lseq (error "nonsense" :: ()) (UnsafeLinear.coerce err)
          in (Dict, MkYulLVMCtx vt (Just rgstr), ())
        -- consume the var registry
        consumeRgstr = with_yulvar_registry \rgstr -> LVM.do
          consumeLVMVarRegistry rgstr
          LVM.pure (Nothing, ())

--
-- YulLVM Registry
--

type YulVarRegistry r = LVMVarRegistry (YulLVMCtx r)

-- The internal api to handle yulvar registry in a continuation.
with_yulvar_registry :: forall r v b.
  KnownNat v =>
  (YulVarRegistry r ⊸ YulLVM v v r (Maybe (YulVarRegistry r), b)) ⊸
  YulLVM v v r b
with_yulvar_registry f = MkLVM \(MkYulLVMCtx vt mbRgstr) ->
  let ctx' = MkYulLVMCtx vt Nothing {- passing the registry through the continuation directly -}
      !(dict, ctx'', (mbRgstr', b)) = case mbRgstr of
        Just rgstr -> unLVM (f rgstr) ctx'
        Nothing    -> lseq (error "registry was destroyed" :: ()) (UnsafeLinear.coerce (f, ctx'))
      vt' = case ctx'' of
        (MkYulLVMCtx vt'' Nothing) -> vt''
        err                        -> lseq (error "nonsense" :: ()) (UnsafeLinear.coerce err)
  in (dict, MkYulLVMCtx vt' mbRgstr', b)

--
-- YulLVM Context
--

-- YulLVMCtx
--

-- | Context needed for the LVM to be a 'YulLVM'.
data YulLVMCtx r where
  -- ^ All arrows are linear so that no yul ports can escape.
  MkYulLVMCtx ::
    VersionThread r          ⊸ -- ^ A version thread for the yul ports.
    Maybe (YulVarRegistry r) ⊸ -- ^ An operating (Just) or consumed (Nothing) YulVar registry.
    YulLVMCtx r

mk_yullvm_ctx :: forall ioe r. YulO1 r => P'x ioe r () ⊸ YulLVMCtx r
mk_yullvm_ctx u = MkYulLVMCtx (vtstart u) Nothing

rm_yullvm_ctx :: forall ioe r. YulO1 r => YulLVMCtx r ⊸ P'x ioe r ()
rm_yullvm_ctx (MkYulLVMCtx vt mbRgstr) =
  case mbRgstr of
    Nothing -> ()
    err     -> lseq (error "rm_yullvm_ctx: registry not consumed" :: ()) (UnsafeLinear.coerce err)
  `lseq` unsafeCoerceYulPort (vtstop vt)

instance YulO2 r a => ContextualConsumable (YulLVMCtx r) (P'x eff r a) where
  contextualConsume (MkYulLVMCtx vt rgstr) x = MkYulLVMCtx (vtgulp vt x) rgstr

-- Fine-grained ContextualSeqable
--

instance (YulO3 r a b) => ContextualSeqable (YulLVMCtx r) (P'P r a) (P'P r b) where
  contextualSeq ctx a b = (ctx, const'l b a)

instance (YulO3 r a b) => ContextualSeqable (YulLVMCtx r) (P'P r a) (P'V vb r b) where
  contextualSeq ctx a b = (ctx, const'l b (unsafeCoerceYulPort a))

instance (YulO3 r a b) => ContextualSeqable (YulLVMCtx r) (P'V va r a) (P'P r b) where
  contextualSeq ctx a b = (ctx, const'l b (unsafeCoerceYulPort a))

-- When both ports are versioned, it is important to thread them in the right sequence to avoid out-of-order side
-- effects.
instance (KnownNat va, KnownNat vb, va <= vb, YulO3 r a b) =>
         ContextualSeqable (YulLVMCtx r) (P'V va r a) (P'V vb r b) where
  contextualSeq (MkYulLVMCtx vt mbRgstr) a b =
    let !(vt', b') = vtseq (vt, a) b
    in (MkYulLVMCtx vt' mbRgstr, b')

-- Other Linear Context Instances
--

instance YulO2 r a => ContextualDupable (YulLVMCtx r) (P'x eff r a) where
  contextualDup ctx x = (ctx, dup'l x)

instance YulO2 r a => ContextualEmbeddable (YulLVMCtx r) (P'x eff r) a where
  contextualEmbed (MkYulLVMCtx vt mbRgstr) x'p =
    let !(vt', u') = vtmkunit vt
        x'v = emb'l x'p u'
    in (MkYulLVMCtx vt' mbRgstr, x'v)

-- LinearlyVersionRestrictable
--

instance (KnownNat v, YulO2 a r) => LinearlyVersionRestrictable v (YulLVMCtx r) (P'P r a) where
  type instance LinearlyVersionRestricted (YulLVMCtx r) (P'P r a) v = P'V v r a
  restrictVersion a = LVM.pure (unsafeCoerceYulPort a)

instance (KnownNat v, YulO2 a r) => LinearlyVersionRestrictable v (YulLVMCtx r) (P'V v r a) where
  type instance LinearlyVersionRestricted (YulLVMCtx r) (P'V v r a) v = P'V v r a
  restrictVersion = LVM.pure

------------------------------------------------------------------------------------------------------------------------
-- $YulVarRefAPI
-- * Yul VarRef API
------------------------------------------------------------------------------------------------------------------------

--
-- Uv, Rv
--

-- | Yul VarRef Unrestricted in-version (Uv).
type UvYulVarRef r a = UvLVMVarRef (YulLVMCtx r) (P'P r a)

-- | Wrapper of 'UvYulVarRef' in two letters.
data Uv r a where Uv :: forall r a. UvYulVarRef r a -> Uv r a
type role Uv nominal nominal

-- | Yul VarRef restricted in-version (Rv) .
type RvYulVarRef v r a = RvLVMVarRef (YulLVMCtx r) v (P'V v r a)

-- | Wrapper of 'RvYulVarRef' in two letters.
data Rv v r a where Rv :: forall v r a. RvYulVarRef v r a -> Rv v r a
type role Rv nominal nominal nominal

--
-- MakeableYulVarRef
--

class MakeableYulVarRef v r port_ ref_ | v port_ -> ref_, ref_ -> port_ where
  ymkref :: forall a. (KnownNat v, YulO2 a r) => port_ a ⊸ YulLVM v v r (Ur (ref_ a))

instance MakeableYulVarRef v r (P'P r) (Uv r) where
  ymkref x = with_yulvar_registry \rgstr ->
    let !(Ur var, rgstr') = registerUvLVMVar x rgstr
    in LVM.pure (Just rgstr', Ur (Uv var))

instance MakeableYulVarRef v r (P'V v r) (Rv v r) where
  ymkref x = with_yulvar_registry \rgstr ->
    let !(Ur var, rgstr') = registerRvLVMVar x rgstr
    in LVM.pure (Just rgstr', Ur (Rv var))

class MakeableYulVarRef v r port_ ref_ => MakeableYulVarRefNP xs v r port_ ref_ where
  ymkrefNP :: forall. (KnownNat v, YulO2 r (NP xs)) => NP (MapList port_ xs) ⊸ YulLVM v v r (NP (MapList ref_ xs))

instance MakeableYulVarRef v r port_ ref_ => MakeableYulVarRefNP '[] v r port_ ref_ where
  ymkrefNP Nil = LVM.pure Nil

instance ( MakeableYulVarRef v r port_ ref_
         , YulO2 x (NP xs)
         , MakeableYulVarRefNP xs v r port_ ref_
         ) => MakeableYulVarRefNP (x:xs) v r port_ ref_ where
  ymkrefNP (x :* xs) = LVM.do
    (Ur xref) <- ymkref x
    xsrefs <- ymkrefNP @xs @v @r @port_ @ref_ xs
    LVM.pure (xref :* xsrefs)

--
-- ReferenciableYulVar, DereferenceYulVar
--

type ReferenciableYulVar v r ref = ReferenciableLVMVar v ref (YulLVMCtx r) (DereferenceYulVar ref)

type family DereferenceXv ref = port | port -> ref where
  DereferenceXv (Uv r a)   = P'P r a
  DereferenceXv (Rv v r a) = P'V v r a

type family DereferenceYulVar ref = port | port -> ref where
  DereferenceYulVar (UvYulVarRef r a)   = P'P r a
  DereferenceYulVar (RvYulVarRef v r a) = P'V v r a

ypure :: forall a v r ie ref_.
  ( KnownNat v, YulO2 a r
  , DereferenceXv (ref_ a) ~ P'x ie r a
  , MakeableYulVarRef v r (P'x ie r) ref_
  ) =>
  P'x ie r a ⊸ YulLVM v v r (ref_ a)
ypure a = ymkref a LVM.>>= \(Ur var) -> LVM.pure var

-- | Generate a unit monadically.
yembed :: forall a v r ie ref_.
  ( KnownNat v, YulO2 r a
  , DereferenceXv (ref_ a) ~ P'x ie r a
  , MakeableYulVarRef v r (P'x ie r) ref_
  ) => a -> YulLVM v v r (ref_ a)
yembed a = embed a LVM.>>= ypure

--
-- AnyYulVarRef
--

data AnyYulVarRef v r a where
  AnyUv :: forall v r a. UvYulVarRef   r a -> AnyYulVarRef v r a
  AnyRv :: forall v r a. RvYulVarRef v r a -> AnyYulVarRef v r a

-- TODO: to make this version work some day
-- type AnyYulVarRef v r = forall ref. ReferenciableLVMVar v ref (YulLVMCtx r) (DereferenceYulVar ref) => ref

--
-- YTakeableVarRefNP (ytakeUvNP, ytakeAnyNP), ytakeUvN, ytakeAnyN
--

class YTakeableVarRefNP v xs r where
  ytakeUvNP :: forall m1 m2.
    ( KnownNat v
    , Uv r ~ m1
    , P'P r ~ m2
    ) =>
    NP (MapList m1 xs) ⊸
    YulLVM v v r (NP (MapList m2 xs))

  ytakeAnyNP :: forall m1 m2.
    ( KnownNat v
    , AnyYulVarRef v r ~ m1
    , P'V v r ~ m2
    ) =>
    NP (MapList m1 xs) ⊸
    YulLVM v v r (NP (MapList m2 xs))

instance YTakeableVarRefNP v '[] r where
  ytakeUvNP Nil = LVM.pure Nil
  ytakeAnyNP Nil = LVM.pure Nil

instance (YulO2 x r, YTakeableVarRefNP v xs r) => YTakeableVarRefNP v (x:xs) r where
  ytakeUvNP np = LVM.do
    (x', xsref') <- with_yulvar_registry \rgstr -> LVM.do
      let !(Uv xref, xsref) = splitNonEmptyNP np
      (x, rgstr') <- takeLVMVarRef xref rgstr
      LVM.pure (Just rgstr', (x, xsref))
    xs <- ytakeUvNP @v @xs xsref'
    LVM.pure (x' :* xs)

  ytakeAnyNP np = LVM.do
    (x', xsref') <- with_yulvar_registry \rgstr -> LVM.do
      let !(axref, xsref) = splitNonEmptyNP np
      (x, rgstr') <- case axref of
        AnyUv xref -> takevLVMVarRef xref rgstr
        AnyRv xref -> takevLVMVarRef xref rgstr
      LVM.pure (Just rgstr', (x, xsref))
    xs <- ytakeAnyNP @v @xs xsref'
    LVM.pure (x' :* xs)

ytakeUvN :: forall v aN xs r m1 m2.
  ( KnownNat v
  , Uv r ~ m1
  , P'P r ~ m2
  , ConvertibleTupleNtoNP aN
  , TupleNtoNP aN ~ NP (MapList m1 xs)
  , ConvertibleNPtoTupleN (NP (MapList m1 xs))
  , ConvertibleNPtoTupleN (NP (MapList m2 xs))
  , YTakeableVarRefNP v xs r
  ) =>
  aN ->
  YulLVM v v r (NPtoTupleN (NP (MapList m2 xs)))
ytakeUvN tpl = ytakeUvNP @v @xs (fromTupleNtoNP tpl) LVM.>>= LVM.pure . fromNPtoTupleN

ytakeAnyN :: forall v xs r m1 m2.
  ( KnownNat v
  , AnyYulVarRef v r ~ m1
  , P'V v r ~ m2
  , ConvertibleNPtoTupleN (NP (MapList m1 xs))
  , ConvertibleNPtoTupleN (NP (MapList m2 xs))
  , YTakeableVarRefNP v xs r
  ) =>
  NPtoTupleN (NP (MapList m1 xs)) ->
  YulLVM v v r (NPtoTupleN (NP (MapList m2 xs)))
ytakeAnyN tpl = ytakeAnyNP @v @xs (fromTupleNtoNP tpl) LVM.>>= LVM.pure . fromNPtoTupleN

--
-- ytake1, ytakev1
--

ytake1 :: forall ref v r ioe a.
  ( ReferenciableYulVar v r ref
  , DereferenceYulVar ref ~ P'x ioe r a
  ) =>
  ref ->
  YulLVM v v r (P'x ioe r a)
ytake1 ref = with_yulvar_registry \rgstr -> LVM.do
  (x, rgstr') <- takeLVMVarRef ref rgstr
  LVM.pure (Just rgstr', x)

ytakev1 :: forall ref v a r.
  ( ReferenciableYulVar v r ref
  , LinearlyVersionRestricted (YulLVMCtx r) (DereferenceYulVar ref) v ~ P'V v r a
  ) =>
  ref ->
  YulLVM v v r (P'V v r a)
ytakev1 ref = with_yulvar_registry \rgstr -> LVM.do
  (x, rgstr') <- takevLVMVarRef ref rgstr
  LVM.pure (Just rgstr', x)

-- TODO: ytakeN, ytakevN

--
-- ywithUv, ywithAny
--

type ConstraintForYWith f x xs b bs btpl f' v r m1 m1b m2 mp =
  ( KnownNat v
  , YulO6 x (NP xs) b (NP bs) btpl r
    -- f
  , EquivalentNPOfFunction f (x:xs) btpl
  , UncurriableNP f (x:xs) btpl m2 m2 m2 m2 Many
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
  , MakeableYulVarRefNP (b:bs) v r mp m1b
    -- btpl
  , NP (b:bs) ~ ABITypeDerivedOf btpl
  )

ywithUv :: forall f x xs b bs btpl f' v r m1 m1b m2.
  ( ConstraintForYWith f x xs b bs btpl f' v r m1 m1b m2 (P'P r)
    -- m1, m1b, m2
  , Uv r ~ m1
  , Uv r ~ m1b
  , YulCat Pure (NP (x:xs)) ~ m2
  ) =>
  NPtoTupleN (NP (MapList (Uv r) (x:xs))) ⊸
  PureY f ->
  YulLVM v v r (NPtoTupleN (NP (MapList (Uv r) (b:bs))))
ywithUv xxstpl f = LVM.do
  xxstpl' <- ytakeUvN @v @_ @(x:xs) xxstpl
  let bbs = withNP'l @f' (fromTupleNtoNP xxstpl') f'
  bbsrefs <- ymkrefNP @(b:bs) bbs
  LVM.pure (fromNPtoTupleN bbsrefs)
  where f' txxs = uncurryNP @f @(x:xs) @btpl @m2 @m2 @m2 @m2 @Many f (distributeNP txxs) >.> YulReduceType

ywithAny :: forall f x xs b bs btpl v r m1 m1b m2 f'.
  ( ConstraintForYWith f x xs b bs btpl f' v r m1 m1b m2 (P'V v r)
    -- m1, m2
  , AnyYulVarRef v r ~ m1
  , Rv v r ~ m1b
  , YulCat Pure (NP (x:xs)) ~ m2
  ) =>
  NPtoTupleN (NP (MapList (AnyYulVarRef v r) (x:xs))) ⊸
  PureY f ->
  YulLVM v v r (NPtoTupleN (NP (MapList (Rv v r) (b:bs))))
ywithAny xxstpl f = LVM.do
  xxstpl' <- ytakeAnyN @v @(x:xs) xxstpl
  let bbs = withNP'l @f' (fromTupleNtoNP xxstpl') f'
  bbsrefs <- ymkrefNP @(b:bs) bbs
  LVM.pure (fromNPtoTupleN bbsrefs)
  where f' txxs = uncurryNP @f @(x:xs) @btpl @m2 @m2 @m2 @m2 @Many f (distributeNP txxs) >.> YulReduceType

------------------------------------------------------------------------------------------------------------------------
-- $YulLVMDiagrams
-- * YulLVM Monadic Diagrams
------------------------------------------------------------------------------------------------------------------------

--
-- uncurry helpers
--

yuncurry_nil :: forall a b r ie m1 va vb.
  ( KnownNat va, KnownNat vb
  , YulO2 a r
  ) =>
  YulLVM va vb r b ⊸
  (m1 a ⊸ P'x ie r (NP '[])) ⊸
  (m1 a ⊸ YulLVM va vb r b)
yuncurry_nil b h a = h a & eject . unsafeCoerceYulPort . coerceType'l @_ @() LVM.>> b

yuncurry_xs :: forall m1 m1b m2_ m2b_ m2' m2b' g x xs b r a ie v1 vn.
  ( YulO4 x (NP xs) r a
  , UncurriableNP g xs b m1 m1b (m2_ a) (m2b_ a) One
  --
  , KnownNat v1, KnownNat vn
  , MakeableYulVarRef v1 r m2' m1 -- m1 |- m2' ∧ m2' |- m1
  , YulLVM v1 vn r ~ m1b -- m1b
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
-- yullvm'pp
--

-- | Monadic yul port diagrams for pure input and yul monad output.
newtype YulCat'LPPM v r a b = MkYulCat'LPPM (P'P r a ⊸ YulLVM v v r b)

instance forall b v r a.
         ( KnownNat v
         , YulO3 b r a
         ) =>
         UncurriableNP (Uv r b) '[] (Uv r b)
         (Uv r) (YulLVM v v r) (YulCat'LPP r a) (YulCat'LPPM v r a) One where
  uncurryNP b (MkYulCat'LPP h) = MkYulCat'LPPM (yuncurry_nil b h)

instance forall x xs b g v r a.
         ( KnownNat v
         , EquivalentNPOfFunction g xs (Uv r b)
         , YulO5 x (NP xs) b r a
         , UncurriableNP g xs (Uv r b) (Uv r) (YulLVM v v r) (YulCat'LPP r a) (YulCat'LPPM v r a) One
         ) =>
         UncurriableNP (x -> g) (x:xs) (Uv r b)
         (Uv r) (YulLVM v v r) (YulCat'LPP r a) (YulCat'LPPM v r a) One where
  uncurryNP f (MkYulCat'LPP h) = MkYulCat'LPPM $ yuncurry_xs f h MkYulCat'LPP (\(MkYulCat'LPPM g) -> g)

yullvm'pp :: forall xs b f m1 m1b m2 m2b r b'.
  ( YulO3 (NP xs) b r
  , Uv             r ~ m1
  , YulLVM   0 0 r ~ m1b
  , YulCat'LPP    r (NP xs) ~ m2
  , YulCat'LPPM 0 r (NP xs) ~ m2b
  -- b'
  , Uv r b ~ b'
  -- f'
  , UncurriableNP f xs b' m1 m1b m2 m2b One
  ) =>
  LiftFunction f m1 m1b One ->
  (P'P r (NP xs) ⊸ P'P r b)
yullvm'pp f =
  let !(MkYulCat'LPPM f') = uncurryNP @f @xs @b' @m1 @m1b @m2 @m2b @One f (MkYulCat'LPP id)
  in \xs -> let !(xs', u) = mkUnit'l xs in unsafeCoerceYulPort $ runYulLVM u $ LVM.do
    Uv bvar <- f' xs'
    ytakev1 bvar

instance forall b v r a.
         YulO2 r a =>
         CurriableNP (Uv r b) '[] (Uv r b)
         (Uv r) (YulLVM v v r) (YulCat'LPP r a) One where
  curryNP fNP = fNP (MkYulCat'LPP (\a -> coerceType'l (discard'l a)))

instance forall x xs b g r a v.
         ( YulO4 x (NP xs) r a
         , CurriableNP g xs (Uv r b) (Uv r) (YulLVM v v r) (YulCat'LPP r a) One
           --
         , KnownNat v
         , ReferenciableYulVar v r (UvYulVarRef r b)
         ) =>
         CurriableNP (x -> g) (x:xs) (Uv r b)
         (Uv r) (YulLVM v v r) (YulCat'LPP r a) One where
  curryNP fNP (Uv xref) = curryNP @g @xs @(Uv r b) @(Uv r) @(YulLVM v v r) @(YulCat'LPP r a) @One
    (\(MkYulCat'LPP fxs) -> ytake1 xref LVM.>>= \x -> fNP (MkYulCat'LPP (\a -> consNP x (fxs a))))

--
-- yullvm'pv
--

-- | Monadic yul port diagrams for pure input and yul monad output.
newtype YulCat'LPVM v1 vn r a b = MkYulCat'LPVM (P'P r a ⊸ YulLVM v1 vn r b)

instance forall b v1 vn r a.
         ( KnownNat v1, KnownNat vn
         , YulO3 b r a
         ) =>
         UncurriableNP (Rv vn r b) '[] (Rv vn r b)
         (Uv r) (YulLVM v1 vn r) (YulCat'LPP r a) (YulCat'LPVM v1 vn r a) One where
  uncurryNP b (MkYulCat'LPP h) = MkYulCat'LPVM (yuncurry_nil b h)

instance forall x xs b g v1 vn r a.
         ( KnownNat v1, KnownNat vn
         , YulO5 x (NP xs) b r a
         , UncurriableNP g xs (Rv vn r b) (Uv r) (YulLVM v1 vn r) (YulCat'LPP r a) (YulCat'LPVM v1 vn r a) One
         ) =>
         UncurriableNP (x -> g) (x:xs) (Rv vn r b)
         (Uv r) (YulLVM v1 vn r) (YulCat'LPP r a) (YulCat'LPVM v1 vn r a) One where
  uncurryNP f (MkYulCat'LPP h) = MkYulCat'LPVM $ yuncurry_xs f h MkYulCat'LPP (\(MkYulCat'LPVM g) -> g)

yullvm'pv :: forall xs b r vd m1 m1b m2 m2b f b'.
  ( KnownNat vd
  , YulO3 (NP xs) b r
  -- m1, m1b, m2, m2b
  , Uv          r ~ m1
  , YulLVM 0 vd r ~ m1b
  , YulCat'LPP       r (NP xs) ~ m2
  , YulCat'LPVM 0 vd r (NP xs) ~ m2b
  -- b'
  , Rv vd r b ~ b'
  -- f'
  , UncurriableNP f xs b' m1 m1b m2 m2b One
  ) =>
  LiftFunction f m1 m1b One ->
  (P'P r (NP xs) ⊸ P'V vd r b)
yullvm'pv f =
  let !(MkYulCat'LPVM f') = uncurryNP @f @xs @b' @m1 @m1b @m2 @m2b @One f (MkYulCat'LPP id)
  in \xs -> let !(xs', u) = mkUnit'l xs in unsafeCoerceYulPort $ runYulLVM u $ LVM.do
    Rv bvar <- f' xs'
    ytakev1 bvar

instance forall b v1 vn r a.
         YulO2 r a =>
         CurriableNP (Rv vn r b) '[] (Rv vn r b)
         (Uv r) (YulLVM v1 vn r) (YulCat'LPP r a) One where
  curryNP fNP = fNP (MkYulCat'LPP (\a -> coerceType'l (discard'l a)))

instance forall x xs b g r a v1 vn.
         ( YulO4 x (NP xs) r a
         , CurriableNP g xs (Rv vn r b) (Uv r) (YulLVM v1 vn r) (YulCat'LPP r a) One
           --
         , KnownNat v1, KnownNat vn
         , ReferenciableYulVar v1 r (UvYulVarRef r b)
         ) =>
         CurriableNP (x -> g) (x:xs) (Rv vn r b)
         (Uv r) (YulLVM v1 vn r) (YulCat'LPP r a) One where
  curryNP fNP (Uv xref) = curryNP @g @xs @(Rv vn r b) @(Uv r) @(YulLVM v1 vn r) @(YulCat'LPP r a) @One
    (\(MkYulCat'LPP fxs) -> ytake1 xref LVM.>>= \x -> fNP (MkYulCat'LPP (\a -> consNP x (fxs a))))

--
-- yullvm'vv
--

-- | Monadic yul port diagrams for pure input and yul monad output.
newtype YulCat'LVVM v1 vn r a b = MkYulCat'LVVM (P'V v1 r a ⊸ YulLVM v1 vn r b)

instance forall b v1 vn r a.
         ( KnownNat v1, KnownNat vn
         , YulO3 b r a
         ) =>
         UncurriableNP (Rv vn r b) '[] (Rv vn r b)
         (Rv v1 r) (YulLVM v1 vn r) (YulCat'LVV v1 v1 r a) (YulCat'LVVM v1 vn r a) One where
  uncurryNP b (MkYulCat'LVV h) = MkYulCat'LVVM (yuncurry_nil b h)

instance forall x xs b g v1 vn r a.
         ( EquivalentNPOfFunction g xs (Rv vn r b)
         , UncurriableNP g xs (Rv vn r b) (Rv v1 r) (YulLVM v1 vn r) (YulCat'LVV v1 v1 r a) (YulCat'LVVM v1 vn r a) One
           --
         , YulO5 x (NP xs) b r a
         , KnownNat v1, KnownNat vn
         ) =>
         UncurriableNP (x -> g) (x:xs) (Rv vn r b)
         (Rv v1 r) (YulLVM v1 vn r) (YulCat'LVV v1 v1 r a) (YulCat'LVVM v1 vn r a) One where
  uncurryNP f (MkYulCat'LVV h) = MkYulCat'LVVM $ yuncurry_xs f h MkYulCat'LVV (\(MkYulCat'LVVM g) -> g)

yullvm'vv :: forall xs b r vd m1 m1b m2 m2b f b'.
  ( KnownNat vd
  , YulO3 (NP xs) b r
  -- m1, m1b, m2, m2b
  , Rv          0 r ~ m1
  , YulLVM   0 vd r ~ m1b
  , YulCat'LVV  0 0  r (NP xs) ~ m2
  , YulCat'LVVM 0 vd r (NP xs) ~ m2b
  -- b'
  , Rv vd r b ~ b'
  -- f'
  , UncurriableNP f xs b' m1 m1b m2 m2b One
  ) =>
  LiftFunction f m1 m1b One ->
  (P'V 0 r (NP xs) ⊸ P'V vd r b)
yullvm'vv f =
  let !(MkYulCat'LVVM f') = uncurryNP @f @xs @b' @m1 @m1b @m2 @m2b @One f (MkYulCat'LVV id)
  in \xs -> let !(xs', u) = mkUnit'l xs in unsafeCoerceYulPort $ runYulLVM u $ LVM.do
    Rv bvar <- f' xs'
    ytakev1 bvar

instance forall b v1 vn r a.
         YulO2 r a =>
         CurriableNP (Rv vn r b) '[] (Rv vn r b)
         (Rv v1 r) (YulLVM v1 vn r) (YulCat'LVV v1 v1 r a) One where
  curryNP fNP = fNP (MkYulCat'LVV (\a -> coerceType'l (discard'l a)))

instance forall x xs b g r a v1 vn.
         ( YulO4 x (NP xs) r a
         , CurriableNP g xs (Rv vn r b) (Rv v1 r) (YulLVM v1 vn r) (YulCat'LVV v1 v1 r a) One
           --
         , KnownNat v1, KnownNat vn
         , ReferenciableYulVar v1 r (RvYulVarRef v1 r b)
         ) =>
         CurriableNP (x -> g) (x:xs) (Rv vn r b)
         (Rv v1 r) (YulLVM v1 vn r) (YulCat'LVV v1 v1 r a) One where
  curryNP fNP (Rv xref) = curryNP @g @xs @(Rv vn r b) @(Rv v1 r) @(YulLVM v1 vn r) @(YulCat'LVV v1 v1 r a) @One
    (\(MkYulCat'LVV fxs) -> ytake1 xref LVM.>>= \x -> fNP (MkYulCat'LVV (\a -> consNP x (fxs a))))

--
-- curryNP'vv instances
--

instance forall b v1 vn r a.
         ( YulO2 r a
         ) =>
         CurriableNP (P'V vn r b) '[] (P'V vn r b)
         (P'V v1 r) (YulLVM v1 vn r) (YulCat'LVV v1 v1 r a) One where
  curryNP fNP = fNP (MkYulCat'LVV (\a -> coerceType'l (discard'l a)))

instance forall g x xs b r a v1 vn.
         ( YulO4 x (NP xs) r a
         , CurriableNP g xs b (P'V v1 r) (YulLVM v1 vn r) (YulCat'LVV v1 v1 r a) One
         ) =>
         CurriableNP (x -> g) (x:xs) b
         (P'V v1 r) (YulLVM v1 vn r) (YulCat'LVV v1 v1 r a) One where
  curryNP fNP x = curryNP @g @xs @b @(P'V v1 r) @(YulLVM v1 vn r) @(YulCat'LVV v1 v1 r a) @One
                  (\(MkYulCat'LVV fxs) -> fNP (MkYulCat'LVV (\a -> (consNP x (fxs a)))))
