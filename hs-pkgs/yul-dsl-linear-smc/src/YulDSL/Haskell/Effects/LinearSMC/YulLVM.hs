{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances   #-}
module YulDSL.Haskell.Effects.LinearSMC.YulLVM
  ( -- * Yul Monad
    YulLVM, runYulLVM
  , ypure, yembed
  , Uv (Uv), Rv (Rv)
  , withYulVarRegistry, ymkref, ytake, ytakev
    -- * Yul Monadic Diagrams
  , YulCat'LVM (MkYulCat'LVM), YulCat'LPM (MkYulCat'LPM)
  , yullvm'pp, yullvm'pv, yullvm'vv
    -- * Other LVM Primitives
  , module Control.LinearlyVersionedMonad.Combinators
  , module Control.LinearlyVersionedMonad.LVMVar
  -- FIXME to be deleted
  , yullvm'v, yullvm'p, withinPureY
  ) where
-- base
import GHC.TypeLits                                  (KnownNat)
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
-- YulLVM: A Linearly Versioned Monad for YulDSL
------------------------------------------------------------------------------------------------------------------------

-- | YulLVM is a linear versioned monad with 'YulLVMCtx' as its context data.
type YulLVM va vb r = LVM (YulLVMCtx r) va vb

-- | Run a YulLVM with an initial unit port and returns a versioned result.
runYulLVM :: forall b vd r ie.
  ( KnownNat vd
  , YulO2 r b
  ) =>
  P'x ie r () ⊸ YulLVM 0 vd r (P'V vd r b) ⊸ P'V vd r b
runYulLVM u m = let ctx = mkYulLVMCtx u
                    !(ctx', b) = runLVM ctx mWrapper
                in rmYulLVMCtx ctx' b
  where -- wrap given monad with var registry init/consume block
        mWrapper = LVM.do
          initRgstr
          b <- m
          consumeRgstr
          LVM.pure b
        -- initialize the var registry
        initRgstr :: YulLVM 0 0 r ()
        initRgstr = MkLVM \(MkYulLVMCtx ud mbRgstr) ->
          let rgstr = case mbRgstr of
                Nothing -> initLVMVarRegistry
                err     -> lseq (error "initRgstr: registry should be empty" :: ()) (UnsafeLinear.coerce err)
          in (Dict, MkYulLVMCtx ud (Just rgstr), ())
        -- consume the var registry
        -- consumeRgstr :: YulLVM vd vd r ()
        consumeRgstr = withYulVarRegistry \rgstr -> LVM.do
          consumeLVMVarRegistry rgstr
          LVM.pure (Nothing, ())

-- An alias to 'LVM.pure' to avoid naming conflict with Monad pure function.
ypure :: forall a v r. KnownNat v => P'V v r a ⊸ YulLVM v v r (P'V v r a)
ypure = LVM.pure

-- | Generate a unit monadically.
yembed :: forall a v r. (KnownNat v, YulO2 r a) => a -> YulLVM v v r (P'V v r a)
yembed = embed

------------------------------------------------------------------------------------------------------------------------
-- YulLVM Context
------------------------------------------------------------------------------------------------------------------------

type YulVarRegistry r = LVMVarRegistry (YulLVMCtx r)

-- | Context needed for the LVM to be a 'YulLVM'.
data YulLVMCtx r where
  -- ^ All arrows are linear so that no yul ports can escape.
  MkYulLVMCtx :: YulPortUniter r ⊸ Maybe (YulVarRegistry r) ⊸ YulLVMCtx r

mkYulLVMCtx ::  P'x ie r () ⊸ YulLVMCtx r
mkYulLVMCtx u = MkYulLVMCtx (MkYulPortUniter (unsafeCoerceYulPort u)) Nothing

rmYulLVMCtx :: YulO2 b r => YulLVMCtx r ⊸ P'x oe r b ⊸ P'x oe r b
rmYulLVMCtx (MkYulLVMCtx (MkYulPortUniter u) mbRgstr) =
  case mbRgstr of
    Nothing -> ()
    err     -> lseq (error "rmYulLVMCtx: registry not consumed" :: ()) (UnsafeLinear.coerce err)
  `lseq` ignore'l (unsafeCoerceYulPort u)

instance YulO2 r a => ContextualConsumable (YulLVMCtx r) (P'x eff r a) where

  contextualConsume (MkYulLVMCtx ud rgstr) x = MkYulLVMCtx (yulPortUniterGulp ud x) rgstr

instance YulO3 r a b => ContextualSeqable (YulLVMCtx r) (P'x eff1 r a) (P'x eff2 r b) where
  contextualSeq (MkYulLVMCtx ud mbRgstr) a b =
    let ud' = yulPortUniterGulp ud a
        !(ud'', u') = yulPortUniterMkUnit ud'
        b' = ignore'l u' b
    in (MkYulLVMCtx ud'' mbRgstr, b')

instance YulO2 r a => ContextualDupable (YulLVMCtx r) (P'x eff r a) where
  contextualDup ctx x = (ctx, dup2'l x)

instance YulO2 r a => ContextualEmbeddable (YulLVMCtx r) (P'x eff r) a where
  contextualEmbed (MkYulLVMCtx ud mbRgstr) x'p =
    let !(ud', u') = yulPortUniterMkUnit ud
        x'v = emb'l x'p u'
    in (MkYulLVMCtx ud' mbRgstr, x'v)

instance (KnownNat v, YulO2 a r) => LinearlyVersionRestrictable v (YulLVMCtx r) (P'P r a) where
  type instance LinearlyVersionRestricted (YulLVMCtx r) (P'P r a) v = P'V v r a
  restrictVersion a = LVM.pure (unsafeCoerceYulPort a)

instance (KnownNat v, YulO2 a r) => LinearlyVersionRestrictable v (YulLVMCtx r) (P'V v r a) where
  type instance LinearlyVersionRestricted (YulLVMCtx r) (P'V v r a) v = P'V v r a
  restrictVersion = LVM.pure

------------------------------------------------------------------------------------------------------------------------
-- LVMVar API
------------------------------------------------------------------------------------------------------------------------

withYulVarRegistry :: forall r v b.
  KnownNat v =>
  (YulVarRegistry r ⊸ YulLVM v v r (Maybe (YulVarRegistry r), b)) ⊸
  YulLVM v v r b
withYulVarRegistry f = MkLVM \(MkYulLVMCtx ud mbRgstr) ->
  let ctx' = MkYulLVMCtx ud Nothing
      !(dict, ctx'', (mbRgstr', b)) = case mbRgstr of
        Just rgstr -> unLVM (f rgstr) ctx'
        Nothing    -> lseq (error "withYulVarRegistry: registry should exist" :: ()) (UnsafeLinear.coerce (f, ctx'))
      ud' = case ctx'' of
        (MkYulLVMCtx ud'' Nothing) -> ud''
        err                        -> lseq (error "withYulVarRegistry: nonsense" :: ()) (UnsafeLinear.coerce err)
  in (dict, MkYulLVMCtx ud' mbRgstr', b)

type YulUvVar r a = UvLVMVarRef (YulLVMCtx r) (P'P r a)
data Uv r a where Uv :: forall a r. YulUvVar r a -> Uv r a
type role Uv nominal nominal

type YulRvVar v r a = RvLVMVarRef (YulLVMCtx r) v (P'V v r a)
data Rv v r a where Rv :: forall a v r. YulRvVar v r a -> Rv v r a
type role Rv nominal nominal nominal

type family ReferencedYulVar ref = port | port -> ref where
  ReferencedYulVar (YulUvVar r a)   = P'P r a
  ReferencedYulVar (YulRvVar v r a) = P'V v r a

type ReferenciableYulVar v r ref = ReferenciableLVMVar v ref (YulLVMCtx r) (ReferencedYulVar ref)

class MakeableYulRef v r port ref | v port -> ref, ref -> port where
  ymkref :: forall. (KnownNat v, YulO1 r) => port ⊸ YulLVM v v r (Ur ref)

instance YulO1 a => MakeableYulRef v r (P'P r a) (Uv r a) where
  ymkref x = withYulVarRegistry \rgstr ->
    let !(Ur var, rgstr') = registerUvLVMVar x rgstr
    in LVM.pure (Just rgstr', Ur (Uv var))

instance YulO1 a => MakeableYulRef v r (P'V v r a) (Rv v r a) where
  ymkref x = withYulVarRegistry \rgstr ->
    let !(Ur var, rgstr') = registerRvLVMVar x rgstr
    in LVM.pure (Just rgstr', Ur (Rv var))

ytake :: forall ref v r ioe a.
  ( ReferenciableYulVar v r ref
  , ReferencedYulVar ref ~ P'x ioe r a
  ) =>
  ref ->
  YulLVM v v r (ReferencedYulVar ref)
ytake ref = withYulVarRegistry \rgstr -> LVM.do
  (x, rgstr') <- takeLVMVarRef ref rgstr
  LVM.pure (Just rgstr', x)

ytakev :: forall ref v r a.
  ( ReferenciableYulVar v r ref
  , LinearlyVersionRestricted (YulLVMCtx r) (ReferencedYulVar ref) v ~ P'V v r a
  ) =>
  ref ->
  YulLVM v v r (P'V v r a)
ytakev ref = withYulVarRegistry \rgstr -> LVM.do
  (x, rgstr') <- takevLVMVarRef ref rgstr
  LVM.pure (Just rgstr', x)

------------------------------------------------------------------------------------------------------------------------
-- yullvm'{pp, pv, vv}
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
  , MakeableYulRef v1 r (m2' x) (m1 x) -- m1 |- m2' ∧ m2' |- m1
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
  let !(a1, a2) = dup2'l a
      !(x, xs) = unconsNP (h a1)
  in ymkref x LVM.>>= \(Ur xref) ->
    let g = uncurryNP @g @xs @b @m1 @m1b @(m2_ a) @(m2b_ a) @One
            (f xref)
            (mk (\a' -> ignore'l (discard'l a') xs))
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
    ytakev bvar

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
         , ReferenciableYulVar v r (YulUvVar r b)
         ) =>
         CurriableNP (x -> g) (x:xs) (Uv r b)
         (Uv r) (YulLVM v v r) (YulCat'LPP r a) One where
  curryNP fNP (Uv xref) = curryNP @g @xs @(Uv r b) @(Uv r) @(YulLVM v v r) @(YulCat'LPP r a) @One
    (\(MkYulCat'LPP fxs) -> ytake xref LVM.>>= \x -> fNP (MkYulCat'LPP (\a -> consNP x (fxs a))))

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
         ( EquivalentNPOfFunction g xs (Rv vn r b)
         , UncurriableNP g xs (Rv vn r b) (Uv r) (YulLVM v1 vn r) (YulCat'LPP r a) (YulCat'LPVM v1 vn r a) One
         , KnownNat v1, KnownNat vn
         , YulO5 x (NP xs) b r a
         ) =>
         UncurriableNP (x -> g) (x:xs) (Rv vn r b)
         (Uv r) (YulLVM v1 vn r) (YulCat'LPP r a) (YulCat'LPVM v1 vn r a) One where
  uncurryNP f (MkYulCat'LPP h) = MkYulCat'LPVM $ yuncurry_xs f h MkYulCat'LPP (\(MkYulCat'LPVM g) -> g)

yullvm'pv :: forall xs b r vd m1 m1b m2 m2b f b'.
  ( KnownNat vd
  , YulO3 (NP xs) b r
  -- m1, m1b, m2, m2b
  , Rv         vd r ~ m1
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
    ytakev bvar

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
         , ReferenciableYulVar v1 r (YulUvVar r b)
         ) =>
         CurriableNP (x -> g) (x:xs) (Rv vn r b)
         (Uv r) (YulLVM v1 vn r) (YulCat'LPP r a) One where
  curryNP fNP (Uv xref) = curryNP @g @xs @(Rv vn r b) @(Uv r) @(YulLVM v1 vn r) @(YulCat'LPP r a) @One
    (\(MkYulCat'LPP fxs) -> ytake xref LVM.>>= \x -> fNP (MkYulCat'LPP (\a -> consNP x (fxs a))))

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
  , Rv         vd r ~ m1
  , YulLVM 0 vd r ~ m1b
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
    ytakev bvar

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
         , ReferenciableYulVar v1 r (YulRvVar v1 r b)
         ) =>
         CurriableNP (x -> g) (x:xs) (Rv vn r b)
         (Rv v1 r) (YulLVM v1 vn r) (YulCat'LVV v1 v1 r a) One where
  curryNP fNP (Rv xref) = curryNP @g @xs @(Rv vn r b) @(Rv v1 r) @(YulLVM v1 vn r) @(YulCat'LVV v1 v1 r a) @One
    (\(MkYulCat'LVV fxs) -> ytake xref LVM.>>= \x -> fNP (MkYulCat'LVV (\a -> consNP x (fxs a))))























------------------------------------------------------------------------------------------------------------------------
-- !!!!!!!!!!!!!!!!!!!!!!!!!!!! TO BE DELETED !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
------------------------------------------------------------------------------------------------------------------------

------------------------------------------------------------------------------------------------------------------------
-- yullvm'p
------------------------------------------------------------------------------------------------------------------------

-- | Monadic yul port diagrams for pure input and yul monad output.
newtype YulCat'LPM v1 vn r a b = MkYulCat'LPM (P'P r a ⊸ YulLVM v1 vn r b)

instance forall b v1 vn r a.
         ( KnownNat v1, KnownNat vn
         , YulO3 b r a
         ) =>
         UncurriableNP (P'V vn r b) '[] (P'V vn r b)
         (P'P r) (YulLVM v1 vn r) (YulCat'LPP r a) (YulCat'LPM v1 vn r a) One where
  uncurryNP b (MkYulCat'LPP h) = MkYulCat'LPM \a -> eject (unsafeCoerceYulPort (h a & coerceType'l @_ @())) LVM.>> b

instance forall x xs b g v1 vn r a.
         ( EquivalentNPOfFunction g xs (P'V vn r b)
         , YulO5 x (NP xs) b r a
         , UncurriableNP g xs (P'V vn r b) (P'P r) (YulLVM v1 vn r) (YulCat'LPP r a) (YulCat'LPM v1 vn r a) One
         ) =>
         UncurriableNP (x -> g) (x:xs) (P'V vn r b)
         (P'P r) (YulLVM v1 vn r) (YulCat'LPP r a) (YulCat'LPM v1 vn r a) One where
  uncurryNP f (MkYulCat'LPP h) = MkYulCat'LPM (uncurryNP'lx f h MkYulCat'LPP (\(MkYulCat'LPM g) -> g))

yullvm'p :: forall xs b r vd m1 m1b m2 m2b f' b'.
  ( KnownNat vd
  , YulO3 (NP xs) b r
  -- m1, m1b, m2, m2b
  , P'P           r ~ m1
  , YulLVM 0 vd r ~ m1b
  , YulCat'LPP      r (NP xs) ~ m2
  , YulCat'LPM 0 vd r (NP xs) ~ m2b
  -- b'
  , P'V vd r b ~ b'
  -- f'
  , UncurriableNP f' xs b' m1 m1b m2 m2b One
  ) =>
  LiftFunction f' m1 m1b One -> -- ^ LiftFunction               f1  m1 m1b One
  (P'P r (NP xs) ⊸ P'V vd r b)  -- ^ LiftFunction (NP (():xs) -> b) m1 m1b One
yullvm'p f =
  let !(MkYulCat'LPM f') = uncurryNP @f' @xs @b' @m1 @m1b @m2 @m2b @One f (MkYulCat'LPP id)
  in \xs -> mkUnit'l xs & \(xs', u) -> runYulLVM u (f' xs')

------------------------------------------------------------------------------------------------------------------------
-- yullvm'v
------------------------------------------------------------------------------------------------------------------------

-- | Monadic yul port diagrams for versioned input and yul monad output.
newtype YulCat'LVM v1 vn r a b = MkYulCat'LVM (P'V v1 r a ⊸ YulLVM v1 vn r b)

instance forall b v1 vn r a.
         ( KnownNat v1, KnownNat vn
         , YulO2 a r
         ) =>
         UncurriableNP (P'V vn r b) '[] (P'V vn r b)
         (P'V v1 r) (YulLVM v1 vn r) (YulCat'LVV v1 v1 r a) (YulCat'LVM v1 vn r a) One where
  uncurryNP b (MkYulCat'LVV h) = MkYulCat'LVM \a -> eject (h a) LVM.>> b

instance forall x xs b g v1 vn r a.
         ( YulO4 x (NP xs) r a
         , UncurriableNP g xs b (P'V v1 r) (YulLVM v1 vn r) (YulCat'LVV v1 v1 r a) (YulCat'LVM v1 vn r a) One
         ) =>
         UncurriableNP (x -> g) (x:xs) b
         (P'V v1 r) (YulLVM v1 vn r)
         (YulCat'LVV v1 v1 r a) (YulCat'LVM v1 vn r a) One where
  uncurryNP f (MkYulCat'LVV h) = MkYulCat'LVM (uncurryNP'lx f h MkYulCat'LVV (\(MkYulCat'LVM g) -> g))

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

yullvm'v :: forall xs b r vd m1 m1b m2 m2b f' b'.
  ( KnownNat vd
  , YulO3 (NP xs) b r
  -- m1, m1b, m2, m2b
  , P'V         0 r ~ m1
  , YulLVM 0 vd r ~ m1b
  , YulCat'LVV 0  0 r (NP xs) ~ m2
  , YulCat'LVM 0 vd r (NP xs) ~ m2b
  -- b'
  , P'V vd r b ~ b'
  -- f'
  , UncurriableNP f' xs b' m1 m1b m2 m2b One
  ) =>
  LiftFunction f' m1 m1b One ->  -- ^ LiftFunction               f1  m1 m1b One
  (P'V 0 r (NP xs) ⊸ P'V vd r b) -- ^ LiftFunction (NP (():xs) -> b) m1 m1b One
yullvm'v f =
  let !(MkYulCat'LVM f') = uncurryNP @f' @xs @b' @m1 @m1b @m2 @m2b @One f (MkYulCat'LVV id)
  in \xs -> mkUnit'l xs & \(xs', u) -> runYulLVM u (f' xs')

------------------------------------------------------------------------------------------------------------------------
-- Run YulPorts Within a Pure Yul Function
------------------------------------------------------------------------------------------------------------------------

withinPureY :: forall f x xs b r ioe m1 m2.
  ( YulO4 x (NP xs) b r
  -- m1, m2
  , P'x ioe r ~ m1
  , YulCat Pure (NP (x:xs)) ~ m2
  -- f, x:xs, b
  , EquivalentNPOfFunction f (x:xs) b
  , ConvertibleNPtoTupleN (NP (MapList m1 (x:xs)))
  , LinearDistributiveNP m1 (x:xs)
  , UncurriableNP f (x:xs) b m2 m2 m2 m2 Many
  ) =>
  NPtoTupleN (NP (MapList m1 (x:xs))) ⊸
  PureY f ->
  P'x ioe r b
withinPureY tplxxs f = encodeP'x cat' sxxs
  where !(x, xs) = splitNonEmptyNP (fromTupleNtoNP tplxxs)
        !(x', u) = mkUnit'l x
        sxxs = linearDistributeNP (x' :* xs) u :: m1 (NP (x:xs))
        cat = uncurryNP @f @(x:xs) @b @m2 @m2 @m2 @m2 f YulId
        cat' = YulUnsafeCoerceEffect cat

-- cond :: P'V va r BOOL ⊸ (Bool ⊸ YulLVM va vb r (P'V vb r a))
-- cond c f = _
--   -- LVM.do
--   -- u <- yembed ()
--   -- match (YulId :: YulCat eff p p)
