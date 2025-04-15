{-# LANGUAGE AllowAmbiguousTypes #-}
module YulDSL.Haskell.Effects.LinearSMC.YulMonad
  ( -- * Yul Monad
    YulMonad, runYulMonad
  , ypure, yembed
  , withYulVarRegistry, yMkUvVar, yMkVrVar, yvread
    -- * Yul Monadic Diagrams
  , YulCat'LVM (MkYulCat'LVM), YulCat'LPM (MkYulCat'LPM)
  , yulmonad'v, yulmonad'p
  , module Control.LinearlyVersionedMonad.Combinators
  , module Control.LinearlyVersionedMonad.LVMVar
  , Control.Functor.Linear.fmap
  --
  , withinPureY
  ) where
-- base
import GHC.TypeLits                                  (KnownNat)
-- linear-base
import Control.Functor.Linear qualified
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

--------------------------------------------------------------------------------
-- YulMonad: A Linearly Versioned Monad for YulDSL
--------------------------------------------------------------------------------

-- | YulMonad is a linear versioned monad with 'YulMonadCtx' as its context data.
type YulMonad va vb r = LVM (YulMonadCtx r) va vb

-- | Run a YulMonad with an initial unit port and returns a versioned result.
runYulMonad :: forall b vd r ie.
  ( KnownNat vd
  , YulO2 r b
  ) =>
  P'x ie r () ⊸ YulMonad 0 vd r (P'V vd r b) ⊸ P'V vd r b
runYulMonad u m = let ctx = mkYulMonadCtx u
                      !(ctx', b) = runLVM ctx mWrapper
                  in rmYulMonadCtx ctx' b
  where mWrapper = LVM.do
          initRgstr
          b <- m
          consumeRgstr
          LVM.pure b
        initRgstr :: YulMonad 0 0 r ()
        initRgstr = MkLVM \(MkYulMonadCtx ud mbRgstr) ->
          let rgstr = case mbRgstr of
                Nothing -> initLVMVarRegistry
                err     -> lseq (error "initRgstr: registry should be empty" :: ()) (UnsafeLinear.coerce err)
          in (Dict, MkYulMonadCtx ud (Just rgstr), ())
        consumeRgstr :: YulMonad vd vd r ()
        consumeRgstr = withYulVarRegistry \rgstr -> LVM.do
          consumeLVMVarRegistry rgstr
          LVM.pure (Nothing, ())

-- An alias to 'LVM.pure' to avoid naming conflict with Monad pure function.
ypure :: forall a v r. KnownNat v => P'V v r a ⊸ YulMonad v v r (P'V v r a)
ypure = LVM.pure

-- | Generate a unit monadically.
yembed :: forall a v r. (KnownNat v, YulO2 r a) => a -> YulMonad v v r (P'V v r a)
yembed = embed

--------------------------------------------------------------------------------
-- YulMonad Context
--------------------------------------------------------------------------------

type YulVarRegistry r = LVMVarRegistry (YulMonadCtx r)

-- Context to be with the 'YulMonad'.
data YulMonadCtx r where
  MkYulMonadCtx :: YulPortUniter r ⊸ Maybe (YulVarRegistry r) ⊸ YulMonadCtx r

mkYulMonadCtx ::  P'x ie r () ⊸ YulMonadCtx r
mkYulMonadCtx u = MkYulMonadCtx (MkYulPortUniter (unsafeCoerceYulPort u)) Nothing

rmYulMonadCtx :: YulO2 b r => YulMonadCtx r ⊸ P'x oe r b ⊸ P'x oe r b
rmYulMonadCtx (MkYulMonadCtx (MkYulPortUniter u) mbRgstr) =
  case mbRgstr of
    Nothing -> ()
    err     -> lseq (error "rmYulMonadCtx: registry not consumed" :: ()) (UnsafeLinear.coerce err)
  `lseq` ignore'l (unsafeCoerceYulPort u)

instance YulO2 r a => ContextualConsumable (YulMonadCtx r) (P'x eff r a) where

  contextualConsume (MkYulMonadCtx ud rgstr) x = MkYulMonadCtx (yulPortUniterGulp ud x) rgstr

instance YulO3 r a b => ContextualSeqable (YulMonadCtx r) (P'x eff1 r a) (P'x eff2 r b) where
  contextualSeq (MkYulMonadCtx ud mbRgstr) a b =
    let ud' = yulPortUniterGulp ud a
        !(ud'', u') = yulPortUniterMkUnit ud'
        b' = ignore'l u' b
    in (MkYulMonadCtx ud'' mbRgstr, b')

instance YulO2 r a => ContextualDupable (YulMonadCtx r) (P'x eff r a) where
  contextualDup ctx x = (ctx, dup2'l x)

instance YulO2 r a => ContextualEmbeddable (YulMonadCtx r) (P'x eff r) a where
  contextualEmbed (MkYulMonadCtx ud mbRgstr) x'p =
    let !(ud', u') = yulPortUniterMkUnit ud
        x'v = emb'l x'p u'
    in (MkYulMonadCtx ud' mbRgstr, x'v)

instance (KnownNat v, YulO2 a r) => LinearlyVersionRestrictable v (YulMonadCtx r) (P'P r a) where
  type instance LinearlyRestrictedVersion (YulMonadCtx r) (P'P r a) v = P'V v r a
  restrictVersion a = LVM.pure (unsafeCoerceYulPort a)

instance (KnownNat v, YulO2 a r) => LinearlyVersionRestrictable v (YulMonadCtx r) (P'V v r a) where
  type instance LinearlyRestrictedVersion (YulMonadCtx r) (P'V v r a) v = P'V v r a
  restrictVersion = LVM.pure

--------------------------------------------------------------------------------
-- LVMVar API
--------------------------------------------------------------------------------

withYulVarRegistry :: forall r v b.
  KnownNat v =>
  (YulVarRegistry r ⊸ YulMonad v v r (Maybe (YulVarRegistry r), b)) ⊸
  YulMonad v v r b
withYulVarRegistry f = MkLVM \(MkYulMonadCtx ud mbRgstr) ->
  let ctx' = MkYulMonadCtx ud Nothing
      !(dict, ctx'', (mbRgstr', b)) = case mbRgstr of
        Just rgstr -> unLVM (f rgstr) ctx'
        Nothing    -> lseq (error "withYulVarRegistry: registry should exist" :: ()) (UnsafeLinear.coerce (f, ctx'))
      ud' = case ctx'' of
        (MkYulMonadCtx ud'' Nothing) -> ud''
        err                          -> lseq (error "withYulVarRegistry: nonsense" :: ()) (UnsafeLinear.coerce err)
  in (dict, MkYulMonadCtx ud' mbRgstr', b)

type YulUvVar r a = Ur (UvLVMVarRef (YulMonadCtx r) (P'P r a))

type YulVrVar v r a = Ur (VrLVMVarRef (YulMonadCtx r) v (P'V v r a))

yMkUvVar :: forall a r v. (KnownNat v, YulO2 a r) => P'P r a ⊸ YulMonad v v r (YulUvVar r a)
yMkUvVar x = withYulVarRegistry \rgstr ->
  let !(var, rgstr') = registerUvLVMVar x rgstr
  in LVM.pure (Just rgstr', var)

yMkVrVar :: forall a r v. (KnownNat v, YulO2 a r) => P'V v r a ⊸ YulMonad v v r (YulVrVar v r a)
yMkVrVar x = withYulVarRegistry \rgstr ->
  let !(var, rgstr') = registerVrLVMVar x rgstr
  in LVM.pure (Just rgstr', var)

-- yread :: forall ref v r a.
--   LVMVarReferenciable v ref (YulMonadCtx r) (P'V v r a) =>
--   ref ->
--   YulMonad v v r (P'V v r a)
-- yread ref = withYulVarRegistry \rgstr -> LVM.do
--   (x, rgstr') <- readLVMVarRef ref rgstr
--   LVM.pure (Just rgstr', x)
--   in LVM.pure (Just rgstr', var)

yvread :: forall a ref v r ie oe.
  ( LVMVarReferenciable v ref (YulMonadCtx r) (P'x ie r a)
  , LinearlyRestrictedVersion (YulMonadCtx r) (P'x ie r a) v ~ P'x oe r a
  )=>
  ref ->
  YulMonad v v r (P'x oe r a)
yvread ref = withYulVarRegistry \rgstr -> LVM.do
  (x, rgstr') <- vreadLVMVarRef ref rgstr
  LVM.pure (Just rgstr', x)

------------------------------------------------------------------------------------------------------------------------
-- yulmonad'v
------------------------------------------------------------------------------------------------------------------------

-- | Monadic yul port diagrams for versioned input and yul monad output.
newtype YulCat'LVM v1 vn r a b = MkYulCat'LVM (P'V v1 r a ⊸ YulMonad v1 vn r b)

instance forall b v1 vn r a.
         ( KnownNat v1, KnownNat vn
         , YulO2 a r
         , EquivalentNPOfFunction b '[] b
         , LiftFunction b (P'V v1 r) (YulMonad v1 vn r) One ~ YulMonad v1 vn r b
         , LiftFunction b (YulCat'LVV v1 v1 r a) (YulCat'LVM v1 vn r a) One ~ YulCat'LVM v1 vn r a b
         ) =>
         UncurriableNP b '[] b
         (P'V v1 r) (YulMonad v1 vn r)
         (YulCat'LVV v1 v1 r a) (YulCat'LVM v1 vn r a) One where
  uncurryNP b (MkYulCat'LVV h) = MkYulCat'LVM \a -> eject (h a) LVM.>> b

instance forall x xs b g v1 vn r a.
         ( YulO4 x (NP xs) r a
         , UncurriableNP g xs b (P'V v1 r) (YulMonad v1 vn r) (YulCat'LVV v1 v1 r a) (YulCat'LVM v1 vn r a) One
         ) =>
         UncurriableNP (x -> g) (x:xs) b
         (P'V v1 r) (YulMonad v1 vn r)
         (YulCat'LVV v1 v1 r a) (YulCat'LVM v1 vn r a) One where
  uncurryNP f (MkYulCat'LVV h) = MkYulCat'LVM (uncurryNP'lx f h MkYulCat'LVV (\(MkYulCat'LVM g) -> g))

instance forall b v1 vn r a.
         ( YulO2 r a
         , EquivalentNPOfFunction b '[] b
         , LiftFunction (CurryNP (NP '[]) b) (P'V v1 r) (YulMonad v1 vn r) One ~ YulMonad v1 vn r b
         , LiftFunction (CurryNP (NP '[]) b) (YulCat'LVV v1 v1 r a) (YulMonad v1 vn r) One ~ YulMonad v1 vn r b
         ) =>
         CurriableNP b '[] b
         (P'V v1 r) (YulMonad v1 vn r) (YulCat'LVV v1 v1 r a) One where
  curryNP fNP = fNP (MkYulCat'LVV (\a -> coerceType'l (discard'l a)))

instance forall g x xs b r a v1 vn.
         ( YulO4 x (NP xs) r a
         , CurriableNP g xs b (P'V v1 r) (YulMonad v1 vn r) (YulCat'LVV v1 v1 r a) One
         ) =>
         CurriableNP (x -> g) (x:xs) b
         (P'V v1 r) (YulMonad v1 vn r) (YulCat'LVV v1 v1 r a) One where
  curryNP fNP x = curryNP @g @xs @b @(P'V v1 r) @(YulMonad v1 vn r) @(YulCat'LVV v1 v1 r a) @One
                    (\(MkYulCat'LVV fxs) -> fNP (MkYulCat'LVV (\a -> (consNP x (fxs a)))))

yulmonad'v :: forall xs b r vd m1 m1b m2 m2b f' b'.
  ( KnownNat vd
  , YulO3 (NP xs) b r
  -- m1, m1b, m2, m2b
  , P'V         0 r ~ m1
  , YulMonad 0 vd r ~ m1b
  , YulCat'LVV 0  0 r (NP xs) ~ m2
  , YulCat'LVM 0 vd r (NP xs) ~ m2b
  -- b'
  , P'V vd r b ~ b'
  -- f'
  , UncurriableNP f' xs b' m1 m1b m2 m2b One
  ) =>
  LiftFunction f' m1 m1b One ->  -- ^ LiftFunction               f1  m1 m1b One
  (P'V 0 r (NP xs) ⊸ P'V vd r b) -- ^ LiftFunction (NP (():xs) -> b) m1 m1b One
yulmonad'v f =
  let !(MkYulCat'LVM f') = uncurryNP @f' @xs @b' @m1 @m1b @m2 @m2b @One f (MkYulCat'LVV id)
  in \xs -> mkUnit'l xs & \(xs', u) -> runYulMonad u (f' xs')

------------------------------------------------------------------------------------------------------------------------
-- yulmonad'p
------------------------------------------------------------------------------------------------------------------------

-- | Monadic yul port diagrams for pure input and yul monad output.
newtype YulCat'LPM v1 vn r a b = MkYulCat'LPM (P'P r a ⊸ YulMonad v1 vn r b)

instance forall b v1 vn r a.
         ( KnownNat v1, KnownNat vn
         , YulO3 b r a
         , LiftFunction b (P'P r) (P'V vn r) One ~ P'V vn r b
         ) =>
         UncurriableNP (P'V vn r b) '[] (P'V vn r b)
         (P'P r) (YulMonad v1 vn r)
         (YulCat'LPP r a) (YulCat'LPM v1 vn r a) One where
  uncurryNP b (MkYulCat'LPP h) = MkYulCat'LPM \a -> eject (unsafeCoerceYulPort (h a & coerceType'l @_ @())) LVM.>> b

instance forall x xs b g v1 vn r a.
         ( EquivalentNPOfFunction g xs (P'V vn r b)
         , YulO5 x (NP xs) b r a
         , UncurriableNP g xs (P'V vn r b) (P'P r) (YulMonad v1 vn r) (YulCat'LPP r a) (YulCat'LPM v1 vn r a) One
         ) =>
         UncurriableNP (x -> g) (x:xs) (P'V vn r b)
         (P'P r) (YulMonad v1 vn r) (YulCat'LPP r a) (YulCat'LPM v1 vn r a) One where
  uncurryNP f (MkYulCat'LPP h) = MkYulCat'LPM (uncurryNP'lx f h MkYulCat'LPP (\(MkYulCat'LPM g) -> g))

yulmonad'p :: forall xs b r vd m1 m1b m2 m2b f' b'.
  ( KnownNat vd
  , YulO3 (NP xs) b r
  -- m1, m1b, m2, m2b
  , P'P           r ~ m1
  , YulMonad 0 vd r ~ m1b
  , YulCat'LPP      r (NP xs) ~ m2
  , YulCat'LPM 0 vd r (NP xs) ~ m2b
  -- b'
  , P'V vd r b ~ b'
  -- f'
  , UncurriableNP f' xs b' m1 m1b m2 m2b One
  ) =>
  LiftFunction f' m1 m1b One -> -- ^ LiftFunction               f1  m1 m1b One
  (P'P r (NP xs) ⊸ P'V vd r b)  -- ^ LiftFunction (NP (():xs) -> b) m1 m1b One
yulmonad'p f =
  let !(MkYulCat'LPM f') = uncurryNP @f' @xs @b' @m1 @m1b @m2 @m2b @One f (MkYulCat'LPP id)
  in \xs -> mkUnit'l xs & \(xs', u) -> runYulMonad u (f' xs')

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

-- cond :: P'V va r BOOL ⊸ (Bool ⊸ YulMonad va vb r (P'V vb r a))
-- cond c f = _
--   -- LVM.do
--   -- u <- yembed ()
--   -- match (YulId :: YulCat eff p p)
