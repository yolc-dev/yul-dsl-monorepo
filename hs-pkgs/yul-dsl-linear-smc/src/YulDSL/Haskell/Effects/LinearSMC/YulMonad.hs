{-# LANGUAGE AllowAmbiguousTypes #-}
module YulDSL.Haskell.Effects.LinearSMC.YulMonad
  ( -- * Yul Monad
    YulMonad, runYulMonad
  , ypure, yembed
    -- * Yul Monadic Diagrams
  , YulCat'LVM (MkYulCat'LVM), YulCat'LPM (MkYulCat'LPM)
  , yulmonad'v, yulmonad'p
  , module Control.LinearlyVersionedMonad.Combinators
  , module Control.LinearlyVersionedMonad.LVMVar
  , Control.Functor.Linear.fmap
  --
  , withinPureY
  ) where
import GHC.TypeLits                                  (KnownNat)
-- linear-base
import Control.Functor.Linear qualified
import Prelude.Linear
-- yul-dsl-pure
import YulDSL.Haskell.LibPure
-- linearly-versioned-monad
import Control.LinearlyVersionedMonad                (LVM, runLVM)
import Control.LinearlyVersionedMonad                qualified as LVM
import Control.LinearlyVersionedMonad.Combinators
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
runYulMonad :: forall vd r a ue .
  ( KnownNat vd
  , YulO2 r a
  ) =>
  P'x ue r () ⊸ YulMonad 0 vd r (P'V vd r a) ⊸ P'V vd r a
runYulMonad u m = let ud = MkUnitDumpster (unsafeCoerceYulPort u)
                      !(ctx', a) = runLVM (MkYulMonadCtx ud) m
                      !(MkYulMonadCtx (MkUnitDumpster u')) = ctx'
                  in ignore'l (unsafeCoerceYulPort u') a

-- An alias to 'LVM.pure' to avoid naming conflict with Monad pure function.
ypure :: forall a v r. KnownNat v => P'V v r a ⊸ YulMonad v v r (P'V v r a)
ypure = LVM.pure

-- | Generate a unit monadically.
yembed :: forall a v r. (KnownNat v, YulO2 r a) => a -> YulMonad v v r (P'V v r a)
yembed = embed

--------------------------------------------------------------------------------
-- YulMonad Context
--------------------------------------------------------------------------------

-- A dumpster of units and its utility functions start with "ud_".
newtype UnitDumpster r = MkUnitDumpster (P'V 0 r ())

-- Duplicate a unit.
ud_dupu :: forall eff r. YulO1 r
        => UnitDumpster r ⊸ (UnitDumpster r, P'x eff r ())
ud_dupu (MkUnitDumpster u) = let !(u1, u2) = dup2'l u
                             in (MkUnitDumpster u1, unsafeCoerceYulPort u2)

-- Gulp an input port.
ud_gulp :: forall eff r a. YulO2 r a
        => P'x eff r a ⊸ UnitDumpster r ⊸ UnitDumpster r
ud_gulp x (MkUnitDumpster u) = let u' = ignore'l u (unsafeCoerceYulPort(discard'l x))
                               in MkUnitDumpster u'

-- Context to be with the 'YulMonad'.
newtype YulMonadCtx r = MkYulMonadCtx (UnitDumpster r)

instance YulO2 r a => ContextualConsumable (YulMonadCtx r) (P'x eff r a) where

  contextualConsume (MkYulMonadCtx ud) x = MkYulMonadCtx (ud_gulp x ud)

instance YulO3 r a b => ContextualSeqable (YulMonadCtx r) (P'x eff1 r a) (P'x eff2 r b) where
  contextualSeq (MkYulMonadCtx ud) a b = let ud' = ud_gulp a ud
                                             !(ud'', u') = ud_dupu ud'
                                             b' = ignore'l u' b
                                         in (MkYulMonadCtx ud'', b')

instance YulO2 r a => ContextualDupable (YulMonadCtx r) (P'x eff r a) where
  contextualDup ctx x = (ctx, dup2'l x)

instance YulO2 r a => ContextualEmbeddable (YulMonadCtx r) (P'x eff r) a where
  contextualEmbed (MkYulMonadCtx ud) x'p = let !(ud', u') = ud_dupu ud
                                               x'v = emb'l x'p u'
                                           in (MkYulMonadCtx ud', x'v)

instance YulO2 a r => LinearlyVersionRestrictable (YulMonadCtx r) (P'P r a) where
  type instance LinearlyRestrictedVersion (YulMonadCtx r) (P'P r a) v = P'V v r a
  restrictVersion a = let !(a1, a2) = dup2'l a in LVM.pure (a1, unsafeCoerceYulPort a2)

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
  uncurryNP b (MkYulCat'LVV h) = MkYulCat'LVM \a ->
    eject (h a) LVM.>> b

instance forall x xs b g v1 vn r a.
         ( YulO4 x (NP xs) r a
         , UncurriableNP g xs b (P'V v1 r) (YulMonad v1 vn r) (YulCat'LVV v1 v1 r a) (YulCat'LVM v1 vn r a) One
         ) =>
         UncurriableNP (x -> g) (x:xs) b
         (P'V v1 r) (YulMonad v1 vn r)
         (YulCat'LVV v1 v1 r a) (YulCat'LVM v1 vn r a) One where
  uncurryNP f (MkYulCat'LVV h) = MkYulCat'LVM
    (uncurryNP'lx @g @x @xs @b @(P'V v1 r) @(YulMonad v1 vn r) @(YulCat'LVV v1 v1 r) @(YulCat'LVM v1 vn r)
     f h MkYulCat'LVV (\(MkYulCat'LVM g) -> g))

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
  uncurryNP b (MkYulCat'LPP h) = MkYulCat'LPM \a ->
    eject (unsafeCoerceYulPort (h a & coerceType'l @_ @())) LVM.>> b

instance forall x xs b g v1 vn r a.
         ( EquivalentNPOfFunction g xs (P'V vn r b)
         , YulO5 x (NP xs) b r a
         , UncurriableNP g xs (P'V vn r b) (P'P r) (YulMonad v1 vn r) (YulCat'LPP r a) (YulCat'LPM v1 vn r a) One
         ) =>
         UncurriableNP (x -> g) (x:xs) (P'V vn r b)
         (P'P r) (YulMonad v1 vn r) (YulCat'LPP r a) (YulCat'LPM v1 vn r a) One where
  uncurryNP f (MkYulCat'LPP h) = MkYulCat'LPM
    (uncurryNP'lx @g @x @xs @(P'V vn r b) @(P'P r) @(YulMonad v1 vn r) @(YulCat'LPP r) @(YulCat'LPM v1 vn r)
     f h MkYulCat'LPP (\(MkYulCat'LPM g) -> g))

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
