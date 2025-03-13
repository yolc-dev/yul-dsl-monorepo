{-# LANGUAGE AllowAmbiguousTypes #-}
module YulDSL.Haskell.Effects.LinearSMC.YulMonad
  ( -- * Yul Monad
    YulMonad, runYulMonad
  , ypure, yembed
    -- * Yul Monadic Diagrams
  , YulCat'LVM (MkYulCat'LVM), YulCat'LPM (MkYulCat'LPM)
  , yulmonad'v, yulmonad'p
  , module Control.LinearlyVersionedMonad.Combinators
  , Control.Functor.Linear.fmap
  ) where
-- linear-base
import Control.Functor.Linear qualified
import Prelude.Linear
-- yul-dsl
import YulDSL.Core
-- yul-dsl-pure
import YulDSL.Haskell.Effects.Pure
-- linearly-versioned-monad
import Control.LinearlyVersionedMonad                (LVM, runLVM)
import Control.LinearlyVersionedMonad                qualified as LVM
import Control.LinearlyVersionedMonad.Combinators
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
runYulMonad :: forall vd r a ue . YulO2 r a
            => P'x ue r () ⊸ YulMonad 0 vd r (P'V vd r a) ⊸ P'V vd r a
runYulMonad u m = let ud = MkUnitDumpster (unsafeCoerceYulPort u)
                      !(ctx', a) = runLVM (MkYulMonadCtx ud) m
                      !(MkYulMonadCtx (MkUnitDumpster u')) = ctx'
                  in ignore'l (unsafeCoerceYulPort u') a

-- An alias to 'LVM.pure' to avoid naming conflict with Monad pure function.
ypure :: forall a v r. P'V v r a ⊸ YulMonad v v r (P'V v r a)
ypure = LVM.pure

-- | Generate a unit monadically.
yembed :: YulO2 r a => a ⊸ YulMonad v v r (P'V v r a)
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

------------------------------------------------------------------------------------------------------------------------
-- yulmonad'v
------------------------------------------------------------------------------------------------------------------------

-- | Monadic yul port diagrams for versioned input and yul monad output.
newtype YulCat'LVM v1 vn r a b = MkYulCat'LVM (P'V v1 r a ⊸ YulMonad v1 vn r b)

instance forall x v1 vn r a.
         ( YulO3 x r a
         , LiftFunction x (P'V v1 r) (P'V vn r) One ~ P'V vn r x
         ) => UncurryingNP (P'V vn r x) '[] (P'V vn r x)
         (P'V v1 r) (YulMonad v1 vn r)
         (YulCat'LVV v1 v1 r a) (YulCat'LVM v1 vn r a) One where
  uncurryingNP x (MkYulCat'LVV h) = MkYulCat'LVM
    \a -> tossToUnit (h a) LVM.>> x

instance forall x xs b g v1 vn r a.
         ( YulO5 x (NP xs) b r a
         , UncurryingNP g xs (P'V vn r b) (P'V v1 r) (YulMonad v1 vn r) (YulCat'LVV v1 v1 r a) (YulCat'LVM v1 vn r a) One
         ) => UncurryingNP (x -> g) (x:xs) (P'V vn r b)
         (P'V v1 r) (YulMonad v1 vn r)
         (YulCat'LVV v1 v1 r a) (YulCat'LVM v1 vn r a) One where
  uncurryingNP f (MkYulCat'LVV h) = MkYulCat'LVM
    \xxs ->
      dup2'l xxs
    & \(xxs1, xxs2) -> split'l (coerceType'l @(NP (x:xs)) @(x, NP xs) (h xxs1))
    & \(x, xs) -> let !(MkYulCat'LVM g) =
                        (uncurryingNP
                          @g @xs @(P'V vn r b)
                          @(P'V v1 r) @(YulMonad v1 vn r) @(YulCat'LVV v1 v1 r a) @(YulCat'LVM v1 vn r a) @One
                          (f x)
                          (MkYulCat'LVV (\a -> ignore'l (discard'l a) xs))
                        )
                  in g xxs2

instance forall x v1 vn r a.
         ( YulO3 x r a
         , LiftFunction (CurryNP (NP '[]) x) (P'V v1 r) (YulMonad v1 vn r) One ~ YulMonad v1 vn r x
         ) => CurryingNP '[] (P'V vn r x) (P'V v1 r) (YulMonad v1 vn r) (YulCat'LVV v1 v1 r a) One where
  curryingNP cb = cb (MkYulCat'LVV (\a -> coerceType'l (discard'l a)))

instance forall x xs b r a v1 vn.
         ( YulO5 x (NP xs) b r a
         , CurryingNP xs (P'V vn r b) (P'V v1 r) (YulMonad v1 vn r) (YulCat'LVV v1 v1 r a) One
         ) => CurryingNP (x:xs) (P'V vn r b) (P'V v1 r) (YulMonad v1 vn r) (YulCat'LVV v1 v1 r a) One where
  curryingNP cb x = curryingNP @xs @(P'V vn r b) @(P'V v1 r) @(YulMonad v1 vn r) @(YulCat'LVV v1 v1 r a) @One
                    (\(MkYulCat'LVV fxs) -> cb (MkYulCat'LVV (\a -> (cons'l x (fxs a)))))

yulmonad'v :: forall f xs b r vd m1 m1b m2 m2b f' b'.
  ( YulO3 (NP xs) b r
  -- constraint f, using b xs
  , EquivalentNPOfFunction f xs b
  -- constraint m1, m1b, m2, m2b, using xs
  , P'V         0 r ~ m1
  , YulMonad 0 vd r ~ m1b
  , YulCat'LVV 0  0 r (NP xs) ~ m2
  , YulCat'LVM 0 vd r (NP xs) ~ m2b
  -- constraint b'
  , P'V vd r b ~ b'
  , LiftFunction b' m2 m2b One ~ m2b b'
  -- constraint f'
  , EquivalentNPOfFunction f' xs b'
  , UncurryingNP f' xs b' m1 m1b m2 m2b One
  )
  => LiftFunction f' m1 m1b One     -- ^ LiftFunction               f1  m1 m1b One
  -> (P'V 0 r (NP xs) ⊸ P'V vd r b) -- ^ LiftFunction (NP (():xs) -> b) m1 m1b One
yulmonad'v f =
  let !(MkYulCat'LVM f') = uncurryingNP @f' @xs @b' @m1 @m1b @m2 @m2b @One f (MkYulCat'LVV id)
  in \xs -> mkUnit'l xs & \(xs', u) -> runYulMonad u (f' xs')

------------------------------------------------------------------------------------------------------------------------
-- yulmonad'p
------------------------------------------------------------------------------------------------------------------------

-- | Monadic yul port diagrams for pure input and yul monad output.
newtype YulCat'LPM v1 vn r a b = MkYulCat'LPM (P'P r a ⊸ YulMonad v1 vn r b)

instance forall x v1 vn r a.
         ( YulO3 x r a
         , LiftFunction x (P'P r) (P'V vn r) One ~ P'V vn r x
         ) => UncurryingNP (P'V vn r x) '[] (P'V vn r x)
         (P'P r) (YulMonad v1 vn r)
         (YulCat'LPP r a) (YulCat'LPM v1 vn r a) One where
  uncurryingNP x (MkYulCat'LPP h) = MkYulCat'LPM
    \a -> tossToUnit (unsafeCoerceYulPort (h a & coerceType'l @_ @())) LVM.>> x

instance forall x xs b g v1 vn r a.
         ( YulO5 x (NP xs) b r a
         , UncurryingNP g xs (P'V vn r b) (P'P r) (YulMonad v1 vn r) (YulCat'LPP r a) (YulCat'LPM v1 vn r a) One
         ) => UncurryingNP (x -> g) (x:xs) (P'V vn r b)
         (P'P r) (YulMonad v1 vn r)
         (YulCat'LPP r a) (YulCat'LPM v1 vn r a) One where
  uncurryingNP f (MkYulCat'LPP h) = MkYulCat'LPM
    \xxs ->
      dup2'l xxs
    & \(xxs1, xxs2) -> split'l (coerceType'l @(NP (x:xs)) @(x, NP xs) (h xxs1))
    & \(x, xs) -> let !(MkYulCat'LPM g) =
                        (uncurryingNP
                          @g @xs @(P'V vn r b)
                          @(P'P r) @(YulMonad v1 vn r) @(YulCat'LPP r a) @(YulCat'LPM v1 vn r a) @One
                          (f x)
                          (MkYulCat'LPP (\a -> ignore'l (discard'l a) xs))
                        )
                  in g xxs2

yulmonad'p :: forall f xs b r vd m1 m1b m2 m2b f' b'.
  ( YulO3 (NP xs) b r
  -- constraint f, using b xs
  , EquivalentNPOfFunction f xs b
  -- constraint m1, m1b, m2, m2b, using xs
  , P'P           r ~ m1
  , YulMonad 0 vd r ~ m1b
  , YulCat'LPP      r (NP xs) ~ m2
  , YulCat'LPM 0 vd r (NP xs) ~ m2b
  -- constraint b'
  , P'V vd r b ~ b'
  , LiftFunction b' m2 m2b One ~ m2b b'
  --
  , EquivalentNPOfFunction f' xs b'
  , UncurryingNP f' xs b' m1 m1b m2 m2b One
  )
  => LiftFunction f' m1 m1b One   -- ^ LiftFunction               f1  m1 m1b One
  -> (P'P r (NP xs) ⊸ P'V vd r b) -- ^ LiftFunction (NP (():xs) -> b) m1 m1b One
yulmonad'p f =
  let !(MkYulCat'LPM f') = uncurryingNP @f' @xs @b' @m1 @m1b @m2 @m2b @One f (MkYulCat'LPP id)
  in \xs -> mkUnit'l xs & \(xs', u) -> runYulMonad u (f' xs')

------------------------------------------------------------------------------------------------------------------------
-- Run YulPorts Within a Pure Yul Function
------------------------------------------------------------------------------------------------------------------------

withinPureY :: forall f xs b xsTupleN r ioe.
  ( EquivalentNPOfFunction f xs b
  , NPtoTupleN (NP (MapList (P'x ioe r) xs)) ~ xsTupleN
  , ConvertibleTupleNtoNP xsTupleN
  , YulO3 (NP xs) b r
  ) =>
  xsTupleN ->
  PureY f ->
  P'x ioe r b
withinPureY = undefined
