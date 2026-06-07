{-# LANGUAGE AllowAmbiguousTypes #-}
module YulDSL.Haskell.Effects.LinearSMC.YulMonad
  ( -- * Yul Monad
    YulMonad
    -- * Yul Monadic Diagrams
  , yulmonad'p
  --
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

------------------------------------------------------------------------------------------------------------------------

-- | Monadic yul port diagrams for pure input and yul monad output.
newtype YulCat'LPM v1 vn r a b = MkYulCat'LPM (P'P r a ⊸ YulMonad v1 vn r b)



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
