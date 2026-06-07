module Counter where
import Control.LinearlyVersionedMonad            qualified as LVM
import Prelude.Linear                            (fromString)
import YulDSL.Core                               (ADDR, REF, U256, YulO1, mkYulObject, staticFn, yulNoop)
import YulDSL.Haskell.Effects.LinearSMC.LinearFn (StaticFn)
import YulDSL.Haskell.Effects.LinearSMC.YulMonad (YulMonad, yulmonad'p)
import YulDSL.Haskell.Effects.LinearSMC.YulPort  (P'P, P'V, ver'l)
import YulDSL.Haskell.LibLinearSMC               (extendType'l, keccak256'l, lfn')


-- base
import GHC.TypeLits                              (KnownNat)


-- constraints
import Data.Constraint                           hiding ((\\))
-- linear-base
import Prelude.Linear                            (flip)
import Unsafe.Linear                             qualified as UnsafeLinear


-- Linear version of (\\) for internal use.
(\\) :: HasDict c e => (c => r) ⊸ e ⊸ r
(\\) = flip (UnsafeLinear.toLinear2 (withDict))
infixl 1 \\



-- | A Storage Hash-Map (SHMap) with a U256 root-key.
data SHMap b = SHMap

-- | Get a storage reference from the storage hash-map.
getCounterRef' :: forall b r v.
  ( KnownNat v
  , YulO1 b
  , YulO1 r
  -- , YulO1 (REF b)
  ) =>
  P'P r ADDR ⊸
  YulMonad v v r (P'V v r (REF b))
getCounterRef' a = LVM.pure (extendType'l (keccak256'l (ver'l a)))

getCounterRef :: StaticFn (ADDR -> REF U256)
getCounterRef = lfn' "getRef" (yulmonad'p getCounterRef')

object = mkYulObject "Counter" yulNoop
  [ staticFn "getCounterRef" getCounterRef
  ]
