module Counter where
import Control.LinearlyVersionedMonad            qualified as LVM
import Prelude.Linear                            (fromString)
import YulDSL.Core
    ( ADDR
    , REF
    , U256
    , YulCat (YulSGet)
    , YulO1
    , mkYulObject
    , staticFn
    , yulNoop
    )
import YulDSL.Haskell.Effects.LinearSMC.LinearFn (StaticFn)
import YulDSL.Haskell.Effects.LinearSMC.Storage  (SReferenceable)
import YulDSL.Haskell.Effects.LinearSMC.YulMonad (YulMonad, yulmonad'p)
import YulDSL.Haskell.Effects.LinearSMC.YulPort
    ( P'P
    , P'V
    , PortEffect (PurePort, VersionedPort)
    , Versionable'L
    , encodeP'x
    , reduceType'l
    , ver'l
    )
import YulDSL.Haskell.LibLinearSMC               (embed, extendType'l, keccak256'l, lfn', merge'l)


-- base
import GHC.TypeLits                              (KnownNat)
-- linear-base
import Prelude.Linear                            (fromInteger)


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

sget' :: ( KnownNat v
         , YulO1 r
         , Versionable'L (VersionedPort v) v
         ) => P'P r (REF U256) ⊸ P'V v r U256
sget' s = encodeP'x YulSGet (reduceType'l (ver'l s))


lvmMap1 :: forall ctx v b r. (YulO1 b, KnownNat v) =>
  ((P'P r U256) ⊸ (P'P r (REF b))) %1 -> LVM.LVM ctx v v (P'P r U256) ⊸ LVM.LVM ctx v v (P'P r (REF b))
lvmMap1 f ma = LVM.MkLVM \ctx -> let !(aleb, ctx', a) = LVM.unLVM ma ctx
                                 in  (aleb, ctx', f a)

-- | Get a storage reference from the storage hash-map.
shmapRef :: forall r b v.
  ( KnownNat v
  , YulO1 b
  , YulO1 r
  -- , YulO1 (REF b)
  ) =>
  SHMap b ->
  P'P r ADDR ⊸
  YulMonad v v r (P'P r (REF b))
shmapRef _ a =
  lvmMap1
  (\key' -> extendType'l (keccak256'l (merge'l (key', a))))
  (embed (fromInteger 10))



lvmMap2 :: forall ctx v a b r. (YulO1 a, YulO1 b, KnownNat v) =>
  ((P'P r a) ⊸ (P'V v r b)) %1 -> LVM.LVM ctx v v (P'P r a) ⊸ LVM.LVM ctx v v (P'V v r b)
lvmMap2 f ma = LVM.MkLVM \ctx -> let !(aleb, ctx', a) = LVM.unLVM ma ctx
                                 in  (aleb, ctx', f a)

-- | Get a value from the storage hash-map.
shmapGet :: forall r v.
  ( YulO1 r
  , SReferenceable PurePort v r (REF U256) U256
  ) =>
  P'P r ADDR ⊸
  YulMonad v v r (P'V v r U256)
shmapGet a = lvmMap2 sget' (shmapRef (SHMap :: SHMap U256) a)

getCounter :: StaticFn (ADDR -> U256)
getCounter = lfn' "test" (yulmonad'p shmapGet)


object = mkYulObject "Counter" yulNoop
  [ staticFn "getCounter" getCounter
  ]
