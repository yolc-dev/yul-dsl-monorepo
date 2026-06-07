module Counter where
import Prelude.YulDSL (extendType'l, bytesnToInteger, stringKeccak256
                      , embed, merge'l, sget, keccak256'l
                      , mkYulObject, sput, yulmonad'p, lfn
                      , ($), staticFn, yulNoop, ADDR, U256
                      , StaticFn, fromString, P'V, P'x, YulMonad, YulO1, REF, SReferenceable)

-- base
import GHC.TypeLits                   (KnownNat)
-- linear-base
import Prelude.Linear                 (String, fromInteger)
-- yul-dsl
--
import Control.LinearlyVersionedMonad qualified as LVM
--import YulDSL.Haskell.LibLinearSMC



-- | A Storage Hash-Map (SHMap) with a U256 root-key.
newtype SHMap a b = SHMap U256

-- | Create a storage hash-map with a root-key represented by a string.
shmap :: forall s a b. s ~ (a -> b) => String -> SHMap a b
shmap key = SHMap (fromInteger (bytesnToInteger (stringKeccak256 key)))

-- | Get a storage reference from the storage hash-map.
shmapRef :: forall a b ie r v.
  ( KnownNat v
  , YulO1 r
  , YulO1 a
  , YulO1 b
  ) =>
  SHMap a b ->
  P'x ie r a ⊸
  YulMonad v v r (P'x ie r (REF b))
shmapRef (SHMap key) a = LVM.do
  key' <- embed key
  LVM.pure (extendType'l (keccak256'l (merge'l (key', a))))

-- | Get a value from the storage hash-map.
shmapGet :: forall a b ie r v.
  ( YulO1 r
  , YulO1 a
  , YulO1 b
  , SReferenceable ie v r (REF b) b
  ) =>
  SHMap a b ->
  P'x ie r a ⊸
  YulMonad v v r (P'V v r b)
shmapGet m a = shmapRef m a LVM.>>= sget


object = mkYulObject "Counter" yulNoop
  [ staticFn "getCounter" getCounter
  ]

-- | Storage map of user counters
counterMap :: SHMap ADDR U256
counterMap = shmap "Yolc.Demo.Counter.Storage.Counter.PerUser"

getCounter :: StaticFn (ADDR -> U256)
getCounter = $lfn $ yulmonad'p
  \acc -> counterMap `shmapGet` acc
