module YulDSL.Haskell.Data.SHMap
  ( SHMap (SHMap), shmap
  , shmapRef, shmapGet, shmapPut
  ) where
-- base
import GHC.TypeLits                              (type (+))
-- linear-base
import Prelude.Linear                            (String, fromInteger, type (~))
-- yul-dsl
import YulDSL.Core
--
import Control.LinearlyVersionedMonad            qualified as LVM
import Data.Num.Linear.YulDSL                    ()
import YulDSL.Haskell.Effects.LinearSMC.Storage
import YulDSL.Haskell.Effects.LinearSMC.YulMonad
import YulDSL.Haskell.Effects.LinearSMC.YulPort
import YulDSL.Haskell.YulUtils.LinearSMC


-- | A Storage Hash-Map (SHMap) with a U256 root-key.
newtype SHMap a b = SHMap U256

-- | Create a storage hash-map with a root-key represented by a string.
shmap :: forall s a b. s ~ (a -> b) => String -> SHMap a b
shmap key = SHMap (fromInteger (bytesnToInteger (stringKeccak256 key)))

-- | Get a storage reference from the storage hash-map.
shmapRef :: forall a b ie r v.
  YulO3 r a b =>
  SHMap a b ->
  P'x ie r a ⊸
  YulMonad v v r (P'x ie r (REF b))
shmapRef (SHMap key) a = LVM.do
  key' <- embed key
  LVM.pure (extendType'l (yulKeccak256'l (merge'l (key', a))))

-- | Get a value from the storage hash-map.
shmapGet :: forall a b ie r v.
  ( YulO3 r a b
  , SReferenceable ie v r (REF b) b
  ) =>
  SHMap a b ->
  P'x ie r a ⊸
  YulMonad v v r (P'V v r b)
shmapGet m a = shmapRef m a LVM.>>= sget

-- | Get a value from the storage hash-map.
shmapPut :: forall a b ie r v.
  ( YulO3 r a b
  , SReferenceable ie v r (REF b) b
  ) =>
  SHMap a b ->
  P'x ie r a ⊸
  P'V v r b ⊸
  YulMonad v (v + 1) r (P'V (v + 1) r ())
shmapPut m a b = shmapRef m a LVM.>>= \s -> sput s b
