module YulDSL.Haskell.Data.SHMap
  ( SHMap, shmap
  , shmapGet
  ) where
-- linear-base
import Control.Category.Linear
import Prelude.Linear                            (String, fromInteger, type (~))
-- yul-dsl
import YulDSL.Core
--
import Control.LinearlyVersionedMonad            qualified as LVM
import Data.Num.Linear.YulDSL                    ()
import YulDSL.Haskell.Effects.LinearSMC.YulMonad
import YulDSL.Haskell.Effects.LinearSMC.YulPort

newtype SHMap a b = SHMap U256

shmap :: forall s a b. s ~ (a -> b) => String -> SHMap a b
shmap key = SHMap (fromInteger (bytesnToInteger (stringKeccak256 key)))

shmapGet :: forall a b ie r v. YulO3 r a b
  => SHMap a b
  -> P'x ie r a
  ⊸ YulMonad v v r (P'x ie r (REF b))
shmapGet (SHMap key) a = LVM.do
  key' <- embed key
  with a (\a' -> ypure (extendType'l (yulKeccak256'l (merge (key', a')))))
