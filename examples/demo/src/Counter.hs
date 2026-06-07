module Counter where
import Control.LinearlyVersionedMonad qualified as LVM
import Prelude.YulDSL

object = mkYulObject "Counter" yulNoop
  [ -- staticFn "getGlobalCounter" getGlobalCounter
  -- omniFn   "incGlobalCounter" incGlobalCounter
    staticFn "getCounter" getCounter
  -- , omniFn   "incCounter" incCounter
  ]

-- | Storage map of user counters
counterMap :: SHMap ADDR U256
counterMap = shmap "Yolc.Demo.Counter.Storage.Counter.PerUser"

getCounter :: StaticFn (ADDR -> U256)
getCounter = $lfn $ yulmonad'p
  \acc -> counterMap `shmapGet` acc
