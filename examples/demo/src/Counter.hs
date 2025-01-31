module Counter where
import Control.LinearlyVersionedMonad qualified as LVM
import Prelude.YulDSL

object = mkYulObject "Counter" emptyCtor
  [ staticFn "getCounter" getCounter
  , omniFn   "incCounter" incCounter
  -- , staticFn "GetCounter" getCounter'
  -- , omniFn   "GetCounter" incCounter'
  ]

counter :: PureFn (() -> REF U256)
counter = $fn $
  \_ -> YulEmb (keyRef "Yolc.Demo.Counter.Storage.Counter.Global")

getCounter :: StaticFn (() -> U256)
getCounter = $lfn $ yulmonad'p
  \u -> sget (callFn'l counter u)

incCounter :: OmniFn (U256 -> ())
incCounter = $lfn $ yulmonad'p
  \inc_p -> LVM.do
  u <- yembed ()
  (counterRef, currentValue) <- pass (callFn'l counter u) sget
  sput counterRef (currentValue + ver'l inc_p)

-- -- | Storage map of conters
-- counterMap :: SHMap ADDR U256
-- counterMap = shmap "Yolc.Demo.Counter.Storage.Counter.PerUser"

-- getCounter' :: StaticFn (ADDR -> U256)
-- getCounter' = $lfn $ yulmonad'p
--   \acc -> counterMap `shmapGet` acc

-- incCounter' :: OmniFn (U256 -> ())
-- incCounter' = $lfn $ yulmonad'p
--   \inc_p -> LVM.do
--   u <- yembed()
--   (acc, counterRef) <- pass (yulCaller'l u) (counterMap `shmapRef`)
--   let currentValue = callFn'l getCounter' acc
--   sput counterRef (currentValue + ver'l inc_p)
