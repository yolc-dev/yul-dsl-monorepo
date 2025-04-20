module Counter where
import Control.LinearlyVersionedMonad.LVM qualified as LVM
import Prelude.YulDSL

object = mkYulObject "Counter" yulNoop
  [ staticFn "getGlobalCounter" getGlobalCounter
  , omniFn   "incGlobalCounter" incGlobalCounter
  , staticFn "getCounter" getCounter
  , omniFn   "incCounter" incCounter
  ]

globalCounterLoc :: PureFn (REF U256)
globalCounterLoc = $fn do
  yulEmb (keyRef "Yolc.Demo.Counter.Storage.Counter.Global")

incGlobalCounter :: OmniFn (U256 -> ())
incGlobalCounter = $lfn $ yullvm'p
  \inc_p -> LVM.do
    counterRef <- ycall0 globalCounterLoc
    (counterRef, currentValue) <- pass1 counterRef sget
    sput counterRef (currentValue + ver'l inc_p)

getGlobalCounter :: StaticFn U256
getGlobalCounter = $lfn $ yullvm'p $ LVM.do
  counterRef <- ycall0 globalCounterLoc
  sget counterRef

-- | Storage map of user counters
counterMap :: SHMap ADDR U256
counterMap = shmap "Yolc.Demo.Counter.Storage.Counter.PerUser"

getCounter :: StaticFn (ADDR -> U256)
getCounter = $lfn $ yullvm'p
  \acc -> counterMap `shmapGet` acc

incCounter :: OmniFn (U256 -> ())
incCounter = $lfn $ yullvm'p
  \inc_p -> LVM.do
    acc <- ycaller
    counterRef <- counterMap `shmapRef` acc
    (counterRef, newValue) <- pass1 counterRef \counterRef -> LVM.do
      currentValue <- sget counterRef
      ypure $ withinPureY @(U256 -> U256 -> U256)
              (currentValue, ver'l inc_p)
              (\a b -> a + b)
    sput counterRef newValue
