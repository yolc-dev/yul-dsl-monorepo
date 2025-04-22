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
incGlobalCounter = $lfn $ yullvm'pv
  \(Uv inc'uv) -> LVM.do
    inc_p <- ytake1 inc'uv
    counterRef <- ycall0 globalCounterLoc
    (counterRef, currentValue) <- pass1 counterRef sget
    sput counterRef (currentValue + ver'l inc_p)

    yembed ()

getGlobalCounter :: StaticFn U256
getGlobalCounter = $lfn $ yullvm'pv LVM.do
  counterRef <- ycall0 globalCounterLoc
  ypure LVM.=<< sget counterRef

-- | Storage map of user counters
counterMap :: SHMap ADDR U256
counterMap = shmap "Yolc.Demo.Counter.Storage.Counter.PerUser"

getCounter :: StaticFn (ADDR -> U256)
getCounter = $lfn $ yullvm'pv
  \(Uv acc'uv) -> LVM.do
    acc <- ytakev1 acc'uv
    ypure LVM.=<< counterMap `shmapGet` acc

incCounter :: OmniFn (U256 -> ())
incCounter = $lfn $ yullvm'pv
  \(Uv inc'uv) -> LVM.do
    acc <- ycaller
    counterRef <- counterMap `shmapRef` acc

    (counterRef, newValue) <- pass1 counterRef \counterRef -> LVM.do
      inc_p <- ytakev1 inc'uv
      currentValue <- sget counterRef
      let !(MkSolo newValue) = with'l @(U256 -> U256 -> Solo U256)
                               (currentValue, ver'l inc_p)
                               (\a b -> be (a + b))
      LVM.pure newValue
    sput counterRef newValue

    yembed ()
