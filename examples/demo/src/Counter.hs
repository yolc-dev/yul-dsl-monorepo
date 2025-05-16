module Counter where
import Control.LinearlyVersionedMonad.LVM qualified as LVM
import Prelude.YulDSL


object = mkYulObject "Counter" yulNoop
  [ staticFn "getGlobalCounter" getGlobalCounter
  , omniFn   "incGlobalCounter" incGlobalCounter
  , staticFn "getCounter" getCounter
  , omniFn   "incCounter" incCounter
  ]

--
-- Global counter using raw REF
--

globalCounterLoc :: PureFn (REF U256)
globalCounterLoc = $fn do
  yulEmb (keyRef "Yolc.Demo.Counter.Storage.Counter.Global")


incGlobalCounter :: OmniFn (U256 -> ())
incGlobalCounter = $lfn $ ylvm'pv
  \inc -> LVM.do
    Ur counterRef <- ycalluv_0 globalCounterLoc

    Ur currentValue <- sget counterRef

    Ur newValue <- ywithrv_1 @(U256 -> U256 -> U256)
      (currentValue, ver inc)
      (\a b -> a + b)

    ycalluv_0 globalCounterLoc <<:= newValue

    yembed ()

getGlobalCounter :: StaticFn U256
getGlobalCounter = $lfn $ ylvm'pv LVM.do
  Ur counterRef <- ycalluv_0 globalCounterLoc
  sget counterRef

--
-- User-owned counters using SMap
--

userCounterMap :: SMap (ADDR -> U256)
userCounterMap = makeSMap "Yolc.Demo.Counter.Storage.Counter.PerUser"

getCounter :: StaticFn (ADDR -> U256)
getCounter = $lfn $ ylvm'pv \acc -> sgetM (userCounterMap #-> acc)

incCounter :: OmniFn (U256 -> ())
incCounter = $lfn $ ylvm'pv
  \inc -> LVM.do
    Ur acc <- ycaller

    Ur currentValue <- sgetM (userCounterMap #-> acc)

    Ur newValue <- ywithrv_1 @(U256 -> U256 -> U256)
      (currentValue, ver inc)
      (\a b -> a + b)

    userCounterMap #-> acc <<:= newValue

    yembed ()
