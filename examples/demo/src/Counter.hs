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
incGlobalCounter = $lfn $ ylvm'pv
  \(Uv inc) -> LVM.do
    Ur (Uv counterRef) <- ycalluv_0 globalCounterLoc

    Ur (Rv currentValue) <- sget (Uv counterRef)

    Ur (Rv newValue) <- ywithrvN_1 @(U256 -> U256 -> U256)
      (Rv currentValue, ver inc)
      (\a b -> a + b)

    sput (ycalluv_0 globalCounterLoc := Rv newValue)

    yembed ()

getGlobalCounter :: StaticFn U256
getGlobalCounter = $lfn $ ylvm'pv LVM.do
  Ur (Uv counterRef) <- ycalluv_0 globalCounterLoc
  sget (Uv counterRef)

-- | Storage map of user counters
counterMap :: SHMap ADDR U256
counterMap = shmap "Yolc.Demo.Counter.Storage.Counter.PerUser"

getCounter :: StaticFn (ADDR -> U256)
getCounter = $lfn $ ylvm'pv \(Uv acc) -> counterMap `shmapGet` Uv acc

incCounter :: OmniFn (U256 -> ())
incCounter = $lfn $ ylvm'pv
  \(Uv inc) -> LVM.do
    -- TODO: Uv acc <- ycaller
    Ur (Uv acc) <- ycaller

    Ur (Uv counterRef) <- shmapRef counterMap (Uv acc)
    Ur (Rv currentValue) <- sget (Uv counterRef)

    Ur (Rv newValue) <- ywithrvN_1 @(U256 -> U256 -> U256)
      (Rv currentValue, ver inc)
      (\a b -> a + b)

    sput (counterMap .-> Uv acc := Rv newValue)
    yembed ()
