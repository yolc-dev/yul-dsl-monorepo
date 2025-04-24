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
  \(Uv inc) -> LVM.do
    Rv counterRef <- LVM.do
      counterRef_p <- ycall0 globalCounterLoc
      ymkref counterRef_p

    Rv currentValue <- sget counterRef

    MkSolo (Rv newValue) <- ywithAny @(U256 -> U256 -> Solo U256)
      (AnyRv currentValue, AnyUv inc)
      (\a b -> be (a + b))

    sput counterRef newValue

    yembed ()

getGlobalCounter :: StaticFn U256
getGlobalCounter = $lfn $ yullvm'pv LVM.do
  counterRef <- ycall0 globalCounterLoc
  ymkref (sget'l counterRef)

-- | Storage map of user counters
counterMap :: SHMap ADDR U256
counterMap = shmap "Yolc.Demo.Counter.Storage.Counter.PerUser"

getCounter :: StaticFn (ADDR -> U256)
getCounter = $lfn $ yullvm'pv \(Uv acc) -> counterMap `shmapGet` acc

incCounter :: OmniFn (U256 -> ())
incCounter = $lfn $ yullvm'pv
  \(Uv inc) -> LVM.do
    Uv acc <- ymkref LVM.=<< ycaller

    Uv counterRef <- shmapRef counterMap acc
    Rv currentValue <- sget counterRef

    MkSolo (Rv newValue) <- ywithAny @(U256 -> U256 -> Solo U256)
      (AnyRv currentValue, AnyUv inc)
      (\a b -> be (a + b))

    sput counterRef newValue
    yembed ()
