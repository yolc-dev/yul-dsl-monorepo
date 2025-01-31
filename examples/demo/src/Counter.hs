module Counter where
import Control.LinearlyVersionedMonad qualified as LVM
import Prelude.YulDSL

object = mkYulObject "Counter" emptyCtor
  [ staticFn "getCounter" getCounter
  , omniFn   "incCounter"  incCounter
  ]

counter :: PureFn (() -> REF U256)
counter = fn $locId $
  \_ -> YulEmb (keyRef "Yolc.Demo.Counter.Storage.Counter")

getCounter :: StaticFn (() -> U256)
getCounter = lfn $locId $ yulmonad'p
  \u -> sget (callFn'l counter u)

incCounter :: OmniFn (() -> U256 -> ())
incCounter = lfn $locId $ yulmonad'p
  \u inc_p -> LVM.do
    (counterRef, newValue_v0) <- pass (callFn'l counter u) \counterRef -> LVM.do
       currentValue <- sget counterRef
       ypure (currentValue + ver'l inc_p)
    sput counterRef newValue_v0

