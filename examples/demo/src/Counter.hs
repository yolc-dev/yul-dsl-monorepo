module Counter where
import Control.LinearlyVersionedMonad qualified as LVM
import Prelude.YulDSL

object = mkYulObject "Counter" emptyCtor
  [ staticFn "getCounter" getCounter
  , omniFn   "incCounter"  incCounter
  ]

counter :: PureFn (() -> REF U256)
counter = $fn $
  \_ -> YulEmb (keyRef "Yolc.Demo.Counter.Storage.Counter")

getCounter :: StaticFn (() -> U256)
getCounter = $lfn $ yulmonad'p
  \u -> sget (callFn'l counter u)

incCounter :: OmniFn (() -> U256 -> ())
incCounter = $lfn $ yulmonad'p
  \u inc_p -> LVM.do
  (counterRef, currentValue) <- pass (callFn'l counter u) sget
  sput counterRef (currentValue + ver'l inc_p)
