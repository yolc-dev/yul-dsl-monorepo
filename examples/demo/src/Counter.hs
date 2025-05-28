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

getGlobalCounter :: StaticFn U256
getGlobalCounter = $lfn $ ylvm'pv LVM.do
  sgetM (ycall globalCounterLoc)

incGlobalCounter :: OmniFn (U256 -> ())
incGlobalCounter = $lfn $ ylvm'pv
  \inc -> LVM.do
    Ur currentValue <- ycall getGlobalCounter

    Ur newValue <- yrpurelamN_1 (currentValue, ver inc) \x y -> x + y

    ycalluv globalCounterLoc <<:= newValue

    yembed ()

--
-- User-owned counters using SMap
--

userCounterMap :: SMap (ADDR -> U256)
userCounterMap = makeSMap "Yolc.Demo.Counter.Storage.Counter.PerUser"

getCounter :: StaticFn (ADDR -> U256)
getCounter = $lfn $ ylvm'pv \acc -> sgetM (userCounterMap #-> acc)

incCounter :: OmniFn (U256 -> ())
incCounter = $lfn $ ylvm'pv
  -- [solidity]  function incCounter(uint256 inc) returns ()
  \inc -> LVM.do
    -- [solidity] address acc = msg.sender
    Ur acc <- ycaller

    -- [solidity] uint256 currentValue = userCounterMap[acc]
    Ur currentValue <- sgetM (userCounterMap #-> acc)

    -- [solidity] uin256 newValue = currentValue + inc
    Ur newValue <- yrpurelamN_1 (currentValue, ver inc) \x y -> x + y

    -- [solidity]  userCounterMap[acc] = newValue
    userCounterMap #-> acc <<:= newValue

    yembed ()
