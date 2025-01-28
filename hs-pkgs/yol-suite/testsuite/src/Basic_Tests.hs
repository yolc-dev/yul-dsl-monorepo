{-
Test code generations for typical and problematic functions.
-}
module Basic_Tests where
import Prelude.YulDSL

embUnit'p = fn @(I256 -> ()) $locId \_ -> YulEmb ()

embTrue'p = fn @(BOOL) $locId $ YulEmb true

embTrue'l = lfn $locId $ yulmonad'p @(BOOL) (embed true)

revertIfTrue = fn @(BOOL -> U256 -> U256) $locId
  $ \t x -> if t then yulRevert else x

-- Test function recursion; but it will reach stack limit of EVM.
rangeSum'p = fn @(U256 -> U256 -> U256 -> U256) $locId
  \from step until -> let j = from + step
                      in from + if j <= until
                                then callFn rangeSum'p j step until
                                else 0

rangeSum'l = lfn $locId $ yulmonad'p @(U256 -> U256 -> U256 -> U256)
  \from'p step'p until'p -> ypure $ ver'l $ callFn'lpp rangeSum'p from'p step'p until'p

-- TODO: yikes, this is ugly and we need to improve.
callExternalFoo0 = lfn $locId $ yulmonad'v @(ADDR -> U256)
  \to -> dup2'l to & \(to1, to2) -> externalCall external_foo0 to1 (discard'l to2)

callExternalFoo1 = lfn $locId $ yulmonad'v @(ADDR -> U256 -> U256)
  \to val1 -> externalCall external_foo1 to val1

callExternalFoo2 = lfn $locId $ yulmonad'v @(ADDR -> U256 -> U256 -> U256)
  \to val1 val2 -> externalCall external_foo2 to val1 val2

object = mkYulObject "BasicTests" emptyCtor
  [ pureFn   "embUnit$p" embUnit'p
  , pureFn   "embTrue$p" embTrue'p
  , pureFn   "revertIfTrue" revertIfTrue
  , staticFn "embTrue$l" embTrue'l
  , pureFn   "rangeSum$p" rangeSum'p
  , staticFn "rangeSum$l" rangeSum'l
  , omniFn   "callExternalFoo0" callExternalFoo0
  , omniFn   "callExternalFoo1" callExternalFoo1
  , omniFn   "callExternalFoo2" callExternalFoo2
  ]


-- TODO generated interfaces

external_foo0 = declareExternalFn @(() -> U256) "foo0"
external_foo1 = declareExternalFn @(U256 -> U256) "foo1"
external_foo2 = declareExternalFn @(U256 -> U256 -> U256) "foo2"
