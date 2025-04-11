{-
Test code generations for typical and problematic functions.
-}
module Basic_Tests where
import Prelude.YulDSL
import Control.LinearlyVersionedMonad.LVM qualified as LVM


embUnit'p :: PureFn (I256 -> ())
embUnit'p = $fn $ \a -> a >.> yulEmb ()

embTrue'p :: PureFn BOOL
embTrue'p = $fn $ yulEmb true

embTrue'l :: StaticFn BOOL
embTrue'l = $lfn $ yulmonad'p (embed true)

revertIfTrue :: PureFn (BOOL -> U256 -> U256)
revertIfTrue = $fn
  $ \t x -> if t then yulRevert else x

-- Test function recursion; but it will reach stack limit of EVM.
rangeSum'p :: PureFn (U256 -> U256 -> U256 -> U256)
rangeSum'p = $fn \from step until ->
  let j = from + step
  in from + if j <= until
            then call rangeSum'p j step until
            else 0

rangeSum'l :: StaticFn (U256 -> U256 -> U256 -> U256)
rangeSum'l = $lfn $ yulmonad'p
  \from'p step'p until'p -> ypure $ ver'l $ call rangeSum'p from'p step'p until'p

  -- FIXME: yikes, this is ugly and we need to improve.
-- FIXME: this does't even work
-- callExternalFoo0 :: OmniFn (ADDR -> U256)
-- callExternalFoo0 = $lfn $ yulmonad'v
--  \to -> dup2'l to & \(to1, to2) -> externalCall external_foo0 to1 (discard'l to2)

callExternalFoo1 :: OmniFn (ADDR -> U256 -> U256)
callExternalFoo1 = $lfn $ yulmonad'v
  \to val1 -> externalCall external_foo1 to val1

callExternalFoo2 :: OmniFn (ADDR -> U256 -> U256 -> U256)
callExternalFoo2 = $lfn $ yulmonad'v
  \to val1 val2 -> externalCall external_foo2 to val1 val2

sgetTest :: StaticFn (ADDR -> ())
sgetTest = $lfn $ yulmonad'v
  \ acc -> LVM.do
    key <- yembed (42 :: U32)
    ref <- ypure (extendType'l @(REF U256) (keccak256'l (merge'l (key, acc))))
    toss1 ref

shmapGetTest :: StaticFn (ADDR -> ())
shmapGetTest = $lfn $ yulmonad'v
  \acc -> LVM.do
    ref <- (shmapRef @ADDR @U256) (shmap "YolcStorageTest" :: SHMap ADDR U256) acc
    toss1 ref

varSharing :: PureFn (U256 -> U256 -> U256)
varSharing = $fn \a b ->
  let c = a + b in c * c

varSharingL :: StaticFn (U256 -> U256 -> U256)
varSharingL = $lfn $ yulmonad'p \a b ->
  let c = a + b in dup2'l c & \(c1, c2) -> ypure (ver'l (c1 * c2))

lvmvar_test_ugly :: StaticFn (U256 -> U256)
lvmvar_test_ugly = $lfn $ yulmonad'p
  \x -> LVM.do
    let !(x1, x2') = dup2'l (ver'l x)
        !(x2, x3)  = dup2'l x2'
    ypure (x1 + x2 * x3)

lvmvar_test :: StaticFn (U256 -> U256)
lvmvar_test = $lfn $ yulmonad'p
  \x -> LVM.do
    let !(Ur varX, registry) = registerUvLVMVar x initLVMVarRegistry
    (x1, registry) <- vreadLVMVarRef varX registry
    (x2, registry) <- vreadLVMVarRef varX registry
    (x3, registry) <- vreadLVMVarRef varX registry
    consumeLVMVarRegistry registry
    ypure (x1 + x2 * x3)

object = mkYulObject "BasicTests" yulNoop
  [ pureFn   "embUnit$p" embUnit'p
  , pureFn   "embTrue$p" embTrue'p
  , pureFn   "revertIfTrue" revertIfTrue
  , staticFn "embTrue$l" embTrue'l
  , pureFn   "rangeSum$p" rangeSum'p
  , staticFn "rangeSum$l" rangeSum'l
-- , omniFn   "callExternalFoo0" callExternalFoo0
  , omniFn   "callExternalFoo1" callExternalFoo1
  , omniFn   "callExternalFoo2" callExternalFoo2

  , staticFn "sgetTest" sgetTest
  , staticFn "shmapGetTest" shmapGetTest

  , pureFn "varSharing" varSharing
  , staticFn "varSharingL" varSharingL

  , staticFn "lvmvar_test_ugly" lvmvar_test_ugly
  , staticFn "lvmvar_test" lvmvar_test
  ]


-- TODO generated interfaces

external_foo0 = declareExternalFn @(() -> U256) "foo0"
external_foo1 = declareExternalFn @(U256 -> U256) "foo1"
external_foo2 = declareExternalFn @(U256 -> U256 -> U256) "foo2"
