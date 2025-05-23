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

embTrue'l :: PureFn BOOL
embTrue'l = $lfn $ ylvm'pp $ yembed true

revertIfTrue :: PureFn (BOOL -> U256 -> U256)
revertIfTrue = $fn
  $ \t x -> if t then yulRevert else x

-- Test function recursion; but it will reach stack limit of EVM.
rangeSum'p :: PureFn (U256 -> U256 -> U256 -> U256)
rangeSum'p = $fn \from step til ->
  let j = from + step
  in from + if j <= til
            then call rangeSum'p j step til
            else 0

rangeSum'l :: PureFn (U256 -> U256 -> U256 -> U256)
rangeSum'l = $lfn $ yulports'pp
  \from'p step'p until'p -> call rangeSum'p from'p step'p until'p

callExternalFoo0 :: OmniFn (ADDR -> U256)
callExternalFoo0 = $lfn $ ylvm'pv
  \to -> ycall (to @-> external_foo0)

callExternalFoo1 :: OmniFn (ADDR -> U256 -> U256)
callExternalFoo1 = $lfn $ ylvm'pv
  \to val -> ycall (to @-> external_foo1) (ver val)

callExternalFoo2 :: OmniFn (ADDR -> U256 -> U256 -> U256)
callExternalFoo2 = $lfn $ ylvm'vv
  \to val1 val2 -> ycall (to @-> external_foo2) val1 val2

sgetTest :: StaticFn (ADDR -> U256)
sgetTest = $lfn $ ylvm'pv
  \acc'uv -> LVM.do
    acc <- ytkvarv acc'uv
    key <- embed (42 :: U32)
    ymkvar (sget'l (extendType'l @(REF U256) (keccak256'l (merge'l (key, acc)))))

shmapGetTest :: StaticFn (ADDR -> U256)
shmapGetTest = $lfn $ ylvm'pv
  \acc -> LVM.do
    sgetM $ (makeSMap "shmapGetTest" :: SMap (ADDR -> U256)) #-> acc

varSharing :: PureFn (U256 -> U256 -> U256 -> U256)
varSharing = $fn \a b c ->
  let z = a + b * c in z * z

varSharingL :: PureFn (U256 -> U256 -> U256 -> U256)
varSharingL = $lfn $ yulports'pp
  \a b c ->
  let z = a + b * c in dup'l z & uncurry (*) -- (z1, z2) -> z1 * z2

lvmvar_test1 :: PureFn (U256 -> U256 -> U256)
lvmvar_test1 = $lfn $ ylvm'pp
  \x_ y_ -> ywithuv_1 (x_, y_) \x y -> x * y + y

lvmvar_test2 :: PureFn (U256)
lvmvar_test2 = $lfn $ ylvm'pp LVM.do
  b <- embed (42 :: U256)
  let !(b1, b2) = dup'l b
  ymkvar (b1 + b2)

lvmvar_test3 :: StaticFn (U256)
lvmvar_test3 = $lfn $ ylvm'pv LVM.do
  b <- embed (42 :: U256)
  let !(b1, b2) = dup'l b
  ymkvar (b1 + b2)

lvmvar_test4 :: StaticFn (U256 -> U256 -> U256)
lvmvar_test4 = $lfn $ ylvm'vv
  \x y -> LVM.do
    x1 <- ytkvar x
    x2 <- ytkvar x
    y1 <- ytkvar y
    ymkvar (x1 + x2 * y1)

object = mkYulObject "BasicTests" yulNoop
  [ pureFn "embUnit$p" embUnit'p
  , pureFn "embTrue$p" embTrue'p
  , pureFn "revertIfTrue" revertIfTrue
  , pureFn "embTrue$l" embTrue'l
  , pureFn "rangeSum$p" rangeSum'p
  , pureFn "rangeSum$l" rangeSum'l

--  , omniFn   "callExternalFoo0" callExternalFoo0
  , omniFn   "callExternalFoo1" callExternalFoo1
  , omniFn   "callExternalFoo2" callExternalFoo2

  , staticFn "sgetTest" sgetTest
  , staticFn "shmapGetTest" shmapGetTest

  , pureFn "varSharing" varSharing
  , pureFn "varSharingL" varSharingL

  , pureFn "lvmvar_test1" lvmvar_test1
  , pureFn   "lvmvar_test2" lvmvar_test2
  , staticFn   "lvmvar_test3" lvmvar_test3
  , staticFn "lvmvar_test4" lvmvar_test4
  ]

-- TODO generated interfaces

external_foo0 = externalOmniFn @U256 "foo0"
external_foo1 = externalOmniFn @(U256 -> U256) "foo1"
external_foo2 = externalOmniFn @(U256 -> U256 -> U256) "foo2"
