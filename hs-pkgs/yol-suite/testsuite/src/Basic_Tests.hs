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
embTrue'l = $lfn $ yullvm'pp $ yembed true

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

rangeSum'l :: PureFn (U256 -> U256 -> U256 -> U256)
rangeSum'l = $lfn $ yulports'pp
  \from'p step'p until'p -> call rangeSum'p from'p step'p until'p

  -- FIXME: yikes, this is ugly and we need to improve.
-- FIXME: this does't even work; codegen error in extcall.
-- callExternalFoo0 :: OmniFn (ADDR -> U256)
-- callExternalFoo0 = $lfn $ yullvm'pv
--  \(Uv to'uv) -> LVM.do
--    to <- ytakev1 to'uv
--    u <- embed ()
--    ret <- externalCall external_foo0 to u
--    Ur retref <- ymkref ret
--    LVM.pure retref

callExternalFoo1 :: OmniFn (ADDR -> U256 -> U256)
callExternalFoo1 = $lfn $ yullvm'pv
  \(Uv to'uv) (Uv val1'uv) -> LVM.do
    to'p <- ytake1 to'uv
    val1'p <- ytake1 val1'uv
    ypure LVM.=<< externalCall external_foo1 (ver'l to'p) (ver'l val1'p)

callExternalFoo2 :: OmniFn (ADDR -> U256 -> U256 -> U256)
callExternalFoo2 = $lfn $ yullvm'vv
  \(Rv to'rv) (Rv val1'rv) (Rv val2'rv) -> LVM.do
    to <- ytake1 to'rv
    val1 <- ytake1 val1'rv
    val2 <- ytake1 val2'rv
    ypure LVM.=<< externalCall external_foo2 to val1 val2

sgetTest :: StaticFn (ADDR -> U256)
sgetTest = $lfn $ yullvm'pv
  \(Uv acc'uv) -> LVM.do
    acc'p <- ytakev1 acc'uv
    key <- embed (42 :: U32)
    ypure LVM.=<< sget (extendType'l @(REF U256) (keccak256'l (merge'l (key, acc'p))))

shmapGetTest :: StaticFn (ADDR -> U256)
shmapGetTest = $lfn $ yullvm'pv
  \(Uv acc'uv) -> LVM.do
    acc'p <- ytakev1 acc'uv
    sslot <- (shmapRef @ADDR @U256) (shmap "shmapGetTest" :: SHMap ADDR U256) acc'p
    ypure LVM.=<< sget sslot

varSharing :: PureFn (U256 -> U256 -> U256 -> U256)
varSharing = $fn \a b c ->
  let z = a + b * c in z * z

varSharingL :: PureFn (U256 -> U256 -> U256 -> U256)
varSharingL = $lfn $ yulports'pp
  \a b c ->
  let z = a + b * c in dup'l z & uncurry (*) -- (z1, z2) -> z1 * z2

lvmvar_test1 :: PureFn (U256 -> U256 -> U256)
lvmvar_test1 = $lfn $ yullvm'pp
  \(Uv x_) (Uv y_) -> LVM.do
    (MkSolo r) <- ywithUv @(U256 -> U256 -> Solo U256) (Uv x_, Uv y_) \x y -> be (x * y + y)
    LVM.pure r

lvmvar_test2 :: PureFn (U256)
lvmvar_test2 = $lfn $ yullvm'pp LVM.do
  b <- embed (42 :: U256)
  let !(b1, b2) = dup'l b
  ypure (b1 + b2)

lvmvar_test3 :: StaticFn (U256)
lvmvar_test3 = $lfn $ yullvm'pv LVM.do
  b <- embed (42 :: U256)
  let !(b1, b2) = dup'l b
  ypure (b1 + b2)

lvmvar_test4 :: StaticFn (U256 -> U256 -> U256)
lvmvar_test4 = $lfn $ yullvm'vv
  \(Rv x) (Rv y) -> LVM.do
    x1 <- ytake1 x
    x2 <- ytake1 x
    y1 <- ytake1 y
    ypure (x1 + x2 * y1)

object = mkYulObject "BasicTests" yulNoop
  [ pureFn   "embUnit$p" embUnit'p
  , pureFn   "embTrue$p" embTrue'p
  , pureFn   "revertIfTrue" revertIfTrue
  , pureFn "embTrue$l" embTrue'l
  , pureFn   "rangeSum$p" rangeSum'p
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

external_foo0 = declareExternalFn @(() -> U256) "foo0"
external_foo1 = declareExternalFn @(U256 -> U256) "foo1"
external_foo2 = declareExternalFn @(U256 -> U256 -> U256) "foo2"
