module LinearFn_tests where
-- hspec
import Test.Hspec
-- (lvm)
import Control.LinearlyVersionedMonad qualified as LVM
--
import Prelude                        ()
import Prelude.YulDSL


--------------------------------------------------------------------------------
-- declaring simple linear functions
--------------------------------------------------------------------------------

foo0 :: StaticFn (() -> U256)
foo0 = $lfn $ uncurry'lvv
  (emb'l 42)

foo1 :: StaticFn (U256 -> U256)
foo1 = $lfn $ uncurry'lvv
  id

foo2 :: StaticFn (U256 -> U256 -> U256)
foo2 = $lfn $ uncurry'lvv
  \x1 x2 -> x1 + x2

foo3 :: StaticFn (U256 -> U256 -> U256 -> U256)
foo3 = $lfn $ uncurry'lvv
  \x1 x2 x3 -> x1 + x2 + x3

foo4 :: StaticFn (U256 -> U256 -> U256 -> U256 -> U256)
foo4 = $lfn $ uncurry'lvv
  \x1 x2 x3 x4 -> x1 + x2 + x3 + x4

--------------------------------------------------------------------------------
-- calling other linear functions
--------------------------------------------------------------------------------

call0 :: StaticFn (() -> U256)
call0 = $lfn $ uncurry'lvv
  \u -> call foo0 u

call1 :: StaticFn (U256 -> U256)
call1 = $lfn $ uncurry'lvv
  \x -> call foo1 x

call2 :: StaticFn (U256 -> U256 -> U256)
call2 = $lfn $ uncurry'lvv
  \x1 x2 -> call foo2 x1 x2

call3 :: StaticFn (U256 -> U256 -> U256 -> U256)
call3 = $lfn $ uncurry'lvv
  \x1 x2 x3 -> call foo3 x1 x2 x3

call4 :: StaticFn (U256 -> U256 -> U256 -> U256 -> U256)
call4 = $lfn $ uncurry'lvv
  \x1 x2 x3 x4 -> call foo4 x1 x2 x3 x4

test_withinPureY :: StaticFn (U256 -> U256 -> U256)
test_withinPureY = $lfn $ uncurry'lvv
  \x1_l x2_l -> withinPureY @(U256 -> U256 -> U256) (x1_l, x2_l)
                \x1 x2 -> x1 + x1 * x2

--------------------------------------------------------------------------------
-- declaring yulmonad functions
--------------------------------------------------------------------------------

bar0 :: StaticFn (U256)
bar0 = $lfn $ yulmonad'p $ LVM.do
  u <- yembed ()
  ypure (call foo0 u)

bar1 :: StaticFn (U256 -> U256)
bar1 = $lfn $ yulmonad'p
  \x1 -> ypure (call foo1 (ver'l x1))

bar3 :: StaticFn (U256 -> U256 -> U256 -> U256)
bar3 = $lfn $ yulmonad'p
  \x1 x2 x3 -> ypure (ver'l x1 + ver'l x2 + ver'l x3)

--------------------------------------------------------------------------------
-- pattern matching
--------------------------------------------------------------------------------

match_maybe :: StaticFn (Maybe U256 -> U256)
match_maybe = $lfn $ uncurry'lvv
  \x1 -> match'l x1 \case
    Just c  -> c
    Nothing -> 0

match_tuple3 :: StaticFn ((BOOL, U256, U256) -> U256)
match_tuple3 = $lfn $ uncurry'lvv $
  flip match'l \(b, x, y) -> if b then x else y

--------------------------------------------------------------------------------
-- storage effect
--------------------------------------------------------------------------------

fooSPut :: OmniFn (B32 -> U256 -> ())
fooSPut = $lfn $ yulmonad'p
  \s_p val_p -> sput s_p (ver'l val_p)

callSPut :: OmniFn (B32 -> U256 -> ())
callSPut = $lfn $ yulmonad'p
  \addr_p var_p -> LVM.do
  ycall fooSPut (ver'l addr_p) (ver'l var_p)

--

tests = describe "LinearFn Tests" $ do
  describe "lfn: linear function builder" $ do
    it "simple fn definitions" True
