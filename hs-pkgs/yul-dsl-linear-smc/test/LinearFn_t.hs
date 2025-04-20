module LinearFn_t where
-- hspec
import Test.Hspec
-- (lvm)
import Control.LinearlyVersionedMonad.LVM qualified as LVM
--
import Prelude                        ((>>))
import Prelude qualified as BasePrelude
import Prelude.YulDSL


--------------------------------------------------------------------------------
-- declaring simple linear functions
--------------------------------------------------------------------------------

foo0 :: PureFn (() -> U256)
foo0 = $lfn $ yulports'pp
  (emb'l 42)

foo1 :: StaticFn (U256 -> U256)
foo1 = $lfn $ yulports'vv
  id

foo2 :: StaticFn (U256 -> U256 -> U256)
foo2 = $lfn $ yulports'vv
  \x1 x2 -> x1 + x2

foo3 :: StaticFn (U256 -> U256 -> U256 -> U256)
foo3 = $lfn $ yulports'vv
  \x1 x2 x3 -> x1 + x2 + x3

foo4 :: StaticFn (U256 -> U256 -> U256 -> U256 -> U256)
foo4 = $lfn $ yulports'vv
  \x1 x2 x3 x4 -> x1 + x2 + x3 + x4

--------------------------------------------------------------------------------
-- calling other linear functions
--------------------------------------------------------------------------------

call0 :: StaticFn (() -> U256)
call0 = $lfn $ yulports'vv
  \u -> call foo0 u

call1 :: StaticFn (U256 -> U256)
call1 = $lfn $ yulports'vv
  \x -> call foo1 x

call2 :: StaticFn (U256 -> U256 -> U256)
call2 = $lfn $ yulports'vv
  \x1 x2 -> call foo2 x1 x2

call3 :: StaticFn (U256 -> U256 -> U256 -> U256)
call3 = $lfn $ yulports'vv
  \x1 x2 x3 -> call foo3 x1 x2 x3

call4 :: StaticFn (U256 -> U256 -> U256 -> U256 -> U256)
call4 = $lfn $ yulports'vv
  \x1 x2 x3 x4 -> call foo4 x1 x2 x3 x4

--------------------------------------------------------------------------------
-- declaring yullvm functions
--------------------------------------------------------------------------------

bar0 :: StaticFn (U256)
bar0 = $lfn $ yullvm'p $ LVM.do
  u <- yembed ()
  ypure (call foo0 u)

bar1 :: StaticFn (U256 -> U256)
bar1 = $lfn $ yullvm'p
  \x1 -> ypure (call foo1 (ver'l x1))

bar3 :: StaticFn (U256 -> U256 -> U256 -> U256)
bar3 = $lfn $ yullvm'p
  \x1 x2 x3 -> ypure (ver'l x1 + ver'l x2 + ver'l x3)

--------------------------------------------------------------------------------
-- working with PureY
--------------------------------------------------------------------------------

test_withinPureY :: StaticFn (U256 -> U256 -> U256)
test_withinPureY = $lfn $ yulports'vv
  \x1_l x2_l -> withinPureY @(U256 -> U256 -> U256) (x1_l, x2_l)
                \x1 x2 -> x1 + x1 * x2

--------------------------------------------------------------------------------
-- tuples
--------------------------------------------------------------------------------

tuple2_result :: StaticFn (U256 -> U256 -> (U256, U256))
tuple2_result = $lfn $ yulports'vv
  \x1 x2 -> be (dup2'l (x1 + x2))

tuple2_input :: StaticFn ((U256, U256) -> U256)
tuple2_input = $lfn $ yulports'vv
  -- Note: Unfortunately, viewpattern doesn't support linear arrow well at the moment
  -- \(is -> (x1, x2)) -> x1 + x1
  \xs -> let !(x1, x2) = is xs in x1 + x2

--------------------------------------------------------------------------------
-- storage effect
--------------------------------------------------------------------------------

fooSPut :: OmniFn (B32 -> U256 -> ())
fooSPut = $lfn $ yullvm'p
  \s_p val_p -> sput s_p (ver'l val_p)

callSPut :: OmniFn (B32 -> U256 -> ())
callSPut = $lfn $ yullvm'p
  \addr_p var_p -> LVM.do
  ycall fooSPut (ver'l addr_p) (ver'l var_p)

--------------------------------------------------------------------------------

test_effect_classification :: Bool
test_effect_classification = and
  [ classifyYulCatEffect @PureInputPureOutput BasePrelude.== PureEffect
  , classifyYulCatEffect @(PureInputVersionedOutput 0) BasePrelude.== StaticEffect
  , classifyYulCatEffect @(PureInputVersionedOutput 1) BasePrelude.== OmniEffect
  , classifyYulCatEffect @(VersionedInputOutput 0) BasePrelude.== StaticEffect
  , classifyYulCatEffect @(VersionedInputOutput 1) BasePrelude.== OmniEffect
  , withKnownNamedYulCat foo0 (\(_ :: NamedYulCat eff a b) -> classifyYulCatEffect @eff) BasePrelude.== PureEffect
  , classifyKnownNamedYulCat foo0 BasePrelude.== PureEffect
  , withKnownNamedYulCat bar1 (\(_ :: NamedYulCat eff a b) -> classifyYulCatEffect @eff) BasePrelude.== StaticEffect
  , classifyKnownNamedYulCat bar1 BasePrelude.== StaticEffect
  , withKnownNamedYulCat fooSPut (\(_ :: NamedYulCat eff a b) -> classifyYulCatEffect @eff) BasePrelude.== OmniEffect
  , classifyKnownNamedYulCat fooSPut BasePrelude.== OmniEffect
  ]

--------------------------------------------------------------------------------

tests = describe "YulDSL.Haskell.Effects.LinearSMC.LinearFn" $ do
  it "simple fn definitions" True
  it "linear effects classification" test_effect_classification
