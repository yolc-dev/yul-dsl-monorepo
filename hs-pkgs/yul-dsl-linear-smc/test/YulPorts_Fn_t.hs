module YulPorts_Fn_t where
-- base
import Prelude         ((<$>))
import Prelude qualified as BasePrelude
-- hspec, quickcheck
import Test.Hspec
import Test.QuickCheck
-- yul-dsl
import YulDSL.Eval
import Prelude.YulDSL

------------------------------------------------------------------------------------------------------------------------
-- declaring simple linear functions
------------------------------------------------------------------------------------------------------------------------

pure_fn0 :: PureFn (U256)
pure_fn0 = $fn $ yulEmb 42

pure_fn0u :: PureFn (() -> U256)
pure_fn0u = $lfn $ yulports'pp
  (emb'l 42)

static_fn0u :: StaticFn (() -> U256)
static_fn0u = $lfn $ yulports'vv
  (emb'l 42)

static_fn1 :: StaticFn (U256 -> U256)
static_fn1 = $lfn $ yulports'vv
  id

static_fn2 :: StaticFn (U256 -> U256 -> U256)
static_fn2 = $lfn $ yulports'vv
  \x1 x2 -> x1 + x2

static_fn3 :: StaticFn (U256 -> U256 -> U256 -> U256)
static_fn3 = $lfn $ yulports'vv
  \x1 x2 x3 -> x1 + x2 + x3

static_fn4 :: StaticFn (U256 -> U256 -> U256 -> U256 -> U256)
static_fn4 = $lfn $ yulports'vv
  \x1 x2 x3 x4 -> x1 + x2 + x3 + x4

------------------------------------------------------------------------------------------------------------------------
-- calling other linear functions
------------------------------------------------------------------------------------------------------------------------

-- call_pure_fn0 :: StaticFn (() -> U256)
-- call_pure_fn0 = $lfn $ yulports'vv
--   \u -> call pure_fn0

call_pure_fn0u :: StaticFn (() -> U256)
call_pure_fn0u = $lfn $ yulports'vv
  \u -> call pure_fn0u u

call_static_fn0u :: StaticFn (() -> U256)
call_static_fn0u = $lfn $ yulports'vv
  \u -> call static_fn0u u

call_static_fn1 :: StaticFn (U256 -> U256)
call_static_fn1 = $lfn $ yulports'vv
  \x -> call static_fn1 x

call_static_fn2 :: StaticFn (U256 -> U256 -> U256)
call_static_fn2 = $lfn $ yulports'vv
  \x1 x2 -> call static_fn2 x1 x2

call_static_fn3 :: StaticFn (U256 -> U256 -> U256 -> U256)
call_static_fn3 = $lfn $ yulports'vv
  \x1 x2 x3 -> call static_fn3 x1 x2 x3

call_static_fn4 :: StaticFn (U256 -> U256 -> U256 -> U256 -> U256)
call_static_fn4 = $lfn $ yulports'vv
  \x1 x2 x3 x4 -> call static_fn4 x1 x2 x3 x4

------------------------------------------------------------------------------------------------------------------------
-- working with purelam
------------------------------------------------------------------------------------------------------------------------

test_purelam :: StaticFn (U256 -> U256 -> U256)
test_purelam = $lfn $ yulports'vv
  \x1'v x2'v ->
    let !(r :* Nil) = purelamNP'l (x1'v :* x2'v :* Nil)
          \(x1 :* x2 :* Nil) -> be ((x1 + x1 * x2) :* Nil)
    in r

------------------------------------------------------------------------------------------------------------------------
-- tuples
------------------------------------------------------------------------------------------------------------------------

tuple2_result :: StaticFn (U256 -> U256 -> (U256, U256))
tuple2_result = $lfn $ yulports'vv
  \x1 x2 -> be (dup'l (x1 + x2))

tuple2_input :: StaticFn ((U256, U256) -> U256)
tuple2_input = $lfn $ yulports'vv
  -- Note: Unfortunately, viewpattern doesn't support linear arrow well at the moment
  -- \(is -> (x1, x2)) -> x1 + x1
  \xs -> let !(x1, x2) = is xs in x1 + x2

------------------------------------------------------------------------------------------------------------------------
-- num
------------------------------------------------------------------------------------------------------------------------

num_add :: StaticFn (I256 -> I256 -> I256)
num_add = $lfn $ yulports'vv
  \x1 x2 -> x1 + x2

num_sub :: StaticFn (I256 -> I256 -> I256)
num_sub = $lfn $ yulports'vv
  \x1 x2 -> x1 - x2

num_mul :: StaticFn (I256 -> I256 -> I256)
num_mul = $lfn $ yulports'vv
  \x1 x2 -> x1 * x2

test_num_2op :: Gen Bool
test_num_2op = BasePrelude.do
  x <- BasePrelude.fromInteger <$> chooseInteger (0, toInteger (maxBound @U32))
  y <- BasePrelude.fromInteger <$> chooseInteger (0, toInteger (maxBound @U32))
  BasePrelude.pure $ BasePrelude.and
    [ evalFn num_add (I x :* I y :* Nil) BasePrelude.== x + y
    , evalFn num_sub (I x :* I y :* Nil) BasePrelude.== x - y
    , evalFn num_mul (I x :* I y :* Nil) BasePrelude.== x * y
    ]

------------------------------------------------------------------------------------------------------------------------

test_effect_classification :: Bool
test_effect_classification = BasePrelude.and
  [ classifyYulCatEffect @PureInputPureOutput BasePrelude.== PureEffect
  , classifyYulCatEffect @(PureInputVersionedOutput 0) BasePrelude.== StaticEffect
  , classifyYulCatEffect @(PureInputVersionedOutput 1) BasePrelude.== OmniEffect
  , classifyYulCatEffect @(VersionedInputOutput 0) BasePrelude.== StaticEffect
  , classifyYulCatEffect @(VersionedInputOutput 1) BasePrelude.== OmniEffect

  , withKnownNamedYulCat pure_fn0u (\(_ :: NamedYulCat eff a b) -> classifyYulCatEffect @eff)
    BasePrelude.== PureEffect
  , classifyKnownNamedYulCat pure_fn0u BasePrelude.== PureEffect

  , withKnownNamedYulCat static_fn0u (\(_ :: NamedYulCat eff a b) -> classifyYulCatEffect @eff)
    BasePrelude.== StaticEffect
  , classifyKnownNamedYulCat static_fn0u BasePrelude.== StaticEffect
  ]

--------------------------------------------------------------------------------

tests = describe "YulPorts Linear Function" $ BasePrelude.do
  it "compiles" True
  it "Num binary ops" $ property test_num_2op
  it "Linear effects classification" test_effect_classification
