module Fn_tests where
-- base
import Data.Functor                 ((<&>))
-- hspec, quickcheck
import Test.Hspec
import Test.QuickCheck
-- eth-abi
import Ethereum.ContractABI
-- yul-dsl
import YulDSL.Core
import YulDSL.Eval
--
import YulDSL.Haskell.Lib
--
import TestCommon                   ()


--------------------------------------------------------------------------------
-- Trivial functions
--------------------------------------------------------------------------------

dis_any' :: forall a. YulO1 a => PureY (a -> ())
dis_any' _ = YulEmb()

dis_any :: forall a. YulO1 a => PureFn (a -> ())
dis_any = fn' "dis_any" dis_any'

--------------------------------------------------------------------------------
-- Simple functions
--------------------------------------------------------------------------------

tuple_addNP :: PureY (NP [U256, U256] -> U256)
tuple_addNP (is -> (a :* b :* Nil)) = a + b

test_tuple_addNP1 :: PureFn (U256 -> U256)
test_tuple_addNP1 = $fn \a -> tuple_addNP (be (a, a) >.> YulReduceType)

test_tuple_addNP2 :: PureFn (U256 -> U256)
test_tuple_addNP2 = $fn \a -> tuple_addNP (a `yulCons` a `yulCons` yulNil)

test_tuple_addNP3 :: PureFn (U256 -> U256)
test_tuple_addNP3 = $fn \a -> tuple_addNP (couldBe (a :* a :* Nil))

tuple_add :: PureY ((U256, U256) -> U256)
tuple_add (is -> (a, b)) = a + b

uncurry_fn0 :: PureFn (U256)
uncurry_fn0 = $fn 42

uncurry_fn1 :: PureFn (U256 -> U256)
uncurry_fn1 = $fn \a -> tuple_add (be (a, a))

uncurry_fn2 :: PureFn (U256 -> U256 -> U256)
uncurry_fn2 = $fn \a b -> tuple_add (be (a, b))

uncurry_fn3 :: PureFn (U256 -> U256 -> U256 -> U256)
uncurry_fn3 = $fn \a b c -> a + b + c

uncurry_fn4 :: PureFn (U256 -> U256 -> U256 -> U256 -> U256)
uncurry_fn4 = $fn \a b c d -> f a b + f c d
  where f a b = a + b

call_fn0 :: PureFn (U256)
call_fn0 = $fn
  do uncurry_fn0 <$*> ()

-- call_fn0' :: PureFn (U256)
-- call_fn0' = $fn
--   do callNP' uncurry_fn0

call_fn1 :: PureFn (U256 -> U256)
call_fn1 = $fn
  \a -> callNP uncurry_fn1 a

call_fn2 :: PureFn (U256 -> U256)
call_fn2 = $fn
  \a -> callNP uncurry_fn2 a a

call_fn3 :: PureFn (U256 -> U256)
call_fn3 = $fn
  \a -> callNP uncurry_fn3 a a a

call_fn4 :: PureFn (U256 -> U256)
call_fn4 = $fn
  \a -> callNP uncurry_fn4 a a a a

test_simple_fn :: Gen Bool
test_simple_fn = chooseInteger (0, toInteger (maxBound @U32)) <&>
  (\x -> and
    [ evalFn dis_any (x :* Nil) == ()
    , evalFn call_fn0 Nil == 42
    , evalFn call_fn1 (x :* Nil) == x + x
    , evalFn call_fn2 (x :* Nil) == x + x
    , evalFn call_fn3 (x :* Nil) == x + x + x
    , evalFn call_fn4 (x :* Nil) == x + x + x + x
    ]
  ) . fromInteger

--------------------------------------------------------------------------------
-- Polymorphic
--------------------------------------------------------------------------------

poly_foo :: forall a s n.
  ( a ~ INTx s n, ValidINTx s n
  ) => PureFn (a -> a -> a)
poly_foo = $fn \x y -> x * 2 + y

test_poly_foo :: Bool
test_poly_foo = and
  [ evalFn (poly_foo @U8) (4 :* 2 :* Nil) == 10
  , evalFn (poly_foo @I32) (4 :* 2 :* Nil) == 10
  , evalFn (poly_foo @U256) (4 :* 2 :* Nil) == 10
  ]

--------------------------------------------------------------------------------
-- Pattern matching for Maybe
--------------------------------------------------------------------------------

maybe_num_fn2 :: PureFn (Maybe U8 -> Maybe U8 -> U8)
maybe_num_fn2 = $fn
  \a b -> match (a + b) \case
    Just x -> x
    Nothing -> 0

test_maybe_fn :: Bool
test_maybe_fn = and
  [ evalFn maybe_num_fn2 (Just 42 :* Just 69 :* Nil) == 111
  , evalFn maybe_num_fn2 (Just 255 :* Just 0 :* Nil) == 255
  , evalFn maybe_num_fn2 (Just 255 :* Just 1 :* Nil) == 0
  , evalFn maybe_num_fn2 (Just 128 :* Just 128 :* Nil) == 0
  ]

--------------------------------------------------------------------------------

-- | "YulDSL.Core.Fn" tests.
tests = describe "YulDSL.Core.Fn" $ do
  it "simple fn" $ property test_simple_fn
  it "test polymorphic fn" $ property test_poly_foo
  it "pattern matching with Maybe" $ property test_maybe_fn
