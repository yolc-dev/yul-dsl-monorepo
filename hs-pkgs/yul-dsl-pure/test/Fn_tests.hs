module Fn_tests where
-- base
import Data.Functor                 ((<&>))
-- hspec, quickcheck
import Test.Hspec
import Test.QuickCheck
-- eth-abi
import Data.TupleN                  (Solo (MkSolo))
import Ethereum.ContractABI
-- yul-dsl
import YulDSL.Core
import YulDSL.Eval
-- yul-dsl-pure
import YulDSL.Haskell.Effects.Pure
import YulDSL.Haskell.YulUtils.Pure
--
import TestCommon                   ()


--------------------------------------------------------------------------------
-- Trivial functions
--------------------------------------------------------------------------------

dis_any :: forall a. YulO1 a => PureFn (a -> ())
dis_any = fn "dis_any" \_ -> YulEmb ()

--------------------------------------------------------------------------------
-- Simple functions
--------------------------------------------------------------------------------

uncurry_fn0 :: PureFn (U256)
uncurry_fn0 = fn "uncurry_fn0" 42

uncurry_fn1 :: ValidINTx s n => PureFn (INTx s n -> INTx s n)
uncurry_fn1 =
  fn "uncurry_fn1" \a -> a + a

uncurry_fn2 :: PureFn (U256 -> U256 -> U256)
uncurry_fn2 = fn $locId
  \a b -> a + b

uncurry_fn3 :: PureFn (U256 -> U256 -> U256 -> U256)
uncurry_fn3 = fn $locId
  \a b c -> a + b + c

uncurry_fn4 :: PureFn (U256 -> U256 -> U256 -> U256 -> U256)
uncurry_fn4 = fn $locId
  \a b c d -> f a b + f c d
  where f a b = a + b

call_fn0 :: PureFn (U256)
call_fn0 = fn $locId
  do callFn uncurry_fn0

call_fn1 :: PureFn (U256 -> U256)
call_fn1 = fn $locId
  \a -> callFn uncurry_fn1 a

call_fn2 :: PureFn (U256 -> U256)
call_fn2 = fn $locId
  \a -> callFn uncurry_fn2 a a

call_fn3 :: PureFn (U256 -> U256)
call_fn3 = fn $locId
  \a -> callFn uncurry_fn3 a a a

call_fn4 :: PureFn (U256 -> U256)
call_fn4 = fn $locId
  \a -> callFn uncurry_fn4 a a a a

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

poly_foo :: forall a s n. (a ~ INTx s n, ValidINTx s n) => PureFn (a -> a -> a)
poly_foo = fn $locId \x y -> x * 2 + y

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
maybe_num_fn2 = fn $locId
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
