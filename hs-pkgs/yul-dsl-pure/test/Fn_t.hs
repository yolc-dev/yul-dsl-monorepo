module Fn_t where
-- base
import Prelude
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
import YulDSL.Haskell.LibPure hiding ((==))
--
import TestCommon                   ()


--------------------------------------------------------------------------------
-- Trivial Functions
--------------------------------------------------------------------------------

constant_fn :: PureFn U256
constant_fn = $fn $ yulEmb 42

dis_any_y :: forall a. YulO1 a => PureY (a -> ())
dis_any_y _ = yulEmb ()

dis_any_fn :: forall a. YulO1 a => PureFn (a -> ())
dis_any_fn = fn' "dis_any" dis_any_y

test_trvial_fns :: Bool
test_trvial_fns = and
  [ evalFn constant_fn Nil == 42
  , evalFn dis_any_fn (() :* Nil) == ()
  , evalFn (dis_any_fn @U32) (42 :* Nil) == ()
  ]

--------------------------------------------------------------------------------
-- Simple Fn
--------------------------------------------------------------------------------

def_fn0 :: PureFn (U256)
def_fn0 = $fn 42

def_fn1 :: PureFn (U256 -> U256)
def_fn1 = $fn id

def_fn2 :: PureFn (U256 -> U256 -> U256)
def_fn2 = $fn \a b -> a + b

def_fn3 :: PureFn (U256 -> U256 -> U256 -> U256)
def_fn3 = $fn \a b c -> a + b + c

def_fn4 :: PureFn (U256 -> U256 -> U256 -> U256 -> U256)
def_fn4 = $fn \a b c d -> f a b + f c d
  where f a b = a + b

call_fn0 :: PureFn (U256)
call_fn0 = $fn
  do def_fn0 <$*> ()

call_fn0' :: PureFn (U256)
call_fn0' = $fn
  do call0 def_fn0

call_fn1 :: PureFn (U256 -> U256)
call_fn1 = $fn
  \a -> call def_fn1 a

call_fn2 :: PureFn (U256 -> U256)
call_fn2 = $fn
  \a -> call def_fn2 a a

call_fn3 :: PureFn (U256 -> U256)
call_fn3 = $fn
  \a -> call def_fn3 a a a

call_fn4 :: PureFn (U256 -> U256)
call_fn4 = $fn
  \a -> call def_fn4 a a a a

test_simple_fns :: Gen Bool
test_simple_fns = chooseInteger (0, toInteger (maxBound @U32)) <&>
  (\x -> and
    [ evalFn call_fn0 Nil        == 42
    , evalFn call_fn1 (x :* Nil) == x
    , evalFn call_fn2 (x :* Nil) == x + x
    , evalFn call_fn3 (x :* Nil) == x + x + x
    , evalFn call_fn4 (x :* Nil) == x + x + x + x
    ]
  ) . fromInteger

--------------------------------------------------------------------------------
-- NP Functions
--------------------------------------------------------------------------------

add2_y :: PureY ((U256, U256) -> U256)
add2_y (is -> (a, b)) = a + b

add2NP_y :: PureY (NP [U256, U256] -> U256)
add2NP_y (is -> (a :* b :* Nil)) = add2_y (be (a, b))

add2NP_fn :: PureFn (U256 -> U256 -> U256)
add2NP_fn = $fn \a b -> add2NP_y (be (a, b) >.> YulReduceType)

add2NP_fn' :: PureFn (U256 -> U256 -> U256)
add2NP_fn' = $fn \a b -> add2NP_y (a `yulCons` b `yulCons` yulNil)

add2NP_fn'' :: PureFn (U256 -> U256 -> U256)
add2NP_fn'' = $fn \a b -> add2NP_y (couldBe (a :* b :* Nil))

test_np_fns :: Gen Bool
test_np_fns =
  (\x y ->
     and [ evalFn add2NP_fn (x :* y :* Nil) == x + y
         , evalFn add2NP_fn' (x :* y :* Nil) == x + y
         , evalFn add2NP_fn'' (x :* y :* Nil) == x + y
         ]
  )
  <$> (chooseInteger (0, toInteger (maxBound @U32)) <&> fromInteger)
  <*> (chooseInteger (0, toInteger (maxBound @U32)) <&> fromInteger)

--------------------------------------------------------------------------------
-- Polymorphic Function
--------------------------------------------------------------------------------

poly_foo :: forall a s n.
  ( a ~ INTx s n, ValidINTx s n
  ) => PureFn (a -> a -> a)
poly_foo = $fn \x y -> x * 2 + y

test_poly_foo :: Bool
test_poly_foo = and
  [ evalFn (poly_foo @U8) (4 :* 2 :* Nil)   == 10
  , evalFn (poly_foo @I32) (4 :* 2 :* Nil)  == 10
  , evalFn (poly_foo @U256) (4 :* 2 :* Nil) == 10
  ]

--------------------------------------------------------------------------------
-- Pattern Matching: Maybe
--------------------------------------------------------------------------------

maybe_num_fn2 :: PureFn (Maybe U8 -> Maybe U8 -> U8)
maybe_num_fn2 = $fn
  \a b -> match (a + b) \case
    Just x -> x
    Nothing -> 0

maybe_num_fn1 :: PureFn (U8 -> U8)
maybe_num_fn1 = $fn
  \a -> call maybe_num_fn2 (be (Just a)) (be (Just (a + 42)))

test_maybe_fn :: Bool
test_maybe_fn = and
  [ evalFn maybe_num_fn2 (Just 42 :* Just 69 :* Nil)   == 111
  , evalFn maybe_num_fn2 (Just 255 :* Just 0 :* Nil)   == 255
  , evalFn maybe_num_fn2 (Just 255 :* Just 1 :* Nil)   == 0
  , evalFn maybe_num_fn2 (Just 128 :* Just 128 :* Nil) == 0
  , evalFn maybe_num_fn1 (30 :* Nil) == 102
  , evalFn maybe_num_fn1 (150 :* Nil) == 0
  ]

--------------------------------------------------------------------------------

-- | "YulDSL.Core.Fn" tests.
tests = describe "YulDSL.Core.Fn" $ do
  it "trivial functions" test_trvial_fns
  it "simple functions" $ property test_simple_fns
  it "NP functions" $ property test_np_fns
  it "polymorphic function" test_poly_foo
  it "pattern matching with Maybe" test_maybe_fn
