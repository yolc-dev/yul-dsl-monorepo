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

dis_any_y :: forall a. YulO1 a => PureYulFn (a -> ())
dis_any_y _ = yulEmb ()

dis_any_fn :: forall a. YulO1 a => PureFn (a -> ())
dis_any_fn = fn' "dis_any" dis_any_y

test_trvial_fns :: Bool
test_trvial_fns = and
  [ evalFn constant_fn Nil == 42
  , evalFn dis_any_fn (I () :* Nil) == ()
  , evalFn (dis_any_fn @U32) (I 42 :* Nil) == ()
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
call_fn0 = $fn do call0 def_fn0

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
    , evalFn call_fn1 (I x :* Nil) == x
    , evalFn call_fn2 (I x :* Nil) == x + x
    , evalFn call_fn3 (I x :* Nil) == x + x + x
    , evalFn call_fn4 (I x :* Nil) == x + x + x + x
    ]
  ) . fromInteger

--------------------------------------------------------------------------------
-- NP Functions
--------------------------------------------------------------------------------

add2_y :: PureYulFn ((U256, U256) -> U256)
add2_y (is -> (a, b)) = a + b

add2NP_y :: PureYulFn (NP I [U256, U256] -> U256)
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
     and [ evalFn add2NP_fn   (I x :* I y :* Nil) == x + y
         , evalFn add2NP_fn'  (I x :* I y :* Nil) == x + y
         , evalFn add2NP_fn'' (I x :* I y :* Nil) == x + y
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
  [ evalFn (poly_foo @U8)   (I 4 :* I 2 :* Nil)   == 10
  , evalFn (poly_foo @I32)  (I 4 :* I 2 :* Nil)  == 10
  , evalFn (poly_foo @U256) (I 4 :* I 2 :* Nil) == 10
  ]

--------------------------------------------------------------------------------
-- Pattern Matching: Maybe
--------------------------------------------------------------------------------

bool_fn1 :: PureFn (BOOL -> U8 -> U8 -> U8)
bool_fn1 = $fn
  \a b c -> if a then b else c

bool_fn2 :: PureFn (BOOL -> U8 -> U8 -> U8)
bool_fn2 = $fn
  \a b c -> match a \case True -> b; False -> c

test_bool_fns :: Bool
test_bool_fns = and
  [ evalFn bool_fn1 (I true  :* I 42 :* I 69 :* Nil) == 42
  , evalFn bool_fn1 (I false :* I 42 :* I 69 :* Nil) == 69
  , evalFn bool_fn2 (I true  :* I 42 :* I 69 :* Nil) == 42
  , evalFn bool_fn2 (I false :* I 42 :* I 69 :* Nil) == 69
  ]

--------------------------------------------------------------------------------
-- Pattern Matching: Maybe
--------------------------------------------------------------------------------

maybe_num_fn1 :: PureFn (U8 -> U8)
maybe_num_fn1 = $fn
  \a -> call maybe_num_fn2 (be (Just a)) (be (Just (a + 42)))

maybe_num_fn2 :: PureFn (Maybe U8 -> Maybe U8 -> U8)
maybe_num_fn2 = $fn
  \a b -> match (a + b) \case
    Just x -> x
    Nothing -> 0

maybe_functor_fn1 :: PureFn (Maybe U8 -> Maybe U8)
maybe_functor_fn1 = $fn \a -> a <&&> (+ yulEmb @Pure 42)

maybe_functor_fn2 :: PureFn (Maybe U8 -> U8 -> Maybe U8)
maybe_functor_fn2 = $fn \a b -> (+ b) <$$> a

{- HLint ignore test_maybe_fn "Use isNothing" -}
test_maybe_fn :: Bool
test_maybe_fn = and
  [ evalFn maybe_num_fn1 (I 30 :* Nil) == 102
  , evalFn maybe_num_fn1 (I 150 :* Nil) == 0
  , evalFn maybe_num_fn2 (I (Just 42)  :* I (Just 69) :* Nil)   == 111
  , evalFn maybe_num_fn2 (I (Just 255) :* I (Just 0)  :* Nil)   == 255
  , evalFn maybe_num_fn2 (I (Just 255) :* I (Just 1)  :* Nil)   == 0
  , evalFn maybe_num_fn2 (I (Just 128) :* I (Just 128) :* Nil) == 0
  , evalFn maybe_functor_fn1 (I 30 :* Nil)  == Just 72
  , evalFn maybe_functor_fn1 (I Nothing   :* Nil) == Nothing
  , evalFn maybe_functor_fn2 (I (Just 30) :* I 40 :* Nil)  == Just 70
  , evalFn maybe_functor_fn2 (I Nothing   :* I 20 :* Nil) == Nothing
  ]

--------------------------------------------------------------------------------

test_effect_classification :: Bool
test_effect_classification = and
  [ classifyYulCatEffect @Pure  == PureEffect
  , classifyYulCatEffect @Total == PureEffect
  , withKnownNamedYulCat constant_fn (\(_ :: NamedYulCat eff a b) -> classifyYulCatEffect @eff) == PureEffect
  , classifyKnownNamedYulCat constant_fn == PureEffect
  ]

-- | "YulDSL.Core.Fn" tests.
tests = describe "YulDSL.Core.Fn" $ do
  it "trivial functions" test_trvial_fns
  it "simple functions" $ property test_simple_fns
  it "NP functions" $ property test_np_fns
  it "polymorphic function" test_poly_foo
  it "boolean objects" test_bool_fns
  it "pattern matching with Maybe" test_maybe_fn
  it "pure effects classification" test_effect_classification
