{-# LANGUAGE LinearTypes #-}
module Data_Type_Function_t where
import Prelude
-- base
import Data.Functor.Identity (Identity)
import Data.Type.Equality    (type (==))
-- hspec
import Test.Hspec
--
import Data.SimpleNP
import Data.Type.Function
import TestCommon


test_tf_lift_function_examples = and
  [ fromBoolKind @(LiftFunction Bool Identity Identity Many ==
                   Identity Bool)
  , fromBoolKind @(LiftFunction (Int -> Bool) Identity Identity Many ==
                   (Identity Int -> Identity Bool))
  , fromBoolKind @(LiftFunction (Int -> Float -> Bool) Identity Identity Many ==
                    (Identity Int -> Identity Float -> Identity Bool))
  ]

test_tf_uncurry_examples = and
  [ fromBoolKind @(UncurryNP I (Bool) == (NP I '[] -> Bool))
  , fromBoolKind @(UncurryNP I (Int -> Bool) == (NP I '[Int] -> Bool))
  , fromBoolKind @(UncurryNP I (Int -> Float -> Bool) == (NP I '[Int, Float] -> Bool))
  , fromBoolKind @(UncurryNP I (Int -> Float -> String -> Bool) == (NP I '[Int, Float, String] -> Bool))
  ]

test_tf_curry_examples = and
  [ fromBoolKind @(CurryNP_I (NP I '[]) Int == Int)
  , fromBoolKind @(CurryNP_I (NP I '[Char]) Bool == (Char -> Bool))
  , fromBoolKind @(CurryNP_I (NP I '[Char, Double]) Bool == (Char -> Double -> Bool))
  , fromBoolKind @(CurryNP (NP I '[]) Int One == Int)
  , fromBoolKind @(CurryNP (NP I '[Char]) Bool One == (I Char %1 -> Bool))
  , fromBoolKind @(CurryNP (NP I '[Char, Double]) Bool One == (I Char %1 -> I Double %1 -> Bool))
  ]

test_tf_uncurry_head_examples = and
  [ fromBoolKind @(UncurryNP'Head (Bool) == ())
  , fromBoolKind @(UncurryNP'Head (Int -> Bool) == Int)
  , fromBoolKind @(UncurryNP'Head (Int -> Float -> Bool) == Int)
  ]

test_tf_uncurry_tail_examples = and
  [ fromBoolKind @(UncurryNP'Tail (Bool) == Bool)
  , fromBoolKind @(UncurryNP'Tail (Int -> Bool) == Bool)
  , fromBoolKind @(UncurryNP'Tail (Int -> Float -> Bool) == (Float -> Bool))
  ]

tests = describe "Data.Type.Function" $ do
  it "LiftFunction examples" test_tf_lift_function_examples
  it "UncurryNP examples" test_tf_uncurry_examples
  it "CurryNP examples" test_tf_curry_examples
  it "UncurryNP'Head" test_tf_uncurry_head_examples
  it "UncurryNP'Tail" test_tf_uncurry_tail_examples
