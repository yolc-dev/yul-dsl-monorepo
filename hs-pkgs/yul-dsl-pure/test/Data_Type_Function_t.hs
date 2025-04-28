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
  , fromBoolKind @(LiftFunction (Int -> Float -> Bool) Identity Identity One ==
                    (Identity Int %1-> Identity Float %1-> Identity Bool))
  ]

test_tf_uncurry_examples = and
  [ fromBoolKind @(UncurryNP (Bool) == (NP '[] -> Bool))
  , fromBoolKind @(UncurryNP (Int -> Bool) == (NP '[Int] -> Bool))
  , fromBoolKind @(UncurryNP (Int -> Float -> Bool) == (NP '[Int, Float] -> Bool))
  , fromBoolKind @(UncurryNP (Int -> Float -> String -> Bool) == (NP '[Int, Float, String] -> Bool))
  , fromBoolKind @(UncurryNP (Int %1-> Float %1-> String %1-> Bool) == (NP '[Int, Float, String] %1-> Bool))
  , fromBoolKind @(UncurryNP (Int %1-> Float -> String -> Bool) == (NP '[Int, Float, String] %1-> Bool)) -- tolerated
  ]

test_tf_ncurry_examples = and
  [ fromBoolKind @(CurryNP (NP '[]) Int == Int)
  , fromBoolKind @(CurryNP (NP '[Char]) Bool == (Char -> Bool))
  , fromBoolKind @(CurryNP (NP '[Char, Double]) Bool == (Char -> Double -> Bool))
  , fromBoolKind @(CurryNP (NP '[Char, Char, Double]) Bool == (Char -> Char -> Double -> Bool))
  ]

test_tf_uncurrying_head_examples = and
  [ fromBoolKind @(CurryNP'Head (Bool) == ())
  , fromBoolKind @(CurryNP'Head (Int -> Bool) == Int)
  , fromBoolKind @(CurryNP'Head (Int -> Float -> Bool) == Int)
  , fromBoolKind @(CurryNP'Head (Int %1-> Float %1-> Bool) == Int)
  ]

test_tf_uncurrying_tail_examples = and
  [ fromBoolKind @(CurryNP'Tail (Bool) == Bool)
  , fromBoolKind @(CurryNP'Tail (Int -> Bool) == Bool)
  , fromBoolKind @(CurryNP'Tail (Int -> Float -> Bool) == (Float -> Bool))
  , fromBoolKind @(CurryNP'Tail (Int %1-> Float %1-> Bool) == (Float %1-> Bool))
  , fromBoolKind @(CurryNP'Tail (Int -> Float %1-> Bool) == (Float %1-> Bool)) -- tolerated
  ]

tests = describe "Data.Type.Function" $ do
  it "LiftFunction examples" test_tf_lift_function_examples
  it "UncurryNP examples" test_tf_uncurry_examples
  it "CurryNP examples" test_tf_ncurry_examples
  it "UncurryNP'Head" test_tf_uncurrying_head_examples
  it "UncurryNP'Tail" test_tf_uncurrying_tail_examples
