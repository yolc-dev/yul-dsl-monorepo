{-# OPTIONS_GHC -Wno-type-defaults #-}
module TupleN_test where

-- base
import Data.Type.Equality (type (==))
-- hspec
import Test.Hspec
--
import Data.SimpleNP      (NP (..))
import Data.TupleN        (NPtoTupleN, Solo (MkSolo), TupleNtoNP, fromNPtoTupleN, fromTupleNtoNP)
import KnownBool


test_tf_tuple_to_np = and
  [ fromBoolKind @(TupleNtoNP () == NP '[])
  , fromBoolKind @(TupleNtoNP (Solo Int) == NP '[Int])
  , fromBoolKind @(TupleNtoNP (Int, Float) == NP '[Int, Float])
  ]

test_tf_np_to_tuple = and
  [ fromBoolKind @(NPtoTupleN (NP '[]) == ())
  , fromBoolKind @(NPtoTupleN (NP '[Int]) == Solo Int)
  , fromBoolKind @(NPtoTupleN (NP '[Int, Float]) == (Int, Float))
  , fromBoolKind @(NPtoTupleN (NP '[Int, Float, Double]) == (Int, Float, Double))
  ]

test_from_tuple_to_np = and
  [ fromTupleNtoNP () == Nil
  , fromTupleNtoNP (MkSolo "hi") == "hi" :* Nil
  , fromTupleNtoNP (1, 2) == 1 :* 2 :* Nil
  , fromTupleNtoNP (1, 2) /= 2 :* 1 :* Nil
  , fromTupleNtoNP (1, 2, ("hello" :* Nil)) == 1 :* 2 :* ("hello" :* Nil) :* Nil
  , fromTupleNtoNP (1, 2, 3) /= 3 :* 2 :* 1 :* Nil
  ]

test_from_np_to_tuple = and
  [ fromNPtoTupleN Nil == ()
  , fromNPtoTupleN ("nihao" :* Nil) == (MkSolo "nihao")
  , fromNPtoTupleN (1 :* 2 :* Nil) == (1, 2)
  , fromNPtoTupleN (1 :* 2 :* Nil) /= (2, 1)
  , fromNPtoTupleN (1 :* 2 :* ("konijiwa" :* Nil) :* Nil) == (1, 2, "konijiwa" :* Nil)
  , fromNPtoTupleN (1 :* 2 :* ("konijiwa" :* Nil) :* Nil) /= (1, 2, "nani" :* Nil)
  ]

tests = describe "Data.TupleN" $ do
  it "TupleNtoNP examples" test_tf_tuple_to_np
  it "NPtoTupleN examples" test_tf_np_to_tuple
  it "fromTupleNtoNP examples" test_from_tuple_to_np
  it "fromNPtoTupleN examples" test_from_np_to_tuple
