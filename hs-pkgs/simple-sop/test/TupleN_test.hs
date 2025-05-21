{-# OPTIONS_GHC -Wno-type-defaults -Wno-orphans #-}
module TupleN_test where

-- base
import Data.Type.Equality (type (==))
-- hspec
import Test.Hspec
--
import Data.SimpleNP      (I (I), NP (..))
import Data.TupleN        (NPtoTupleN, Solo (MkSolo), TupleNtoNP, fromNPtoTupleN, fromTupleNtoNP)
import KnownBool

default (Int)

deriving instance Eq a => Eq (I a)

test_tf_tuple_to_np = and
  [ fromBoolKind @(TupleNtoNP I () == NP I '[])
  , fromBoolKind @(TupleNtoNP I (Solo (I Int)) == NP I '[Int])
  , fromBoolKind @(TupleNtoNP I (I Int, I Float) == NP I '[Int, Float])
  ]

test_tf_np_to_tuple = and
  [ -- fromBoolKind @(NPtoTupleN (NP I '[]) == ())
    fromBoolKind @(NPtoTupleN I (NP I '[Int]) == Solo (I Int))
  , fromBoolKind @(NPtoTupleN I (NP I '[Int, Float]) == (I Int, I Float))
  , fromBoolKind @(NPtoTupleN I (NP I '[Int, Float, Double]) == (I Int, I Float, I Double))
  ]

test_from_tuple_to_np = and
  [ -- fromTupleNtoNP () == Nil
    fromTupleNtoNP (MkSolo (I "hi")) == I "hi" :* Nil
  , fromTupleNtoNP (I 1, I 2) == I 1 :* I 2 :* Nil
  , fromTupleNtoNP (I 1, I 2) /= I 2 :* I 1 :* Nil
  , fromTupleNtoNP (I 1, I 2, I (I "hello" :* Nil)) == I 1 :* I 2 :* I (I "hello" :* Nil) :* Nil
  , fromTupleNtoNP (I 1, I 2, I 3) /= I 3 :* I 2 :* I 1 :* Nil
  ]

test_from_np_to_tuple = and
  [ -- fromNPtoTupleN Nil == ()
    fromNPtoTupleN ("nihao" :* Nil) == (MkSolo "nihao")
  , fromNPtoTupleN (I 1 :* I 2 :* Nil) == (I 1, I 2)
  , fromNPtoTupleN (I 1 :* I 2 :* Nil) /= (I 2, I 1)
  , fromNPtoTupleN (I 1 :* I 2 :* I (I "konijiwa" :* Nil) :* Nil) == (I 1, I 2, I (I "konijiwa" :* Nil))
  , fromNPtoTupleN (I 1 :* I 2 :* I (I "konijiwa" :* Nil) :* Nil) /= (I 1, I 2, I (I "nani" :* Nil))
  ]

tests = describe "Data.TupleN" $ do
  it "TupleNtoNP examples" test_tf_tuple_to_np
  it "NPtoTupleN examples" test_tf_np_to_tuple
  it "fromTupleNtoNP examples" test_from_tuple_to_np
  it "fromNPtoTupleN examples" test_from_np_to_tuple
