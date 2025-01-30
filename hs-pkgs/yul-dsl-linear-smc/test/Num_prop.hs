module Num_prop where

import Test.Hspec
--
import Prelude        ()
import Prelude.YulDSL


num_add_just :: StaticFn (U256 -> U256 -> U256)
num_add_just = lfn "add2" $ uncurry'lvv
  \x1 x2 -> x1 + x2

tests = describe "Data.Num.YulDSL.Linear" $ do
  it "Num hierarchy classes" True
