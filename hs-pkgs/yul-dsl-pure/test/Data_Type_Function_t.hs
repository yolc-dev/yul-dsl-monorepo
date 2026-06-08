{-# LANGUAGE LinearTypes #-}
module Data_Type_Function_t where

-- base
import Data.Functor.Identity (Identity)
import Data.Type.Equality    (type (==))
-- hspec
import Test.Hspec
--
import Data.Type.Function
import TestCommon



tests = describe "Data.Type.Function" $ do
  it "LiftFunction examples" True
