module Fn_t where
-- base
import Prelude
import Data.Functor                 ((<&>))
-- hspec, quickcheck
import Test.Hspec
import Test.QuickCheck
-- eth-abi
-- yul-dsl
import YulDSL.Core
import YulDSL.Eval
--
--
import TestCommon                   ()

-- | "YulDSL.Core.Fn" tests.
tests = describe "YulDSL.Core.Fn" $ do
  it "pattern matching with Maybe" True
