module Eval_prop (tests) where

-- base
-- import           Control.Exception    (evaluate)
-- hspec, quickcheck
import Test.Hspec
import Test.QuickCheck
-- eth-abi
import Ethereum.ContractABI
-- yul-dsl
import YulDSL.Core
import YulDSL.Eval
--
import TestCommon


tests = describe "YulDSL.Eval tests" $ do
  describe "YulCoerce" $ do
    it "U256 =~= (U256,())" $ property True
  -- describe "YulNum" $ do
  --   it "YulNumAdd" $ property test_num_add
