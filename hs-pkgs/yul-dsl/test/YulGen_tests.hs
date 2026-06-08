-- {-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# LANGUAGE OverloadedStrings #-}
module YulGen_tests where
-- hspec
import Test.Hspec
--
import YulDSL.Core
--
import YulDSL.CodeGens.YulGen
--
import TestCommon

tests = describe "YulDSL.YulGen tests" $ do
  describe "YulDSL function generation" $ do
    it "test_single_sput"  True
