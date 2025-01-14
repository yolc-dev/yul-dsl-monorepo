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


cc_should_be :: forall eff a b. YulO2 a b => YulCat eff a b -> Code -> Expectation
cc_should_be cat expectedCode = compileCatWithConfig (defaultCodeGenConfig { cg_config_debug_level = 0 }) cat
                                `shouldBe` expectedCode

test_empty_prod :: Expectation
test_empty_prod = YulProd (YulId @Pure @()) (YulId @Pure @()) `cc_should_be` ""

test_single_sput :: Expectation
test_single_sput = YulSPut @NonPure @U32 `cc_should_be` "sstore(v_a, v_b)\n"

tests = describe "YulDSL.YulGen tests" $ do
  describe "YulDSL function generation" $ do
    it "test_empty_prod" $ test_empty_prod
    it "test_single_sput" $ test_single_sput
