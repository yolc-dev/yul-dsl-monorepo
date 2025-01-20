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


b32_12345678 = bytesnFromWord8s [0x12,0x34,0x56,0x78] :: B32
b32_deadbeef = bytesnFromWord8s [0xde,0xad,0xbe,0xef] :: B32

cc_should_be :: forall eff a b. YulO2 a b => YulCat eff a b -> Code -> Expectation
cc_should_be cat expectedCode = compileCat (defaultCodeGenConfig { cg_config_debug_level = 0 }) cat
                                `shouldBe` expectedCode

test_single_sput = YulSPut @NonPure @U32 `cc_should_be` "sstore(v_a, v_b)\n"

test_simple_emb = YulEmb @Pure @() (42 :: U32) `cc_should_be` "v_a := 42\n"

test_simple_comp =
  let c = YulEmb @NonPure @() b32_deadbeef `YulFork` YulEmb @NonPure @() 42 >.> YulSPut @NonPure @U32
  in c `cc_should_be` "sstore(0xdeadbeef, 42)\n"

test_empty_prod = YulProd (YulId @Pure @()) (YulId @Pure @()) `cc_should_be` ""

-- Test YulProd code generation that should order code correctly
test_prod_exr =
  let c = (YulFork
           ((YulProd
             (YulEmb @NonPure @() b32_deadbeef `YulFork` YulEmb @NonPure @() 42 >.> YulSPut @NonPure @U32)
             (YulEmb @NonPure @() b32_12345678))
            >.> YulExr)
           (YulEmb @NonPure @((),()) 69))
          >.> YulSPut @NonPure @U32
  in c `cc_should_be` "sstore(0x12345678, 69)\n"

tests = describe "YulDSL.YulGen tests" $ do
  describe "YulDSL function generation" $ do
    it "test_single_sput"  test_single_sput
    it "test_simple_emb"   test_simple_emb
    it "test_simple_comp"  test_simple_comp
    it "test_empty_prod"   test_empty_prod
    -- it "test_prod_exr"    $ test_prod_exr
