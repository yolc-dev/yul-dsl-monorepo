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


test_coerce_uint256_unit_prod :: forall a. a ~ U256 => a -> Bool
test_coerce_uint256_unit_prod a = toInteger a == toInteger b
  where (b, ()) = evalYulCat (YulCoerceType @Pure @a @(a, ())) a

test_coerce_two_vals_unit_hlist :: forall p q. (p ~ I128, q ~ BOOL) => p -> q -> Bool
test_coerce_two_vals_unit_hlist a b = a == a' && b == b' &&
                                      a == a'' && b == b''
  where (a', b') = evalYulCat (YulExtendType @Pure @(NP [p, q]) @(p, q)) (a :* b :* Nil)
        (a'' :* b'' :* Nil) = evalYulCat (YulReduceType @Pure @(p, q) @(NP [p, q])) (a, b)
--
test_coerce_commutative :: forall p q r. (p ~ ADDR, q ~ U160, r ~ BOOL) => p -> q -> r -> Bool
test_coerce_commutative a b c = a == a' && b == b' && c == c' &&
                                a == a'' && b == b'' && c == c''
  where ((a',b'),c') = evalYulCat (YulCoerceType @Pure @(p, (q, r)) @((p, q), r)) (a, (b, c))
        (a'',(b'',c'')) = evalYulCat (YulCoerceType @Pure @((p, q), r) @(p, (q, r))) ((a, b), c)

-- test_num_add :: U256 -> U256 -> Expectation
-- test_num_add a b = if a' + b' <= toInteger (maxBound @U256) then a + b == c `shouldBe` True
--                    else evaluate c `shouldThrow` (errorCall "Maybe.fromJust: Nothing")
--   where a' = toInteger a
--         b' = toInteger b
--         c = evalYulCat YulNumAdd (a, b)

tests = describe "YulDSL.Eval tests" $ do
  describe "YulCoerce" $ do
    it "U256 =~= (U256,())" $ property test_coerce_uint256_unit_prod
    it "p :* q :* () =~= (p, q)" $ property test_coerce_two_vals_unit_hlist
    it "(p, (q, r)) =~= ((p, q), r)" $ property test_coerce_commutative
  -- describe "YulNum" $ do
  --   it "YulNumAdd" $ property test_num_add
