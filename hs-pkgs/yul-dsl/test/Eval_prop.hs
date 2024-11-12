module Eval_prop (tests) where

-- hspec, quickcheck
import           Test.Hspec
import           Test.QuickCheck
-- yul-dsl
import           YulDSL.Core
import           YulDSL.Eval
--
import           TestCommon      ()

test_coerce_uint256_unit_prod :: forall a. a ~ U256 => a -> Bool
test_coerce_uint256_unit_prod a = toInteger a == toInteger b
  where (_, (b, ())) = evalYulDSL initEvalState (YulCoerce @a @(a, ())) a

-- test_coerce_two_vals_unit_hlist :: forall p q. (p ~ INT128, q ~ BOOL) => p -> q -> Bool
-- test_coerce_two_vals_unit_hlist a b = a == a' && b == b' &&
--                                       a == a'' && b == b''
--   where (_, (a', b')) = evalYulDSL initEvalState (YulCoerce @(p :* q :* ()) @(p, q)) (a :* b :* ())
--         (_, a'' :* b'' :* ()) = evalYulDSL initEvalState (YulCoerce @(p, q) @(p :* q :* ())) (a, b)
--
test_coerce_commutative :: forall p q r. (p ~ ADDR, q ~ U32, r ~ BOOL) => p -> q -> r -> Bool
test_coerce_commutative a b c = a == a' && b == b' && c == c' &&
                                a == a'' && b == b'' && c == c''
  where (_, ((a',b'),c')) = evalYulDSL initEvalState (YulCoerce @(p, (q, r)) @((p, q), r)) (a, (b, c))
        (_, (a'',(b'',c''))) = evalYulDSL initEvalState (YulCoerce @((p, q), r) @(p, (q, r))) ((a, b), c)

test_num_add :: U256 -> U256 -> Bool
test_num_add a b = Just (a + b) == c
  where (_, c) = evalYulDSL initEvalState YulNumAdd (Just a, Just b)

tests = describe "YulDSL.Eval tests" $ do
  describe "YulCoerce" $ do
    it "U256 =~= (U256,())" $ property test_coerce_uint256_unit_prod
    -- it "p :* q :* () =~= (p, q)" $ property test_coerce_two_vals_unit_hlist
    it "(p, (q, r)) =~= ((p, q), r)" $ property test_coerce_commutative
  it "YulNumAdd" $ property test_num_add
