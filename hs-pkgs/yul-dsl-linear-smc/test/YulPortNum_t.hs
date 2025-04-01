module YulPortNum_t where
-- base
import Prelude         (fromInteger, pure, (<$>), (==), (>>=))
-- hspec, quickcheck
import Test.Hspec
import Test.QuickCheck
-- yul-dsl
import YulDSL.Core
import YulDSL.Eval
--
import Prelude.YulDSL  hiding (fromInteger, (==))


num_add :: StaticFn (I256 -> I256 -> I256)
num_add = $lfn $ uncurry'lvv
  \x1 x2 -> x1 + x2

num_sub :: StaticFn (I256 -> I256 -> I256)
num_sub = $lfn $ uncurry'lvv
  \x1 x2 -> x1 - x2

num_mul :: StaticFn (I256 -> I256 -> I256)
num_mul = $lfn $ uncurry'lvv
  \x1 x2 -> x1 * x2

test_2op :: Gen Bool
test_2op = do
  x <- fromInteger <$> chooseInteger (0, toInteger (maxBound @U32))
  y <- fromInteger <$> chooseInteger (0, toInteger (maxBound @U32))
  pure $ and
    [ evalFn num_add (x :* y :* Nil) == x + y
    , evalFn num_sub (x :* y :* Nil) == x - y
    , evalFn num_mul (x :* y :* Nil) == x * y
    ]

tests = describe "YulPort Num Class" $ do
  it "Num binary ops" $ property test_2op
