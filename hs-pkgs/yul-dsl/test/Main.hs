import Test.Hspec

import Eval_prop qualified
import YulGen_tests qualified

main = hspec $ do
  Eval_prop.tests
  YulGen_tests.tests
