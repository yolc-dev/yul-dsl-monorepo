import Test.Hspec

import Eval_prop qualified

main = hspec $ do
  Eval_prop.tests
