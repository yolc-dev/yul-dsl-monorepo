import Test.Hspec
--
import Prelude
--
import LinearFn_tests qualified
import YulPortNum_tests qualified

main = hspec do
  LinearFn_tests.tests
  YulPortNum_tests.tests
