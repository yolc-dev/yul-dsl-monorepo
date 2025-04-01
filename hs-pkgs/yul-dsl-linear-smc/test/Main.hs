import Test.Hspec
--
import Prelude
--
import LinearFn_t qualified
import YulPortNum_t qualified

main = hspec do
  LinearFn_t.tests
  YulPortNum_t.tests
