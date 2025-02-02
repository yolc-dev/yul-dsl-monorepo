import Test.Hspec
--
import FunctionType_test qualified
import TupleN_test qualified

main = hspec $ do
  FunctionType_test.tests
  TupleN_test.tests
