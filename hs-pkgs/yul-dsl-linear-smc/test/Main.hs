import Test.Hspec
--
import Prelude
--
import YLVM_Fn_t qualified
import YulPorts_Fn_t qualified

main = hspec do
  YulPorts_Fn_t.tests
  YLVM_Fn_t.tests
