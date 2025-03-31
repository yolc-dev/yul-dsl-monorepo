import Test.Hspec

import Data_Type_Function_t qualified
import Fn_t qualified

main = hspec $ do
  Data_Type_Function_t.tests
  Fn_t.tests
