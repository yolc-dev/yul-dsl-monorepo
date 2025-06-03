import Test.Hspec
--
import ABITypeCodec_golden qualified
import INTx_prop qualified

main = hspec $ do
  INTx_prop.tests
  ABITypeCodec_golden.tests
