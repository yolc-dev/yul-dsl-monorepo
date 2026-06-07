module LinearFn_t where
-- hspec
import Test.Hspec
-- (lvm)
import Control.LinearlyVersionedMonad qualified as LVM
--
import Prelude                        ()
import Prelude.YulDSL



tests = describe "LinearFn Tests" $ do
  describe "lfn: linear function builder" $ do
    it "simple fn definitions" True
