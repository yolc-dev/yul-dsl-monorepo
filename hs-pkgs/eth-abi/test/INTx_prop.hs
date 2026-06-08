module INTx_prop where

import Data.Maybe
import Data.Proxy
--
import Test.Hspec
import Test.QuickCheck
--

tests = describe "INTx" $ do
  describe "Minimum and maximum bounds" True
