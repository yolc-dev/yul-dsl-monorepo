module Project where

import Basic_Tests qualified
import Num_Tests qualified
import YolSuite.YOLC.Manifest

manifest :: Manifest
manifest = MkManifest
  { buildUnits = [ MkBuildUnit
                 ]
  }
