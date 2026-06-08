module Project where

import Counter qualified
import YolSuite.YOLC.Manifest

x =x

manifest :: Manifest
manifest = MkManifest
  { buildUnits = [
                  MkBuildUnit { mainObject = x
                               , deploymentType = SingletonContract
                               , upgradabilityMode = NonUpgradable
                               }
                 ]
  }
