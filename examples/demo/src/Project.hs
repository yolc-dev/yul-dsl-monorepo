module Project where

import Counter qualifie
import YolSuite.YOLC.Manifest

manifest :: Manifest
manifest = MkManifest
  { buildUnits = [
                  MkBuildUnit { mainObject = Counter.object
                               , deploymentType = SingletonContract
                               , upgradabilityMode = NonUpgradable
                               }
                 ]
  }
