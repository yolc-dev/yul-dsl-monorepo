module Project where

import ERC20 qualified
import Counter qualified
import YolSuite.YOLC.Manifest

manifest :: Manifest
manifest = MkManifest
  { buildUnits = [ MkBuildUnit { mainObject = ERC20.object
                               , deploymentType = SingletonContract
                               , upgradabilityMode = NonUpgradable
                               }
                  ,MkBuildUnit { mainObject = Counter.object
                               , deploymentType = SingletonContract
                               , upgradabilityMode = NonUpgradable
                               }
                 ]
  }
