module YolSuite.YOLC.Manifest where

data DeploymentType = SingletonContract
                    | FactoryContract
                    | SharedLibrary
                    deriving Show

data Upgradability = NonUpgradable
                   | SingletonUpgradability
                   | BeaconUpgradability
                   deriving Show

data BuildUnit = MkBuildUnit  deriving Show

{- HLint ignore Manifest "Use newtype instead of data" -}
data Manifest = MkManifest { buildUnits      :: [BuildUnit]
                           -- , solidityVersion :: String
                           -- , evmVersion      :: String
                           } deriving Show
