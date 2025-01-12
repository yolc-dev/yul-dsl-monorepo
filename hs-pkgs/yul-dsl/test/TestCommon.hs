module TestCommon where
-- eth-abi
import Ethereum.ContractABI.Arbitrary ()
--
import YulDSL.Core.YulCat


------------------------------------------------------------------------------------------------------------------------
-- Pure effect for testing
------------------------------------------------------------------------------------------------------------------------

data PureEffectKind = Pure

instance KnownYulCatEffect Pure where classifyYulCatEffect = PureEffect

type instance IsEffectNotPure (eff :: PureEffectKind) = False
type instance MayEffectWorld  (eff :: PureEffectKind) = False

-- | Function without side effects, hence pure.
type PureFn = Fn Pure
