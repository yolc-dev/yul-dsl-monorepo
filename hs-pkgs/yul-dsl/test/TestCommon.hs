module TestCommon where
-- eth-abi
import Ethereum.ContractABI.Arbitrary ()
--
import YulDSL.Core.YulCat             (Fn)
import YulDSL.Core.YulEffect


------------------------------------------------------------------------------------------------------------------------
-- Pure effect for testing
------------------------------------------------------------------------------------------------------------------------

data TestEffectKind = Pure | NonPure

instance KnownYulCatEffect Pure where classifyYulCatEffect = PureEffect

type instance IsEffectNotPure Pure = False
type instance MayEffectWorld  Pure = False

type instance IsEffectNotPure NonPure = True
type instance MayEffectWorld  NonPure = True

-- | Function without side effects, hence pure.
type PureFn = Fn Pure
