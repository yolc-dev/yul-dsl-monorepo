module TestCommon where
-- eth-abi
import Ethereum.ContractABI.Arbitrary ()
--
import YulDSL.Core.YulEffect


------------------------------------------------------------------------------------------------------------------------
-- Pure effect for testing
------------------------------------------------------------------------------------------------------------------------

data TestEffectKind = Pure | NonPure

type instance IsEffectNonPure Pure = False
type instance MayAffectWorld  Pure = False

type instance IsEffectNonPure NonPure = True
type instance MayAffectWorld  NonPure = True
