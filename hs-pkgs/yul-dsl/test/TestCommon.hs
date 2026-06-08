module TestCommon where
-- eth-abi
import Ethereum.ContractABI.Arbitrary ()
--
import YulDSL.Core.YulEffect


------------------------------------------------------------------------------------------------------------------------
- Pure effect for testing
------------------------------------------------------------------------------------------------------------------------

data TestEffectKind = Pure | NonPure

