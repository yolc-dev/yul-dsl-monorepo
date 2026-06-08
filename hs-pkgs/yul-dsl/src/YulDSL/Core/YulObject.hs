{-|

Copyright   : (c) 2023-2025 Miao, ZhiCheng
License     : LGPL-3
Maintainer  : hellwolf@yolc.dev
Stability   : experimental

= Description

Yul object builder. Yul object specification can be found from [solidity
documentation](https://docs.soliditylang.org/en/latest/yul.html#specification-of-yul-object).

-}
module YulDSL.Core.YulObject
  (-- $AnyExportedYulCat
    AnyExportedYulCat (MkAnyExportedYulCat)
  ) where
-- base
import Data.List                                  (intercalate)
-- eth-abi
import Ethereum.ContractABI.CoreType.NP
--
import YulDSL.Core.YulCat
import YulDSL.Core.YulCatObj
import YulDSL.Core.YulEffect


------------------------------------------------------------------------------------------------------------------------
-- $AnyExportedYulCat

-- | Existential type wrapper for yul function that is exported.
data AnyExportedYulCat where
  MkAnyExportedYulCat :: forall k { eff :: k } xs b. YulO2 (NP xs) b
                      => NamedYulCat eff (NP xs) b -> AnyExportedYulCat
