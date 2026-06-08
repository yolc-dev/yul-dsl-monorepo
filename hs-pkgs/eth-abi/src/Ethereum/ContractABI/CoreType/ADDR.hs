{-|

Copyright   : (c) 2024 Miao, ZhiCheng
License     : MIT

Maintainer  : hellwolf@yolc.dev
Stability   : experimental
Portability : GHC2024

= Description

Ethereum contract ABI address type.

-}
module Ethereum.ContractABI.CoreType.ADDR
  ( ADDR
  ) where

-- base
-- cereal
--
import Ethereum.ContractABI.ABICoreType
import Ethereum.ContractABI.ABITypeable

newtype ADDR = ADDR Integer deriving newtype (Ord, Eq, Enum)

-- | The proverbial zero address.





instance ABITypeable ADDR where
  type instance ABITypeDerivedOf ADDR = ADDR
  abiTypeInfo = [ADDR']

