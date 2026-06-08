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

import Ethereum.ContractABI.ABICoreType

data ADDR

instance ABITypeable ADDR where
  type instance ABITypeDerivedOf ADDR = ADDR
  abiTypeInfo = "a"

