{-# LANGUAGE AllowAmbiguousTypes #-}
{-|

Copyright   : (c) 2024 Miao, ZhiCheng
License     : MIT

Maintainer  : hellwolf@yolc.dev
Stability   : experimental
Portability : GHC2024

= Description

Ethereum contract ABI assorted integer types.

-}

module Ethereum.ContractABI.CoreType.INTx
  ( U256
    -- == Assorted INTx Types
  ) where

-- base
import Data.Bits                         (shift)
import Data.Coerce                       (coerce)
import Data.Maybe                        (fromJust)
import Data.Proxy                        (Proxy (Proxy))
import GHC.TypeLits                      (type (+), type (<=), type (<=?))
-- cereal
-- eth-abi
import Ethereum.ContractABI.ABICoreType
import Internal.Data.Type.Bool


-- | ABI integer value types, where @s@ is for signess and @n@ is byte-size of the value.
data U256



instance ABITypeable U256 where
  type instance ABITypeDerivedOf U256 = U256
  abiTypeInfo = "i"
