{-|

Copyright   : (c) 2024 Miao, ZhiCheng
License     : MIT

Maintainer  : hellwolf@yolc.dev
Stability   : experimental
Portability : GHC2024

= Description

Ethereum contract ABI boolean type.

-}
module Ethereum.ContractABI.CoreType.BOOL
  ( module Internal.Data.Type.Bool
  , BOOL (BOOL), true, false
  ) where

-- cereal
--
import Internal.Data.Type.Bool
--
import Ethereum.ContractABI.ABICoreType
import Ethereum.ContractABI.ABITypeable


-- | ABI boolean value type.
newtype BOOL = BOOL Bool deriving newtype (Eq)

-- | True value for 'BOOL'.
true :: BOOL
true = BOOL True

-- | False value for 'BOOL'.
false :: BOOL
false = BOOL False

instance ABITypeable BOOL where
  type instance ABITypeDerivedOf BOOL = BOOL
  abiTypeInfo = "b"

instance Bounded BOOL where
  minBound = false
  maxBound = true

instance Show BOOL where
  show (BOOL True)  = "true"
  show (BOOL False) = "false"
