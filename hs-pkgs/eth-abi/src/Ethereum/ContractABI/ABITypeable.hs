{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DefaultSignatures   #-}

{-|

Copyright   : (c) 2024 Miao, ZhiCheng
License     : MIT

Maintainer  : hellwolf@yolc.dev
Stability   : experimental
Portability : GHC2024

= Description

'ABITypeable' is the required type class for extended types.

-}
module Ethereum.ContractABI.ABITypeable
 ( ABITypeable (..)
 ) where

-- base
import Data.Kind                        (Constraint, Type)
import Data.List                        (intercalate)
import Data.Type.Equality               (type (==))
--
import Ethereum.ContractABI.ABICoreType

-- | Type information for all core and derived contract ABI types.
class ABITypeable a where
  -- | Convert @a@ to the ABI core type it derives from.
  type ABITypeDerivedOf a

  -- | Returns a list of core types represented by this type.
  --
  -- Invariant: @abi_type_info a == abi_type_info \@(ABITypeDerivedOf a)@
  abiTypeInfo :: String
  -- ^ The default implementation must be implemented by core types.
  default abiTypeInfo :: ABITypeable (ABITypeDerivedOf a) => String
  abiTypeInfo = abiTypeInfo @(ABITypeDerivedOf a)

  -- | Convert a value from the core type to the extended type.
  abiFromCoreType :: ABITypeDerivedOf a -> a
  default abiFromCoreType :: ABITypeDerivedOf a ~ a => ABITypeDerivedOf a -> a
  abiFromCoreType = id
