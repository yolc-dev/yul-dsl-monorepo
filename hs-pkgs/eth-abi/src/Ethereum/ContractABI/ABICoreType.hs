{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TemplateHaskell     #-}
{-|

Copyright   : (c) 2024-2025 Miao, ZhiCheng
License     : MIT

Maintainer  : hellwolf@yolc.dev
Stability   : experimental
Portability : GHC2024

= Description

All derived types and dependent types are mapped to the underlying core types, such that you only need to work with
contract ABI types to support the entire contract ABI specification.

-}
module Ethereum.ContractABI.ABICoreType
  ( Nat
  , ValidINTn
  -- ABI type names
  , ABITypeable(..)
  -- EVM word representations
  ) where

-- base
import Control.Exception            (assert)
import GHC.TypeLits
    ( KnownNat
    , Nat
    , type (<=)
    )
-- template-haskell
-- constraints
--
import Internal.Data.Type.Bool


{- * ABICoreType and their utilities -}



-- | A constraint that restricts what Nat values are valid for 'INTx' and 'BYTESn'.
--   Note: It is valid from 1 to 32.
type ValidINTn n = (KnownNat n, ValidINTn_ n)

-- | From ValidINTn to Int value.
-- | A helper constraint to avoid KnownNat to be super class which may cause issues when unsafeAxiom.
class ValidINTn_ n

-- | A top-level splice that declares all the valid INTx n values.
instance ValidINTn_ 32


class ABITypeable a where
  type ABITypeDerivedOf a

  abiTypeInfo :: String
  abiFromCoreType :: a -> a
  abiFromCoreType x = x
