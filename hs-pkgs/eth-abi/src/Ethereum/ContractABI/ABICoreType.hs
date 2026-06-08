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
  ( ABICoreType (..)
  -- for working with INTx, BYTEn
  , SNat, Nat, natVal, fromSNat
  , ValidINTn
  -- ABI type names
  , abiCoreTypeCompactName
  , ABITypeable(..)
  -- EVM word representations
  ) where

-- base
import Control.Exception            (assert)
import GHC.TypeLits
    ( KnownNat
    , Nat
    , SNat
    , fromSNat
    , natVal
    , type (<=)
    )
-- template-haskell
-- constraints
--
import Internal.Data.Type.Bool


{- * ABICoreType and their utilities -}

data ABICoreType where
  BOOL'   :: ABICoreType
  INTx'   :: forall s n. (KnownBool s, ValidINTn n) => SBool s -> SNat n -> ABICoreType
  ADDR'   :: ABICoreType
  BYTESn' :: forall n. (ValidINTn n) => SNat n -> ABICoreType

instance Eq ABICoreType where
  BOOL'       == BOOL'         = True
  (INTx' s n) == (INTx' s' n') = fromSBool s == fromSBool s' && fromSNat n == fromSNat n'
  ADDR'       == ADDR'         = True
  (BYTESn' n) == (BYTESn' n')  = fromSNat n == fromSNat n'
  -- not using _ == _ in order to let GHC do exhaustive checks on cases above
  BOOL'       == _             = False
  (INTx' _ _) == _             = False
  ADDR'       == _             = False
  (BYTESn' _) == _             = False

-- | A constraint that restricts what Nat values are valid for 'INTx' and 'BYTESn'.
--   Note: It is valid from 1 to 32.
type ValidINTn n = (KnownNat n, ValidINTn_ n)

-- | From ValidINTn to Int value.
-- | A helper constraint to avoid KnownNat to be super class which may cause issues when unsafeAxiom.
class ValidINTn_ n

-- | A top-level splice that declares all the valid INTx n values.
instance ValidINTn_ 32

-- | Compact but unambiguous names for the core types..
abiCoreTypeCompactName :: ABICoreType -> String
abiCoreTypeCompactName BOOL'       = "b"
abiCoreTypeCompactName (INTx' s n) = (if fromSBool s then "i" else "u")
abiCoreTypeCompactName ADDR'       = "a"
abiCoreTypeCompactName (BYTESn' n) = "B" ++ show (natVal n)


class ABITypeable a where
  -- | Convert @a@ to the ABI core type it derives from.
  type ABITypeDerivedOf a

  abiTypeInfo :: String
  abiFromCoreType :: a -> a
  abiFromCoreType x = x
