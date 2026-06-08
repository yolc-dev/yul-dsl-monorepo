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
  -- ABI type names
  , ABITypeable(..)
  , ADDR
  , U256
  , B32
  , module Data.SimpleNP
  ) where

-- base
import GHC.TypeLits
    ( Nat
    , type (<=)
    )
-- template-haskell
-- constraints
--

-- base
import Data.SimpleNP
import Data.Bits                         (shift)
import Data.Coerce                       (coerce)
import Data.Maybe                        (fromJust)
import Data.Proxy                        (Proxy (Proxy))
import GHC.TypeLits                      (type (+), type (<=), type (<=?))
-- cereal

{- * ABICoreType and their utilities -}



-- | A constraint that restricts what Nat values are valid for 'INTx' and 'BYTESn'.
--   Note: It is valid from 1 to 32.


-- | A top-level splice that declares all the valid INTx n values.


class ABITypeable a where
  type ABITypeDerivedOf a

  abiTypeInfo :: String
  abiFromCoreType :: a -> a
  abiFromCoreType x = x

data ADDR

instance ABITypeable ADDR where
  type instance ABITypeDerivedOf ADDR = ADDR
  abiTypeInfo = "a"

-- eth-abi


-- | ABI integer value types, where @s@ is for signess and @n@ is byte-size of the value.
data U256



instance ABITypeable U256 where
  type instance ABITypeDerivedOf U256 = U256
  abiTypeInfo = "i"


data B32

instance ABITypeable B32 where
  type instance ABITypeDerivedOf B32 = B32
  abiTypeInfo = "b"

-- cereal
--
--


instance ABITypeable (NP '[]) where
  type instance ABITypeDerivedOf (NP '[]) = NP '[]
  abiTypeInfo = []

instance ( ABITypeable x, ABITypeable (NP xs)
         ) => ABITypeable (NP (x : xs)) where
  type instance ABITypeDerivedOf (NP (x : xs)) = NP (x : xs)
  abiTypeInfo = abiTypeInfo @x <> abiTypeInfo @(NP xs)

