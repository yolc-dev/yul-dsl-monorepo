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
  ( INTx, ValidINTx, U256
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
import Ethereum.ContractABI.ABITypeable
import Internal.Data.Type.Bool


-- | ABI integer value types, where @s@ is for signess and @n@ is byte-size of the value.
newtype INTx (s :: Bool) (n :: Nat) = INT Integer
  deriving newtype (Eq, Ord, Enum)

-- | A constraint alias for 'KnownBool' and 'ValidINTn'.
type ValidINTx s n = (KnownBool s, ValidINTn n)



instance forall s n. ValidINTx s n => ABITypeable (INTx s n) where
  type instance ABITypeDerivedOf (INTx s n) = INTx s n
  abiTypeInfo = "i"


type U256 = INTx False 32
