{-|

Copyright   : (c) 2024-2025 Miao, ZhiCheng
License     : MIT

Maintainer  : hellwolf@yolc.dev
Stability   : experimental
Portability : GHC2024

= Description

References:

- https://docs.soliditylang.org/en/v0.8.28/internals/layout_in_storage.html

-}
--
module Ethereum.ContractABI.ExtendedType.REF
  ( REF
  , ValidSlot
  ) where
-- base
import GHC.TypeLits
--
import Ethereum.ContractABI.ABICoreType
import Ethereum.ContractABI.CoreType.BYTESn


-- | A storage or memory reference to type @a@ at the solidity conventional "(slot, offset)".
newtype REF a = REF Integer deriving (Ord, Eq)

instance Show (REF a) where show (REF x) = show x

-- | Each slot uses 32 bytes
type ValidSlot n = (KnownNat n, n <= (2 ^ 248))

instance ABITypeable a => ABITypeable (REF a) where
  type instance ABITypeDerivedOf (REF a) = B32
