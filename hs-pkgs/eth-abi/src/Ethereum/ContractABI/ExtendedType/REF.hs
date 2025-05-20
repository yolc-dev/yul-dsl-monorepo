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
  , ValidSlot, constRef, keyRef
  ) where
-- base
import GHC.TypeLits                         (KnownNat (natSing), fromSNat, type (<=), type (^))
--
import Ethereum.ContractABI.ABITypeable     (ABITypeable (..), abiTypeCanonName)
import Ethereum.ContractABI.ABITypeCodec    (ABITypeCodec (..))
import Ethereum.ContractABI.CoreType.BYTESn


-- | A storage or memory reference to type @a@ at the solidity conventional "(slot, offset)".
newtype REF a = REF Integer deriving (Ord, Eq)

-- | Each slot uses 32 bytes
type ValidSlot n = (KnownNat n, n <= (2 ^ 248))

-- | Create a reference at a slot.
constRef :: forall a. forall slot -> ValidSlot slot => REF a
constRef slot = REF (fromSNat (natSing @slot))

-- | Create a reference at a string key (to be keccak256).
keyRef :: forall a. String -> REF a
keyRef = REF . bytesnToInteger . stringKeccak256

--
-- instances
--

instance ABITypeable a => Show (REF a) where
  show (REF x) = show x <> " /* REF@" <> abiTypeCanonName @a <> " */"

instance ABITypeable a => ABITypeable (REF a) where
  type instance ABITypeDerivedOf (REF a) = B32
  abiDefault = REF 0
  abiToCoreType (REF n) = BYTESn n
  abiFromCoreType (BYTESn n) = REF n

instance ABITypeable a => ABITypeCodec (REF a)
