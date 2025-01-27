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
  , zeroAddress, MAX_ADDR, maxAddr
  , constAddr, integerToMaybeAddr, addrFromU160, addrToU160
  ) where

-- base
import GHC.TypeLits                       (KnownNat, type (-), type (<=), type (^))
import Numeric                            (showHex)
-- cereal
import Data.Serialize                     qualified as S
--
import Ethereum.ContractABI.ABICoreType
import Ethereum.ContractABI.ABITypeable
import Ethereum.ContractABI.ABITypeCodec
import Ethereum.ContractABI.CoreType.INTx (U160)

newtype ADDR = ADDR Integer deriving newtype (Ord, Eq, Enum)

-- | The proverbial zero address.
zeroAddress :: ADDR
zeroAddress = ADDR 0

-- | Maximum possible value of address in Nat.
type MAX_ADDR = (2 ^ 160) - 1

-- | Maximum possible value of address.
maxAddr :: ADDR
maxAddr = ADDR (fromSNat (natSing @MAX_ADDR))

-- | Create a constant address from Nat.
constAddr :: forall (a :: Nat) -> (KnownNat a , a <= MAX_ADDR) => ADDR
constAddr a = ADDR (fromSNat (natSing @a))

integerToMaybeAddr :: Integer -> Maybe ADDR
integerToMaybeAddr a = if a >= 0 && a <= (fromSNat (natSing @MAX_ADDR)) then Just (ADDR a) else Nothing

addrFromU160 :: U160 -> ADDR
addrFromU160 x = ADDR (toInteger x)

addrToU160 :: ADDR -> U160
addrToU160 (ADDR x) = fromInteger x

instance Bounded ADDR where
  minBound = zeroAddress
  maxBound = maxAddr

instance ABITypeable ADDR where
  type instance ABITypeDerivedOf ADDR = ADDR
  abiTypeInfo = [ADDR']

instance ABITypeCodec ADDR where
  abiEncoder (ADDR x) = S.put x
  abiDecoder = fmap ADDR S.get

instance ABIWordValue ADDR where
  type instance ABIWordNBytes ADDR = 20
  fromWord = integerToMaybeAddr . wordToInteger
  toWord (ADDR a) = integerToWord a

instance Show ADDR where
  -- TODO: show ERC-55 form
  show (ADDR a) = "0x" ++ showHex a ""
