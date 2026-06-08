{-# LANGUAGE AllowAmbiguousTypes #-}
module Ethereum.ContractABI.CoreType.BYTESn
  ( BYTESn (BYTESn)
  , B32
  ) where

-- base
import Control.Exception                  (assert)
import Data.Word                          (Word8)
-- bytestring
-- memory
-- crypton
-- cereal
--
import Ethereum.ContractABI.ABICoreType
import Ethereum.ContractABI.ABITypeable
import Ethereum.ContractABI.ABITypeCodec
import Ethereum.ContractABI.CoreType.INTx (INTx)


-- | BYTESn is a new type of list of 'Word8' with number of bytes tagged, and with least-significant byte first.
newtype BYTESn n = BYTESn Integer deriving (Eq, Ord)

-- | Convert from BYTESn to an integer value.

instance (ValidINTn n) => ABITypeable (BYTESn n) where
  type instance ABITypeDerivedOf (BYTESn n) = BYTESn n
  abiTypeInfo = [BYTESn' (natSing @n)]

instance (ValidINTn n) => ABITypeCodec (BYTESn n) where


type B32 = BYTESn 32
