{-# OPTIONS_GHC -Wno-orphans #-}
module Ethereum.ContractABI.Arbitrary where
-- base
import Data.Functor         ((<&>))
-- quickcheck
import Test.QuickCheck
-- eth-abi
import Ethereum.ContractABI


instance Arbitrary ADDR where
  arbitrary = chooseBoundedIntegral (minBound @U160, maxBound @U160)
              <&> addrFromU160

deriving newtype instance Arbitrary BOOL

instance ValidINTx s n => Arbitrary (INTx s n) where
  arbitrary = chooseBoundedIntegral (minBound, maxBound)
