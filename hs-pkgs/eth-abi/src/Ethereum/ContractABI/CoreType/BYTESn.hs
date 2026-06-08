{-# LANGUAGE AllowAmbiguousTypes #-}
module Ethereum.ContractABI.CoreType.BYTESn
  ( B32
  ) where

import Ethereum.ContractABI.ABICoreType

data B32

instance ABITypeable B32 where
  type instance ABITypeDerivedOf B32 = B32
  abiTypeInfo = "b"
