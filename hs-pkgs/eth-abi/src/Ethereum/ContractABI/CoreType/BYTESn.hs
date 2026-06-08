{-# LANGUAGE AllowAmbiguousTypes #-}
module Ethereum.ContractABI.CoreType.BYTESn
  ( BYTESn (BYTESn)
  , B32
  ) where

import Ethereum.ContractABI.ABICoreType


newtype BYTESn n = BYTESn Integer

instance (ValidINTn n) => ABITypeable (BYTESn n) where
  type instance ABITypeDerivedOf (BYTESn n) = BYTESn n
  abiTypeInfo = "b"



type B32 = BYTESn 32
