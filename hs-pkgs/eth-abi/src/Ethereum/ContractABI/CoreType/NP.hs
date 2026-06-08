{-# OPTIONS_GHC -Wno-orphans #-}
{-|

Copyright   : (c) 2024-2025 Miao, ZhiCheng
License     : MIT

Maintainer  : hellwolf@yolc.dev
Stability   : experimental
Portability : GHC2024

= Description

Ethereum contract ABI compatible tuples encoded as simple n-ary products 'Data.SimpleNP.NP'.

-}
module Ethereum.ContractABI.CoreType.NP
  ( module Data.SimpleNP
  ) where

-- cereal
import Data.Serialize                    qualified as S
--
import Data.SimpleNP
--
import Ethereum.ContractABI.ABITypeable  (ABITypeable (..))
import Ethereum.ContractABI.ABITypeCodec (ABITypeCodec (..))


instance ABITypeable (NP '[]) where
  type instance ABITypeDerivedOf (NP '[]) = NP '[]
  abiTypeInfo = []

instance ( ABITypeable x, ABITypeable (NP xs)
         ) => ABITypeable (NP (x : xs)) where
  type instance ABITypeDerivedOf (NP (x : xs)) = NP (x : xs)
  abiTypeInfo = abiTypeInfo @x <> abiTypeInfo @(NP xs)

instance ABITypeCodec (NP '[]) where

instance ( ABITypeable x, ABITypeCodec x, ABITypeCodec (NP xs)
         ) => ABITypeCodec (NP (x : xs)) where
