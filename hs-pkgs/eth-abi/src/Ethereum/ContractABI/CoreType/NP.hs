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


--
-- NP of any type function "f"
--

instance ABITypeable (NP f '[]) where
  type instance ABITypeDerivedOf (NP f '[]) = NP f '[]
  abiDefault = Nil
  abiTypeInfo = []

instance ( ABITypeable (f x), ABITypeable (NP f xs)
         ) => ABITypeable (NP f (x : xs)) where
  type instance ABITypeDerivedOf (NP f (x : xs)) = NP f (x : xs)
  abiDefault = abiDefault :* abiDefault
  abiTypeInfo = abiTypeInfo @(f x) <> abiTypeInfo @(NP f xs)

instance ABITypeCodec (NP f '[]) where
  abiEncoder Nil = S.put ()
  abiDecoder = S.get @() >> pure Nil

instance ( ABITypeable (f x), ABITypeCodec (f x), ABITypeCodec (NP f xs)
         ) => ABITypeCodec (NP f (x : xs)) where
  abiEncoder (x :* xs) = do
    abiEncoder x
    abiEncoder xs
  abiDecoder = do
    x <- abiDecoder
    xs <- abiDecoder
    pure (x :* xs)

--
-- Identity type for "f"
--

instance ABITypeable a => ABITypeable (I a) where
  type instance ABITypeDerivedOf (I a) = a
  abiDefault = I abiDefault
  abiTypeInfo = abiTypeInfo @a
  abiToCoreType (I x) = x
  abiFromCoreType = I

instance ABITypeCodec a => ABITypeCodec (I a) where
  abiEncoder (I a) = abiEncoder a
  abiDecoder = I <$> abiDecoder
