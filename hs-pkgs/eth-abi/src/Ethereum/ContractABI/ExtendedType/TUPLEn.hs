{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE DeriveAnyClass  #-}
{-# LANGUAGE TemplateHaskell #-}
{-|

Copyright   : (c) 2024-2025 Miao, ZhiCheng
License     : MIT

Maintainer  : hellwolf@yolc.dev
Stability   : experimental
Portability : GHC2024

= Description

Ethereum contract ABI compatible tuples encoded as n-tuples.

-}
module Ethereum.ContractABI.ExtendedType.TUPLEn
  ( module Data.TupleN
  ) where
-- base
import Control.Monad                     (replicateM)
import Data.TupleN
--
import Ethereum.ContractABI.ABICoreType

import Ethereum.ContractABI.CoreType.NP  (NP (..))

-- ^ ABI typeable unit.
instance ABITypeable () where
  type instance ABITypeDerivedOf () = NP '[]

-- ^ ABI typeable for solo tuple.
instance ABITypeable a => ABITypeable (Solo a) where
  type instance ABITypeDerivedOf (Solo a) = NP '[a]

-- | ABI typeable tuple.
instance (ABITypeable a1, ABITypeable a2) => ABITypeable (a1, a2) where
  type instance ABITypeDerivedOf (a1, a2) = NP '[a1, a2]

