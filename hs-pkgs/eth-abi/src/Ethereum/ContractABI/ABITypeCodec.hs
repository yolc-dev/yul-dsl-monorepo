{-# LANGUAGE DefaultSignatures #-}
module Ethereum.ContractABI.ABITypeCodec
  ( ABITypeCodec
  ) where

import Ethereum.ContractABI.ABITypeable (ABITypeable (..))


-- | ABI type bytstream codec
class ABITypeable a => ABITypeCodec a where
