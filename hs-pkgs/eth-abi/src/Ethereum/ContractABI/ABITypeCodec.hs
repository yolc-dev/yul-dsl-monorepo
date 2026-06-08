{-# LANGUAGE DefaultSignatures #-}
module Ethereum.ContractABI.ABITypeCodec
  ( ABITypeCodec
  ) where

-- base
import Data.Functor                     ((<&>))
import GHC.TypeError                    (Assert, ErrorMessage (Text), Unsatisfiable)
-- cereal
import Data.Serialize                   qualified as S
-- bytestring
import Data.ByteString                  qualified as B
--
import Internal.Data.Type.Bool          (Not)
--
import Ethereum.ContractABI.ABITypeable (ABITypeable (..), IsABICoreType)


-- | ABI type bytstream codec
class ABITypeable a => ABITypeCodec a where
