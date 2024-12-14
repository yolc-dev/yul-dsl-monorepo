{-# LANGUAGE DefaultSignatures #-}
module Ethereum.ContractABI.ABITypeCodec
  ( ABITypeCodec (abiEncoder, abiDecoder)
  , abiEncode, abiDecode
  ) where

-- base
import           Data.Functor                     ((<&>))
import           GHC.TypeError                    (Assert, ErrorMessage (Text), TypeError)
-- cereal
import qualified Data.Serialize                   as S
-- bytestring
import qualified Data.ByteString                  as B
--
import           Internal.Data.Type.Bool          (Not)
--
import           Ethereum.ContractABI.ABITypeable (ABITypeable (..), IsABICoreType)


-- | ABI type bytstream codec
class ABITypeable a => ABITypeCodec a where
  abiDecoder :: forall. S.Get a
  default abiDecoder :: forall. ( Assert (Not (IsABICoreType a))
                                  (TypeError (Text "abiDecoder must be defined for a core type"))
                                , ABITypeCodec (ABITypeDerivedOf a)) => S.Get a
  abiDecoder = abiDecoder <&> abiFromCoreType

  abiEncoder :: forall. S.Putter a
  default abiEncoder :: forall. ( Assert (Not (IsABICoreType a))
                                  (TypeError (Text "abiEncoder must be define for a core type"))
                                , ABITypeCodec (ABITypeDerivedOf a)) => S.Putter a
  abiEncoder = abiEncoder . abiToCoreType

  abiEncode :: forall. a -> B.ByteString
  abiEncode = S.runPut . abiEncoder

  abiDecode :: forall. B.ByteString -> Maybe a
  abiDecode = either (const Nothing) Just . S.runGet abiDecoder