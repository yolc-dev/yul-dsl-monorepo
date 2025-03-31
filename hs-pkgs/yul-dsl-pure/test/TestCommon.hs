{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module TestCommon where
-- eth-abi
import Ethereum.ContractABI.Arbitrary ()

--
-- KnownBool
--

class KnownBool (s :: Bool) where fromBoolKind :: Bool
instance KnownBool True where fromBoolKind = True
instance KnownBool False where fromBoolKind = False
