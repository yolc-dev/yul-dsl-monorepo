{-# OPTIONS_GHC -Wno-orphans #-}
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
-- (simple-np)
import Data.TupleN
-- template-haskell
import Language.Haskell.TH               qualified as TH
--
import Ethereum.ContractABI.ABITypeable  (ABITypeable (..))
import Ethereum.ContractABI.ABITypeCodec (ABITypeCodec (..))
import Ethereum.ContractABI.CoreType.NP  (NP (..))

-- ^ ABI typeable unit.
instance ABITypeable () where
  type instance ABITypeDerivedOf () = NP '[]
  abiDefault = ()
  abiToCoreType () = Nil
  abiFromCoreType Nil = ()
instance ABITypeCodec ()

-- ^ ABI typeable for solo tuple.
instance ABITypeable a => ABITypeable (Solo a) where
  type instance ABITypeDerivedOf (Solo a) = NP '[a]
  abiDefault = MkSolo abiDefault
  abiToCoreType = fromTupleNtoNP
  abiFromCoreType = fromNPtoTupleN
instance ABITypeCodec a => ABITypeCodec (Solo a)

-- | ABI typeable tuple.
instance (ABITypeable a1, ABITypeable a2) => ABITypeable (a1, a2) where
  type instance ABITypeDerivedOf (a1, a2) = NP '[a1, a2]
  abiDefault = (abiDefault, abiDefault)
  abiToCoreType = fromTupleNtoNP
  abiFromCoreType = fromNPtoTupleN

instance (ABITypeCodec a1, ABITypeCodec a2) => ABITypeCodec (a1, a2)

-- Generate the rest: Tuple3 .. Tuple64

do
  insts <- mapM (\n -> do
    as <- replicateM n (TH.newName "a")
    [d| instance $(tupleNFromVarsTWith (TH.conT ''ABITypeable `TH.appT`) as) =>
                  ABITypeable $(tupleNFromVarsT as) where
          type instance ABITypeDerivedOf $(tupleNFromVarsT as) = NP $(promotedListFromVarsT as)
          abiDefault = $(TH.tupE (replicate n (TH.varE 'abiDefault)))
          abiToCoreType = $(TH.varE 'fromTupleNtoNP)
          abiFromCoreType = $(TH.varE 'fromNPtoTupleN)
        instance $(tupleNFromVarsTWith (TH.conT ''ABITypeCodec `TH.appT`) as) =>
                 ABITypeCodec $(tupleNFromVarsT as)
     |]) [3..64]
  pure (concat insts)
