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
  abiToCoreType () = Nil
  abiFromCoreType Nil = ()
instance ABITypeCodec ()

-- ^ ABI typeable for solo tuple.
instance ABITypeable a => ABITypeable (Solo a) where
  type instance ABITypeDerivedOf (Solo a) = NP '[a]
  abiToCoreType = fromTupleNtoNP
  abiFromCoreType = fromNPtoTupleN
instance ABITypeCodec a => ABITypeCodec (Solo a)

-- | ABI typeable tuple.
instance (ABITypeable a1, ABITypeable a2) => ABITypeable (a1, a2) where
  type instance ABITypeDerivedOf (a1, a2) = NP '[a1, a2]
  abiToCoreType = fromTupleNtoNP
  abiFromCoreType = fromNPtoTupleN

instance (ABITypeCodec a1, ABITypeCodec a2) => ABITypeCodec (a1, a2)

-- Generate the rest: Tuple3 .. Tuple64

do
  let mk_tuple_n_t xs = foldl' TH.appT (TH.tupleT (length xs)) (map TH.varT xs)
  let mk_promoted_list_t = foldr (TH.appT . TH.appT TH.promotedConsT . TH.varT) TH.promotedNilT
  insts <- mapM (\n -> do
    xs <- replicateM n (TH.newName "a")
    let tpl = mk_tuple_n_t xs
    let plist = mk_promoted_list_t xs
    let clist1 = foldr (\x b -> b `TH.appT` (TH.conT ''ABITypeable `TH.appT` TH.varT x)) (TH.tupleT n) xs
    let clist2 = foldr (\x b -> b `TH.appT` (TH.conT ''ABITypeCodec `TH.appT` TH.varT x)) (TH.tupleT n) xs
    [d| instance $(clist1) => ABITypeable $(tpl) where
          type instance ABITypeDerivedOf $(tpl) = NP $(plist)
          abiToCoreType = $(TH.varE 'fromTupleNtoNP)
          abiFromCoreType = $(TH.varE 'fromNPtoTupleN)
        instance $(clist2) => ABITypeCodec $(tpl)
     |]) [3..64]
  pure (concat insts)
