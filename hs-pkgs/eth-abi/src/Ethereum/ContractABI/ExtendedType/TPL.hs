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
module Ethereum.ContractABI.ExtendedType.TPL
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
import Ethereum.ContractABI.CoreType.NP  (I (I), NP (..))


-- ^ ABI typeable unit.
instance ABITypeable () where
  type instance ABITypeDerivedOf () = NP I '[]
  abiDefault = ()
  abiToCoreType () = Nil
  abiFromCoreType Nil = ()
instance ABITypeCodec ()

-- ^ ABI typeable for solo tuple.
instance ABITypeable a => ABITypeable (Solo a) where
  type instance ABITypeDerivedOf (Solo a) = NP I '[a]
  abiDefault = MkSolo abiDefault
  abiToCoreType (MkSolo a) = I a :* Nil
  abiFromCoreType (I a :* Nil) = MkSolo a
instance ABITypeCodec a => ABITypeCodec (Solo a)

-- | ABI typeable tuple2.
instance (ABITypeable a1, ABITypeable a2) => ABITypeable (a1, a2) where
  type instance ABITypeDerivedOf (a1, a2) = NP I '[a1, a2]
  abiDefault = (abiDefault, abiDefault)
  abiToCoreType (a1, a2) = I a1 :* I a2 :* Nil
  abiFromCoreType (I a1 :* I a2 :* Nil) = (a1, a2)
instance (ABITypeCodec a1, ABITypeCodec a2) => ABITypeCodec (a1, a2)

-- Generate the tuples (from tuple3) with identity wrappers:

instance (ABITypeable a1, ABITypeable a2, ABITypeable a3) => ABITypeable (a1, a2, a3) where
  type instance ABITypeDerivedOf (a1, a2, a3) = NP I '[a1, a2, a3]
  abiDefault = (abiDefault, abiDefault, abiDefault)
  abiToCoreType (a1, a2, a3) = I a1 :* I a2 :* I a3 :* Nil
  abiFromCoreType (I a1 :* I a2 :* I a3:* Nil) = (a1, a2, a3)
instance (ABITypeCodec a1, ABITypeCodec a2, ABITypeCodec a3) => ABITypeCodec (a1, a2, a3)

do
  insts <- mapM (\n -> do
    let np_e = foldr (\a b -> TH.infixE (Just a) (TH.conE '(:*)) (Just b)) (TH.conE 'Nil)
    let np_p = foldr (\a b -> TH.infixP a '(:*) b) (TH.conP 'Nil [])
    t_as <- replicateM n (TH.newName "a")
    xs <- replicateM n (TH.newName "x")
    [d| instance $(tupleNFromVarsTWith (TH.conT ''ABITypeable `TH.appT`) t_as) =>
                  ABITypeable $(tupleNFromVarsT t_as) where
          type instance ABITypeDerivedOf $(tupleNFromVarsT t_as) = NP I $(promotedListFromVarsT t_as)
          abiDefault = $(TH.tupE (replicate n (TH.varE 'abiDefault)))
          abiToCoreType $(TH.tupP (TH.varP <$> xs)) = $(np_e ((TH.conE 'I `TH.appE`) . TH.varE <$> xs))
          abiFromCoreType $(np_p (TH.conP 'I . (:[]) . TH.varP <$> xs)) = $(TH.tupE (TH.varE <$> xs))
        instance $(tupleNFromVarsTWith (TH.conT ''ABITypeCodec `TH.appT`) t_as) =>
                 ABITypeCodec $(tupleNFromVarsT t_as)
     |]) [4..16]
  pure (concat insts)
