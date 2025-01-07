{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-|

Copyright   : (c) 2023-2024 Miao, ZhiCheng
License     : LGPL-3
Maintainer  : hellwolf@yolc.dev
Stability   : experimental

= Description

This module defines the 'Num' instance from base library for Maybe 'YulNum' objects.

-}
module YulDSL.YulCatObj.Prelude.Base.Maybe
  ( MaybeYulNum
  ) where

-- eth-abi
import Ethereum.ContractABI
--
import YulDSL.Core.YulCat
import YulDSL.Core.YulCatObj
import YulDSL.Core.YulNum


--
-- Maybe (INTx s n) being a YulNum
--

type MaybeYulNum a = ( ABITypeable a
                     , ABITypeable (ABITypeDerivedOf a)
                     , ABITypeCodec (ABITypeDerivedOf a)
                     , Num (ABITypeDerivedOf a)
                     )

instance MaybeYulNum a => ABITypeable (Maybe a) where
  type instance ABITypeDerivedOf (Maybe a) = NP [BOOL, ABITypeDerivedOf a]
  type instance ABITypeValueSize (Maybe a) = 32

  abiToCoreType (Just x) = true :* abiToCoreType x :* Nil
  abiToCoreType Nothing  = false :* 0 :* Nil

  abiFromCoreType (b :* x :* Nil) = case b of
    BOOL True  -> Just (abiFromCoreType x)
    BOOL False -> Nothing

instance MaybeYulNum a => ABITypeCodec (Maybe a)

instance (MaybeYulNum a, Show a) => YulCatObj (Maybe a)

instance ValidINTx s n => YulNum (Maybe (INTx s n)) where
  yulB_NumAdd = (mk_maybe_op @(INTx s n) "add", uncurry (+))
  yulB_NumMul = (mk_maybe_op @(INTx s n) "mul", uncurry (*))
  yulB_NumSub = (mk_maybe_op @(INTx s n) "sub", uncurry (-))
  yulB_NumAbs = (mk_maybe_op @(INTx s n) "abs", abs)
  yulB_NumSig = (mk_maybe_op @(INTx s n) "sig", signum)

mk_maybe_op :: forall a. ABITypeable a => String -> String
mk_maybe_op n = "__maybe_" ++ n ++ "_t_" ++ abiTypeCanonName @a

--
-- PatternMatchable instance
--

instance ( YulCat eff r ~ m
         , YulO2 r a, YulCatObj (ABITypeDerivedOf a), MaybeYulNum a
         ) => PatternMatchable m (Maybe a) (Maybe (m a)) YulCatObj where
  inCase = \case
    Just a  -> YulFork (YulEmb true) (a >.> YulReduceType)
               >.> YulReduceType
               >.> YulExtendType -- @_ @(NP [BOOL, ABITypeDerivedOf a]) @(Maybe a)
    Nothing -> YulFork (YulEmb false) (YulEmb 0)
               >.> YulReduceType
               >.> YulExtendType

  match mp f = let mp' = mp >.> YulReduceType >.> YulSplit
                   b   = mp' >.> YulExl
                   n   = mp' >.> YulExr
                         >.> YulCoerceType @_ @(NP '[ABITypeDerivedOf a]) @(ABITypeDerivedOf a, NP '[])
                         >.> YulExl @_ @(ABITypeDerivedOf a) @_
                         >.> YulExtendType
                 in ifThenElse b (f (Just n)) (f Nothing)
