{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_HADDOCK hide #-}
{-|

Copyright   : (c) 2023-2025 Miao, ZhiCheng
License     : LGPL-3
Maintainer  : hellwolf@yolc.dev
Stability   : experimental

= Description

This module defines the 'Num' instance from base library for Maybe 'YulNum' objects.

-}
module YulDSL.Haskell.YulCatObj.Maybe
  ( MaybeYulNum
  ) where
-- eth-abi
import Ethereum.ContractABI
-- yul-dsl
import YulDSL.Core
import YulDSL.StdBuiltIns.ValueType ()
-- (control-extra)
import Control.PatternMatchable


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

  abiToCoreType (Just x) = true :* abiToCoreType x :* Nil
  abiToCoreType Nothing  = false :* 0 :* Nil

  abiFromCoreType (b :* x :* Nil) = case b of
    BOOL True  -> Just (abiFromCoreType x)
    BOOL False -> Nothing

instance MaybeYulNum a => ABITypeCodec (Maybe a)

instance (MaybeYulNum a, Show a) => YulCatObj (Maybe a)

instance (YulO1 r, ValidINTx s n) => Num (YulCat eff r (Maybe (INTx s n))) where
  a + b = YulJmpB (MkYulBuiltIn @"__maybe_add_t_") <.< YulProd a b <.< YulDup
  a - b = YulJmpB (MkYulBuiltIn @"__maybe_sub_t_") <.< YulProd a b <.< YulDup
  a * b = YulJmpB (MkYulBuiltIn @"__maybe_mul_t_") <.< YulProd a b <.< YulDup
  signum = YulComp (YulJmpB (MkYulBuiltIn @"__maybe_sig_t_"))
  abs = YulComp (YulJmpB (MkYulBuiltIn @"__maybe_abs_t_"))
  fromInteger = YulEmb . Just . fromInteger

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
                 in yulIfThenElse b (f (Just n)) (f Nothing)
