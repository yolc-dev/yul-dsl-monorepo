{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_HADDOCK hide #-}
{-# LANGUAGE UndecidableInstances #-}
{-|

Copyright   : (c) 2023-2025 Miao, ZhiCheng
License     : LGPL-3
Maintainer  : hellwolf@yolc.dev
Stability   : experimental

= Description

This module defines the 'Num' instance from base library for Maybe 'YulNum' objects.

-}
module YulDSL.Haskell.YulCatObj.Maybe () where
-- yul-dsl
import YulDSL.Core
import YulDSL.StdBuiltIns.ValueType ()
-- (control-extra)
import Control.PatternMatchable


instance ValidINTx s n => ABITypeable (Maybe (INTx s n)) where
  type instance ABITypeDerivedOf (Maybe (INTx s n)) = NP [BOOL, INTx s n]

  abiToCoreType (Just x) = true :* abiToCoreType x :* Nil
  abiToCoreType Nothing  = false :* 0 :* Nil

  abiFromCoreType (b :* x :* Nil) = case b of
    BOOL True  -> Just (abiFromCoreType x)
    BOOL False -> Nothing
instance ValidINTx s n => ABITypeCodec (Maybe (INTx s n))
instance ValidINTx s n => YulCatObj (Maybe (INTx s n))

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

-- TODO:
-- , YulO3 (ABITypeDerivedOf a) (Maybe a) (ABITypeDerivedOf (Maybe a))
-- , ABITypeDerivedOf (Maybe a) ~ NP [BOOL, ABITypeDerivedOf a]
-- , ABITypeCoercible (ABITypeDerivedOf (Maybe a)) (BOOL, NP '[ABITypeDerivedOf a])

instance ( YulCat eff r ~ m
         , YulO1 r
         , ValidINTx s n ) =>
         PatternMatchable (YulCat eff r) YulCatObj (Maybe (INTx s n)) (Maybe (m (INTx s n))) where
  match pats f =
    let bn = pats >.> YulReduceType >.> YulExtendType :: YulCat eff r (BOOL, INTx s n)
        b  = bn >.> YulExl
        n  = bn >.> YulExr
    in yulIfThenElse b (f (Just n)) (f Nothing)

instance ( YulCat eff r ~ m
         , YulO1 r
         , ValidINTx s n ) =>
         InjectivePattern (YulCat eff r) YulCatObj (Maybe (INTx s n)) (Maybe (m (INTx s n))) where
  be = \case
    Just a  -> YulFork (YulEmb true) (a >.> YulReduceType)
               >.> YulReduceType
               >.> YulExtendType
    Nothing -> YulFork (YulEmb false) (YulEmb 0)
               >.> YulReduceType
               >.> YulExtendType
