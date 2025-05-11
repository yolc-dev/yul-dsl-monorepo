{-# OPTIONS_GHC -Wno-orphans #-}
{-|

Copyright   : (c) 2023-2025 Miao, ZhiCheng
License     : LGPL-3
Maintainer  : hellwolf@yolc.dev
Stability   : experimental

= Description

This module provides type class instance for Maybe-typed yul objects.

-}
module YulDSL.Haskell.YulCatObj.Maybe () where
-- yul-dsl
import YulDSL.Core
import YulDSL.StdBuiltIns.ValueType ()
--
import YulDSL.Haskell.YulCat        ()
-- (control-extra)
import Control.PatternMatchable
import Data.ExoFunctor


--
-- "Maybe a" as YulCatObj
--

instance {-# OVERLAPPABLE #-} ABITypeable a => ABITypeable (Maybe a) where
  type instance ABITypeDerivedOf (Maybe a) = NP [BOOL, a]
  abiDefault = Nothing
  abiToCoreType = error "to be implemented"
  abiFromCoreType = error "to be implemented"

-- only support "Maybe (INTx s n)" for now:

instance ValidINTx s n => ABITypeable (Maybe (INTx s n)) where
  type instance ABITypeDerivedOf (Maybe (INTx s n)) = NP [BOOL, INTx s n]
  abiDefault = Nothing
  abiToCoreType (Just x) = true :* abiToCoreType x :* Nil
  abiToCoreType Nothing  = false :* 0 :* Nil

  abiFromCoreType (b :* x :* Nil) = case b of
    BOOL True  -> Just (abiFromCoreType x)
    BOOL False -> Nothing

instance ValidINTx s n => ABITypeCodec (Maybe (INTx s n))

instance ValidINTx s n => YulCatObj (Maybe (INTx s n))

--
-- Num instance for "Maybe (INTx s n)"
--

instance (YulO1 a, ValidINTx s n) => Num (YulCat eff a (Maybe (INTx s n))) where
  a + b = YulJmpB (MkYulBuiltIn @"__maybe_add_t_") <.< YulProd a b <.< YulDup
  a - b = YulJmpB (MkYulBuiltIn @"__maybe_sub_t_") <.< YulProd a b <.< YulDup
  a * b = YulJmpB (MkYulBuiltIn @"__maybe_mul_t_") <.< YulProd a b <.< YulDup
  signum = YulComp (YulJmpB (MkYulBuiltIn @"__maybe_sig_t_"))
  abs = YulComp (YulJmpB (MkYulBuiltIn @"__maybe_abs_t_"))
  fromInteger x = yulEmb (Just (fromInteger x))

--
-- PatternMatchable instances for "Maybe a"
--

instance YulO2 r a => InjectivePattern (YulCat eff r) (Maybe a) (Maybe (YulCat eff r a)) YulCatObj Many where
  be = \case
    Just a  -> YulFork (yulEmb true) a
               >.> YulReduceType
               >.> YulExtendType
    Nothing -> YulFork (yulEmb false) (yulEmb abiDefault)
               >.> YulReduceType
               >.> YulExtendType

instance YulO2 a r => PatternMatchable (YulCat eff r) (Maybe a) (Maybe (YulCat eff r a)) YulCatObj Many where
  match pats f =
    let bn pats' = pats' >.> YulReduceType >.> YulExtendType -- :: YulCat eff r (BOOL, INTx s n)
    in YulApply <.<
         yulSwitch
           (\pats' -> bn pats' >.> YulExl >.> yulSafeCast)
           [ (1, \pats' -> f (Just (bn pats' >.> YulExr)))
           , (0, \_ -> f Nothing)]
           (const yulRevert)
         `YulFork`
         pats

--
-- YulFunctor instance
--

instance YulO1 r => HexoFunctor Maybe (YulCat eff) r (YulCat eff) r where
  hexomap g fa = match fa \case
    Just val -> be (Just (g val))
    Nothing -> be Nothing

instance ExoFunctor Maybe (YulCat eff) (YulCat eff) where
  exomap g = match YulId \case
    Just val -> be (Just g) <.< val
    Nothing  -> be Nothing
