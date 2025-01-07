{-# LANGUAGE AllowAmbiguousTypes #-}
{-|

Copyright   : (c) 2023-2024 Miao, ZhiCheng
License     : LGPL-3
Maintainer  : hellwolf@yolc.dev
Stability   : experimental

= Description

This module provides built-in yul functions for the number objects of the YulCat.

-}
module YulDSL.Core.YulNum
  ( YulNum (..)
  , YulNumCmp (..)
  ) where

-- eth-abi
import Ethereum.ContractABI
--
import YulDSL.Core.YulCatObj

-- | Arithmetic operators for the number objects in the YulCat.
class (YulCatObj a, Num a, Ord a) => YulNum a where
  yulB_NumAdd :: BuiltInYulFunction (a, a) a
  yulB_NumSub :: BuiltInYulFunction (a, a) a
  yulB_NumMul :: BuiltInYulFunction (a, a) a
  yulB_NumAbs :: BuiltInYulFunction a a
  yulB_NumSig :: BuiltInYulFunction a a

-- | Comparing number objects in the YulCat.
class YulNum a => YulNumCmp a where
  yulB_NumCmp :: (Bool, Bool, Bool) -> BuiltInYulFunction (a, a) BOOL

instance ValidINTx s n => YulNum (INTx s n) where
  yulB_NumAdd = (mk_chk_op @(INTx s n) "add", uncurry (+))
  yulB_NumSub = (mk_chk_op @(INTx s n) "sub", uncurry (-))
  yulB_NumMul = (mk_chk_op @(INTx s n) "mul", uncurry (*))
  yulB_NumAbs = (mk_chk_op @(INTx s n) "abs", abs)
  yulB_NumSig = (mk_chk_op @(INTx s n) "sig", signum)

instance ValidINTx s n => YulNumCmp (INTx s n) where
  yulB_NumCmp (True , False, False) = (mk_cmp_op @(INTx s n) "lt", BOOL . uncurry ( <))
  yulB_NumCmp (True , True , False) = (mk_cmp_op @(INTx s n) "le", BOOL . uncurry (<=))
  yulB_NumCmp (False, True , False) = (mk_cmp_op @(INTx s n) "eq", BOOL . uncurry (==))
  yulB_NumCmp (False, True , True ) = (mk_cmp_op @(INTx s n) "ge", BOOL . uncurry (>=))
  yulB_NumCmp (False, False, True ) = (mk_cmp_op @(INTx s n) "gt", BOOL . uncurry ( >))
  yulB_NumCmp _                     = error "yulNumCmp: invalid boolean-switches combo"

--
-- Internal function
--

mk_chk_op :: forall a. ABITypeable a => String -> String
mk_chk_op n = "__checked_" ++ n ++ "_t_" ++ abiTypeCanonName @a

mk_cmp_op :: forall a s n. (a ~ INTx s n, ValidINTx s n) => String -> String
mk_cmp_op op = "__cmp_" ++ (if fromBoolKind @s then 's':op else op)  ++ "_t_" ++ abiTypeCanonName @a
