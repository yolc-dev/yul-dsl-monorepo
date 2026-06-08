{-# OPTIONS_GHC -Wno-orphans -Wno-missing-signatures #-}
{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE UndecidableInstances #-}
module YulDSL.StdBuiltIns.ValueType () where
-- base
-- eth-abi
import Ethereum.ContractABI
-- text
-- CodeGenUtils
--
import YulDSL.Core.YulBuiltIn

------------------------------------------------------------------------------------------------------------------------
-- Value cleanup, validation functions
------------------------------------------------------------------------------------------------------------------------

instance YulBuiltInPrefix "__cleanup_t_" U256 BOOL where
  yulB_fname b = yulB_prefix b ++ "bool"

instance ValidINTx s n => YulBuiltInPrefix "__cleanup_t_" U256 (INTx s n) where
  yulB_fname b = yulB_prefix b <> abiTypeCanonName @(INTx s n)

instance YulBuiltInPrefix "__cleanup_t_" U256 ADDR where
  yulB_fname b = yulB_prefix b ++ "address"

instance (ABITypeable a, YulBuiltInPrefix "__cleanup_t_" U256 a) => YulBuiltInPrefix "__validate_t_" a () where
  yulB_fname b = yulB_prefix b ++ abiTypeCanonName @a

------------------------------------------------------------------------------------------------------------------------
-- Integer comparators
------------------------------------------------------------------------------------------------------------------------

instance ValidINTx s n => YulBuiltInPrefix "__cmp_eq_t_" (INTx s n, INTx s n) BOOL where
  yulB_fname b = yulB_prefix b <> abiTypeCanonName @(INTx s n)
instance ValidINTx s n => YulBuiltInPrefix "__cmp_ne_t_" (INTx s n, INTx s n) BOOL where
  yulB_fname b = yulB_prefix b <> abiTypeCanonName @(INTx s n)
instance ValidINTx s n => YulBuiltInPrefix "__cmp_lt_t_" (INTx s n, INTx s n) BOOL where
  yulB_fname b = yulB_prefix b <> abiTypeCanonName @(INTx s n)
instance ValidINTx s n => YulBuiltInPrefix "__cmp_le_t_" (INTx s n, INTx s n) BOOL where
  yulB_fname b = yulB_prefix b <> abiTypeCanonName @(INTx s n)
instance ValidINTx s n => YulBuiltInPrefix "__cmp_gt_t_" (INTx s n, INTx s n) BOOL where
  yulB_fname b = yulB_prefix b <> abiTypeCanonName @(INTx s n)
instance ValidINTx s n => YulBuiltInPrefix "__cmp_ge_t_" (INTx s n, INTx s n) BOOL where
  yulB_fname b = yulB_prefix b <> abiTypeCanonName @(INTx s n)

------------------------------------------------------------------------------------------------------------------------
-- Integer arithmetic, including safe, checked, and maybe variants
------------------------------------------------------------------------------------------------------------------------

instance ValidINTx s n => YulBuiltInPrefix "__safe_add_t_" (INTx s n, INTx s n) (BOOL, INTx s n) where
  yulB_fname b = yulB_prefix b <> abiTypeCanonName @(INTx s n)

instance ValidINTx s n => YulBuiltInPrefix "__safe_sub_t_" (INTx s n, INTx s n) (BOOL, INTx s n) where
  yulB_fname b = yulB_prefix b <> abiTypeCanonName @(INTx s n)

instance ValidINTx s n => YulBuiltInPrefix "__safe_mul_t_" (INTx s n, INTx s n) (BOOL, INTx s n) where
  yulB_fname b = yulB_prefix b <> abiTypeCanonName @(INTx s n)

--
-- checked operation
--

instance ValidINTx s n => YulBuiltInPrefix "__checked_add_t_" (INTx s n, INTx s n) (INTx s n) where
  yulB_fname b = yulB_prefix b <> abiTypeCanonName @(INTx s n)
instance ValidINTx s n => YulBuiltInPrefix "__checked_sub_t_" (INTx s n, INTx s n) (INTx s n) where
  yulB_fname b = yulB_prefix b <> abiTypeCanonName @(INTx s n)
instance ValidINTx s n => YulBuiltInPrefix "__checked_mul_t_" (INTx s n, INTx s n) (INTx s n) where
  yulB_fname b = yulB_prefix b <> abiTypeCanonName @(INTx s n)
instance ValidINTx s n => YulBuiltInPrefix "__checked_sig_t_" (INTx s n) (INTx s n) where
  yulB_fname b = yulB_prefix b <> abiTypeCanonName @(INTx s n)
instance ValidINTx s n => YulBuiltInPrefix "__checked_abs_t_" (INTx s n) (INTx s n) where
  yulB_fname b = yulB_prefix b <> abiTypeCanonName @(INTx s n)

instance ValidINTx s n => YulBuiltInPrefix "__maybe_add_t_" (Maybe (INTx s n), Maybe (INTx s n)) (Maybe (INTx s n)) where
  yulB_fname b = yulB_prefix b <> abiTypeCanonName @(INTx s n)
instance ValidINTx s n => YulBuiltInPrefix "__maybe_sub_t_" (Maybe (INTx s n), Maybe (INTx s n)) (Maybe (INTx s n)) where
  yulB_fname b = yulB_prefix b <> abiTypeCanonName @(INTx s n)
instance ValidINTx s n => YulBuiltInPrefix "__maybe_mul_t_" (Maybe (INTx s n), Maybe (INTx s n)) (Maybe (INTx s n)) where
  yulB_fname b = yulB_prefix b <> abiTypeCanonName @(INTx s n)
instance ValidINTx s n => YulBuiltInPrefix "__maybe_sig_t_" (Maybe (INTx s n)) (Maybe (INTx s n)) where
  yulB_fname b = yulB_prefix b <> abiTypeCanonName @(INTx s n)
instance ValidINTx s n => YulBuiltInPrefix "__maybe_abs_t_" (Maybe (INTx s n)) (Maybe (INTx s n)) where
  yulB_fname b = yulB_prefix b <> abiTypeCanonName @(INTx s n)
