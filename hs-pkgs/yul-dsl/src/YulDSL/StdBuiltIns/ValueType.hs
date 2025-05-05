{-# OPTIONS_GHC -Wno-orphans -Wno-missing-signatures #-}
{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE UndecidableInstances #-}
module YulDSL.StdBuiltIns.ValueType where
-- base
import Data.Maybe                  (fromJust)
-- eth-abi
import Ethereum.ContractABI
-- text
import Data.Text.Lazy              qualified as T
-- CodeGenUtils
import CodeGenUtils.CodeFormatters
import CodeGenUtils.Variable
--
import YulDSL.Core.YulBuiltIn

------------------------------------------------------------------------------------------------------------------------
-- Value cleanup, validation functions
------------------------------------------------------------------------------------------------------------------------

instance YulBuiltInPrefix "__cleanup_t_" U256 BOOL where
  yulB_fname b = yulB_prefix b ++ "bool"
  yulB_body _ = ( [MkVar "value"], [MkVar "cleaned"]
                , [ "cleaned := iszero(iszero(value))" ]
                , [])
  yulB_eval b = error ("NoImpl: yulB_eval " ++ yulB_prefix b)

instance ValidINTx s n => YulBuiltInPrefix "__cleanup_t_" U256 (INTx s n) where
  yulB_fname b = yulB_prefix b <> abiTypeCanonName @(INTx s n)
  yulB_body _ =
    let nbits = intxNBits @(INTx s n)
        icode = [ if nbits < 256
                  then "cleaned := signextend(" <> T.pack (show (nbits `div` 8 - 1)) <> ", value)"
                  else "cleaned := value"
                ]
        ucode = [ if nbits < 256
                  then "cleaned := and(value, " <> max_uint_val nbits <> ")"
                  else "cleaned := value"
                ]
    in ( [MkVar "value"], [MkVar "cleaned"]
       , if fromBoolKind @s then icode else ucode
       , [])
  yulB_eval b = error ("NoImpl: yulB_eval " ++ yulB_prefix b)

instance YulBuiltInPrefix "__cleanup_t_" U256 ADDR where
  yulB_fname b = yulB_prefix b ++ "address"
  yulB_body _ = ( [MkVar "value"], [MkVar "cleaned"]
                , [ "cleaned := " <> T.pack (yulB_fname cleanup_f) <> "(value)" ]
                , [MkAnyYulBuiltIn cleanup_f])
    where cleanup_f = MkYulBuiltIn @"__cleanup_t_" @U256 @U160
  yulB_eval b = error ("NoImpl: yulB_eval " ++ yulB_prefix b)

instance (ABITypeable a, YulBuiltInPrefix "__cleanup_t_" U256 a) => YulBuiltInPrefix "__validate_t_" a () where
  yulB_fname b = yulB_prefix b ++ abiTypeCanonName @a
  yulB_body _ = ( [MkVar "value"], []
                , [ "if neq(value, " <> T.pack (yulB_fname cleanup_f) <> "(value)) { revert(0, 0) }" ]
                , [MkAnyYulBuiltIn cleanup_f])
    where cleanup_f = MkYulBuiltIn @"__cleanup_t_" @U256 @a
  yulB_eval b = error ("NoImpl: yulB_eval " ++ yulB_prefix b)

------------------------------------------------------------------------------------------------------------------------
-- Integer comparators
------------------------------------------------------------------------------------------------------------------------

mk_cmp_body :: forall s n. ValidINTx s n => String -> ([Var], [Var], [Code], [AnyYulBuiltIn])
mk_cmp_body op = ( MkVar <$> ["x", "y"], [MkVar "b"]
                 , [ "b := " <> T.pack op <> "(" <> cleanup_fname <> "(x), " <> cleanup_fname <> "(y))" ]
                 , [])
  where cleanup_f = MkYulBuiltIn @"__cleanup_t_" @U256 @(INTx s n)
        cleanup_fname = T.pack $ yulB_fname cleanup_f

instance ValidINTx s n => YulBuiltInPrefix "__cmp_eq_t_" (INTx s n, INTx s n) BOOL where
  yulB_fname b = yulB_prefix b <> abiTypeCanonName @(INTx s n)
  yulB_body _ = mk_cmp_body @s @n "eq"
  yulB_eval _ (x, y) = BOOL (x == y)
instance ValidINTx s n => YulBuiltInPrefix "__cmp_ne_t_" (INTx s n, INTx s n) BOOL where
  yulB_fname b = yulB_prefix b <> abiTypeCanonName @(INTx s n)
  yulB_body _ = mk_cmp_body @s @n "neq"
  yulB_eval _ (x, y) = BOOL (x /= y)
instance ValidINTx s n => YulBuiltInPrefix "__cmp_lt_t_" (INTx s n, INTx s n) BOOL where
  yulB_fname b = yulB_prefix b <> abiTypeCanonName @(INTx s n)
  yulB_body _ = mk_cmp_body @s @n (if fromBoolKind @s then "slt" else "lt")
  yulB_eval _ (x, y) = BOOL (x < y)
instance ValidINTx s n => YulBuiltInPrefix "__cmp_le_t_" (INTx s n, INTx s n) BOOL where
  yulB_fname b = yulB_prefix b <> abiTypeCanonName @(INTx s n)
  yulB_body _ = mk_cmp_body @s @n (if fromBoolKind @s then "sle" else "le")
  yulB_eval _ (x, y) = BOOL (x <= y)
instance ValidINTx s n => YulBuiltInPrefix "__cmp_gt_t_" (INTx s n, INTx s n) BOOL where
  yulB_fname b = yulB_prefix b <> abiTypeCanonName @(INTx s n)
  yulB_body _ = mk_cmp_body @s @n (if fromBoolKind @s then "sgt" else "gt")
  yulB_eval _ (x, y) = BOOL (x > y)
instance ValidINTx s n => YulBuiltInPrefix "__cmp_ge_t_" (INTx s n, INTx s n) BOOL where
  yulB_fname b = yulB_prefix b <> abiTypeCanonName @(INTx s n)
  yulB_body _ = mk_cmp_body @s @n (if fromBoolKind @s then "sge" else "ge")
  yulB_eval _ (x, y) = BOOL (x >= y)

------------------------------------------------------------------------------------------------------------------------
-- Integer arithmetic, including safe, checked, and maybe variants
------------------------------------------------------------------------------------------------------------------------

instance ValidINTx s n => YulBuiltInPrefix "__safe_add_t_" (INTx s n, INTx s n) (BOOL, INTx s n) where
  yulB_fname b = yulB_prefix b <> abiTypeCanonName @(INTx s n)
  yulB_body _ =
    let nbits = intxNBits @(INTx s n)
        cleanup_f = MkYulBuiltIn @"__cleanup_t_" @U256 @(INTx s n)
        inVars = MkVar <$> ["x", "y"]
        outVars = MkVar <$> ["sum", "failed"]
        ucode = [ "x := " <> T.pack (yulB_fname cleanup_f) <> "(x)"
                , "y := " <> T.pack (yulB_fname cleanup_f) <> "(y)"
                , "sum := add(x, y)"
                , "if "
                  <> (if nbits < 256 then "gt(sum, " <> max_uint_val nbits  <> ")" else "gt(x, sum)")
                  <> " { failed := true }"
                ]
        icode = [ "x := " <> T.pack (yulB_fname cleanup_f) <> "(x)"
                , "y := " <> T.pack (yulB_fname cleanup_f) <> "(y)"
                , "sum := add(x, y)"
                , "if or("
                ] ++ ( if nbits < 256
                       then [ " sgt(sum, " <> max_int_val nbits <> "),"
                            , " slt(sum, " <> min_int_val nbits <> ")" ]
                       else [ " and(sge(x, 0), slt(sum, y)),"
                            , " and(slt(x, 0), sge(sum, y))" ]) ++
                [ ") { failed := true }" ]
    in ( inVars, outVars, if fromBoolKind @s then icode else ucode
       , [MkAnyYulBuiltIn cleanup_f] )
  yulB_eval _ (x, y) = case Just x + Just y of Just z  -> (true, z); Nothing -> (false, 0)

instance ValidINTx s n => YulBuiltInPrefix "__safe_sub_t_" (INTx s n, INTx s n) (BOOL, INTx s n) where
  yulB_fname b = yulB_prefix b <> abiTypeCanonName @(INTx s n)
  yulB_body _ =
    let nbits = intxNBits @(INTx s n)
        cleanup_f = MkYulBuiltIn @"__cleanup_t_" @U256 @(INTx s n)
        inVars = MkVar <$> ["x", "y"]
        outVars = MkVar <$> ["diff", "failed"]
        icode = [ "x := " <> T.pack (yulB_fname cleanup_f) <> "(x)"
                , "y := " <> T.pack (yulB_fname cleanup_f) <> "(y)"
                , "diff := sub(x, y)"
                , "if or("
                ] ++
                (if nbits < 256
                  then [ " slt(diff, " <> min_int_val nbits <> "),"
                       , " sgt(diff, " <> max_int_val nbits <> ")" ]
                  else [ " and(sge(y, 0), sgt(diff, x)),"
                       , " and(slt(y, 0), slt(diff, x))" ]) ++
                [ ") { failed := true }" ]
        ucode = [ "x := " <> T.pack (yulB_fname cleanup_f) <> "(x)"
                , "y := " <> T.pack (yulB_fname cleanup_f) <> "(y)"
                , "diff := sub(x, y)"
                , "if "
                  <> (if nbits < 256 then "gt(diff, " <> max_uint_val nbits <> ")" else "gt(diff, x)")
                  <> " { failed := true}"
                ]
    in ( inVars, outVars, if fromBoolKind @s then icode else ucode
       , [MkAnyYulBuiltIn cleanup_f] )
  yulB_eval _ (x, y) = case Just x - Just y of Just z  -> (true, z); Nothing -> (false, 0)

instance ValidINTx s n => YulBuiltInPrefix "__safe_mul_t_" (INTx s n, INTx s n) (BOOL, INTx s n) where
  yulB_fname b = yulB_prefix b <> abiTypeCanonName @(INTx s n)
  yulB_body _ =
    let nbits = intxNBits @(INTx s n)
        cleanup_f = MkYulBuiltIn @"__cleanup_t_" @U256 @(INTx s n)
        inVars = MkVar <$> ["x", "y"]
        outVars = MkVar <$> ["product", "failed"]
        icode = [ "x := " <> T.pack (yulB_fname cleanup_f) <> "(x)"
                , "y := " <> T.pack (yulB_fname cleanup_f) <> "(y)"
                , "let product_raw := mul(x, y)"
                , "product := " <> T.pack (yulB_fname cleanup_f) <> "(product_raw)"
                ] ++
                if nbits == 256
                then [ "if and(slt(x, 0), eq(y, " <> min_int_val nbits <> ")) { failed := true }"
                     , "if iszero(failed) {"
                     , " if iszero(or(iszero(x), eq(y, sdiv(product, x)))) { failed := true }"
                     , "}"
                     ]
                else if nbits > 128
                then [ "if iszero(or(iszero(x), eq(y, sdiv(product, x)))) { failed := true }" ]
                else [ "if neq(product, product_raw) { failed := true }"]
        ucode = [ "x := " <> T.pack (yulB_fname cleanup_f) <> "(x)"
                , "y := " <> T.pack (yulB_fname cleanup_f) <> "(y)"
                , "let product_raw := mul(x, y)"
                , "product := " <> T.pack (yulB_fname cleanup_f) <> "(product_raw)"
                ] ++
                if nbits > 128
                then [ "// overflow, if x != 0 and y != product/x"
                     , "if iszero(or(iszero(x), eq(y, div(product, x)))) { failed := true }"
                     ]
                else [ "if neq(product, product_raw) { failed := true }" ]
    in ( inVars, outVars, if fromBoolKind @s then icode else ucode
       , [MkAnyYulBuiltIn cleanup_f] )
  yulB_eval _ (x, y) = case Just x * Just y of Just z  -> (true, z); Nothing -> (false, 0)

--
-- checked operation
--

mk_checked_body :: YulBuiltInPrefix p a b => YulBuiltIn p a b -> ([Var], [Var], [Code], [AnyYulBuiltIn])
mk_checked_body safe_op =
  ( MkVar <$> ["x", "y"], MkVar <$> ["result"]
  , [ "let failed := false"
    , "result, failed := " <> T.pack (yulB_fname safe_op) <> "(x, y)"
    , "if eq(failed, true) { panic_error(0x11) }"
    ]
  , [ MkAnyYulBuiltIn safe_op ])

instance ValidINTx s n => YulBuiltInPrefix "__checked_add_t_" (INTx s n, INTx s n) (INTx s n) where
  yulB_fname b = yulB_prefix b <> abiTypeCanonName @(INTx s n)
  yulB_body _ = mk_checked_body (MkYulBuiltIn @"__safe_add_t_" @(INTx s n, INTx s n) @(BOOL, INTx s n))
  yulB_eval _ (x, y) = x + y
instance ValidINTx s n => YulBuiltInPrefix "__checked_sub_t_" (INTx s n, INTx s n) (INTx s n) where
  yulB_fname b = yulB_prefix b <> abiTypeCanonName @(INTx s n)
  yulB_body _ = mk_checked_body (MkYulBuiltIn @"__safe_sub_t_" @(INTx s n, INTx s n) @(BOOL, INTx s n))
  yulB_eval _ (x, y) = x - y
instance ValidINTx s n => YulBuiltInPrefix "__checked_mul_t_" (INTx s n, INTx s n) (INTx s n) where
  yulB_fname b = yulB_prefix b <> abiTypeCanonName @(INTx s n)
  yulB_body _ = mk_checked_body (MkYulBuiltIn @"__safe_mul_t_" @(INTx s n, INTx s n) @(BOOL, INTx s n))
  yulB_eval _ (x, y) = x * y
instance ValidINTx s n => YulBuiltInPrefix "__checked_sig_t_" (INTx s n) (INTx s n) where
  yulB_fname b = yulB_prefix b <> abiTypeCanonName @(INTx s n)
  yulB_body _ = undefined -- FIXME
  yulB_eval _ = signum
instance ValidINTx s n => YulBuiltInPrefix "__checked_abs_t_" (INTx s n) (INTx s n) where
  yulB_fname b = yulB_prefix b <> abiTypeCanonName @(INTx s n)
  yulB_body _ = undefined -- FIXME
  yulB_eval _ = abs

mk_maybe_body :: YulBuiltInPrefix p a b => YulBuiltIn p a b -> ([Var], [Var], [Code], [AnyYulBuiltIn])
mk_maybe_body safe_op =
  ( MkVar <$> ["tx", "x", "ty", "y"], MkVar <$> ["t", "result"]
  , [ "t := iszero(or(iszero(tx), iszero(ty)))"
    , "if eq(t, true) {" -- both Just values
    , "  result, t := " <> T.pack (yulB_fname safe_op) <> "(x, y)"
    , "  if eq(t, true) {" -- t: failed
    , "    result := 0"
    , "  }"
    , "  t := iszero(t)" -- flip t: not failed / Just value
    , "}"
    ]
  , [ MkAnyYulBuiltIn safe_op ])

instance ValidINTx s n => YulBuiltInPrefix "__maybe_add_t_" (Maybe (INTx s n), Maybe (INTx s n)) (Maybe (INTx s n)) where
  yulB_fname b = yulB_prefix b <> abiTypeCanonName @(INTx s n)
  yulB_body _ = mk_maybe_body (MkYulBuiltIn @"__safe_add_t_" @(INTx s n, INTx s n) @(BOOL, INTx s n))
  yulB_eval _ (x, y) = x + y
instance ValidINTx s n => YulBuiltInPrefix "__maybe_sub_t_" (Maybe (INTx s n), Maybe (INTx s n)) (Maybe (INTx s n)) where
  yulB_fname b = yulB_prefix b <> abiTypeCanonName @(INTx s n)
  yulB_body _ = mk_maybe_body (MkYulBuiltIn @"__safe_sub_t_" @(INTx s n, INTx s n) @(BOOL, INTx s n))
  yulB_eval _ (x, y) = x - y
instance ValidINTx s n => YulBuiltInPrefix "__maybe_mul_t_" (Maybe (INTx s n), Maybe (INTx s n)) (Maybe (INTx s n)) where
  yulB_fname b = yulB_prefix b <> abiTypeCanonName @(INTx s n)
  yulB_body _ = mk_maybe_body (MkYulBuiltIn @"__safe_mul_t_" @(INTx s n, INTx s n) @(BOOL, INTx s n))
  yulB_eval _ (x, y) = x * y
instance ValidINTx s n => YulBuiltInPrefix "__maybe_sig_t_" (Maybe (INTx s n)) (Maybe (INTx s n)) where
  yulB_fname b = yulB_prefix b <> abiTypeCanonName @(INTx s n)
  yulB_body _ = undefined -- FIXME
  yulB_eval _ = signum
instance ValidINTx s n => YulBuiltInPrefix "__maybe_abs_t_" (Maybe (INTx s n)) (Maybe (INTx s n)) where
  yulB_fname b = yulB_prefix b <> abiTypeCanonName @(INTx s n)
  yulB_body _ = undefined -- FIXME
  yulB_eval _ = abs

--
-- Internal functions
--

max_uint_val nbits = T.pack . show . fromJust $
  withSomeValidINTx False (toInteger (nbits `div` 8)) $
  \_ (_ :: SNat n) -> toWord (maxBound @(INTx False n))

max_int_val nbits = T.pack . show . fromJust $
  withSomeValidINTx True (toInteger (nbits `div` 8)) $
  \_ (_ :: SNat n) -> toWord (maxBound @(INTx True n))

min_int_val nbits = T.pack . show . fromJust $
  withSomeValidINTx True (toInteger (nbits `div` 8)) $
  \_ (_ :: SNat n) -> toWord (intxUpCast (minBound @(INTx True n)) :: I256)

------------------------------------------------------------------------------------------------------------------------
-- Safe value casting
------------------------------------------------------------------------------------------------------------------------

instance ValidINTx s n => YulBuiltInPrefix "__safecast_bool_t_" BOOL (INTx s n) where
  yulB_eval _ = fromJust . fromWord . toWord
