{-# OPTIONS_GHC -Wno-orphans -Wno-missing-signatures #-}
{-# LANGUAGE OverloadedStrings #-}
module YulDSL.StdBuiltIns.ABICodec where
-- eth-abi
import Ethereum.ContractABI
-- text
import Data.Text.Lazy               qualified as T
-- CodeGenUtils
import CodeGenUtils.CodeFormatters
import CodeGenUtils.Variable
--
import YulDSL.Core.YulBuiltIn
--
import YulDSL.StdBuiltIns.ValueType ()


------------------------------------------------------------------------------------------------------------------------

instance ABITypeable b => YulBuiltInPrefix "__abidec_dispatcher_c_" (U256, U256) b where
  yulB_fname b = yulB_prefix b <> abiTypeCompactName @b
  yulB_body _ =
    let types = abiTypeInfo @b
        outVars = gen_vars (length types)
    in ( MkVar <$> ["headStart", "dataEnd"], outVars,
         abidec_main_body abidec_from_calldata_builtin_f types outVars,
         fmap abidec_from_calldata_builtin_f types)
  yulB_eval b = error ("NoImpl: yulB_eval " ++ yulB_prefix b)

instance ( ABITypeable b, YulBuiltInPrefix "__cleanup_t_" U256 b
         ) => YulBuiltInPrefix "__abidec_from_calldata_t_" (U256, U256) b where
  yulB_fname b = yulB_prefix b <> abiTypeCanonName @b
  yulB_body _ = ( MkVar <$> ["offset", "end"], [ MkVar "value" ]
                , [ "value := " <> T.pack (yulB_fname cleanup_f) <> "(calldataload(offset))" ]
                , [ MkAnyYulBuiltIn cleanup_f ])
    where cleanup_f = MkYulBuiltIn @"__cleanup_t_" @U256 @b
  yulB_eval b = error ("NoImpl: yulB_eval " ++ yulB_prefix b)

------------------------------------------------------------------------------------------------------------------------

instance ABITypeable b => YulBuiltInPrefix "__abidec_from_memory_c_" (U256, U256) b where
  yulB_fname b = yulB_prefix b <> abiTypeCompactName @b
  yulB_body _ =
    let types = abiTypeInfo @b
        outVars = gen_vars (length types)
    in ( MkVar <$> ["headStart", "dataEnd"], outVars,
         abidec_main_body abidec_from_memory_builtin_f types outVars,
         fmap abidec_from_memory_builtin_f types)
  yulB_eval b = error ("NoImpl: yulB_eval " ++ yulB_prefix b)

instance ( ABITypeable b, YulBuiltInPrefix "__cleanup_t_" U256 b
         ) => YulBuiltInPrefix "__abidec_from_memory_t_" (U256, U256) b where
  yulB_fname b = yulB_prefix b <> abiTypeCanonName @b
  yulB_body _ = ( MkVar <$> ["offset", "end"], [ MkVar "value" ]
                , [ "value := " <> T.pack (yulB_fname cleanup_f) <> "(mload(offset))" ]
                , [ MkAnyYulBuiltIn cleanup_f ])
    where cleanup_f = MkYulBuiltIn @"__cleanup_t_" @U256 @b
  yulB_eval b = error ("NoImpl: yulB_eval " ++ yulB_prefix b)

------------------------------------------------------------------------------------------------------------------------

instance ABITypeable a => YulBuiltInPrefix "__abienc_from_stack_c_" (U256, a) U256 where
  yulB_fname b = yulB_prefix b <> abiTypeCompactName @a
  yulB_body _ =
    let types = abiTypeInfo @a
        aVars = gen_vars (length types)
    in ( MkVar "headStart" : aVars, [ MkVar "tail" ]
       , abienc_main_body abienc_from_stack_builtin_f types aVars
       , fmap abienc_from_stack_builtin_f types)
  yulB_eval b = error ("NoImpl: yulB_eval " ++ yulB_prefix b)

instance ( ABITypeable a, YulBuiltInPrefix "__cleanup_t_" U256 a
         ) => YulBuiltInPrefix "__abienc_from_stack_t_" (U256, a) () where
  yulB_fname b = yulB_prefix b <> abiTypeCanonName @a
  yulB_body _ = ( MkVar <$> ["pos", "value"], []
                , [ "mstore(pos, " <> T.pack (yulB_fname cleanup_f) <> "(value))" ]
                , [ MkAnyYulBuiltIn cleanup_f ])
    where cleanup_f = MkYulBuiltIn @"__cleanup_t_" @U256 @a
  yulB_eval b = error ("NoImpl: yulB_eval " ++ yulB_prefix b)

instance ABITypeable a => YulBuiltInPrefix "__keccak_c_" a B32 where
  yulB_fname b = yulB_prefix b <> abiTypeCompactName @a
  yulB_body _ =
    let inVars = gen_vars (length (abiTypeInfo @a))
        abienc_builtin = MkYulBuiltIn @"__abienc_from_stack_c_" @(U256, a) @U256
    in ( inVars, [ MkVar "hash" ]
       , [ " let memPos := allocate_unbounded()"
         , " let memEnd := " <> T.pack (yulB_fname abienc_builtin) <> "(memPos, " <> spread_vars inVars <> ")"
         , " hash := keccak256(memPos, sub(memEnd, memPos))"
         ]
       , [ MkAnyYulBuiltIn abienc_builtin ])
  yulB_eval b = error ("TODO: yulB_eval " ++ yulB_prefix b)

------------------------------------------------------------------------------------------------------------------------

--
-- internal functions
--

-- decoder

abidec_from_calldata_builtin_f t = case t of
  INTx' @s @n _ _ -> MkAnyYulBuiltIn (MkYulBuiltIn @"__abidec_from_calldata_t_" @(U256, U256) @(INTx s n))
  BOOL'           -> MkAnyYulBuiltIn (MkYulBuiltIn @"__abidec_from_calldata_t_" @(U256, U256) @BOOL)
  ADDR'           -> MkAnyYulBuiltIn (MkYulBuiltIn @"__abidec_from_calldata_t_" @(U256, U256) @ADDR)
  BYTESn' @n _    -> MkAnyYulBuiltIn (MkYulBuiltIn @"__abidec_from_calldata_t_" @(U256, U256) @(BYTESn n))
  _               -> error ("abidec_from_calldata_builtin_f unsupported: " <> show t)

abidec_from_memory_builtin_f t = case t of
  INTx' @s @n _ _ -> MkAnyYulBuiltIn (MkYulBuiltIn @"__abidec_from_memory_t_" @(U256, U256) @(INTx s n))
  BOOL'           -> MkAnyYulBuiltIn (MkYulBuiltIn @"__abidec_from_memory_t_" @(U256, U256) @BOOL)
  ADDR'           -> MkAnyYulBuiltIn (MkYulBuiltIn @"__abidec_from_memory_t_" @(U256, U256) @ADDR)
  BYTESn' @n _    -> MkAnyYulBuiltIn (MkYulBuiltIn @"__abidec_from_memory_t_" @(U256, U256) @(BYTESn n))
  _               -> error ("abidec_from_memory_builtin_f unsupported: " <> show t)

abidec_main_body :: (ABICoreType -> AnyYulBuiltIn) -> [ABICoreType] -> [Var] -> [Code]
abidec_main_body builtin_f types vars =
  add_indent "if slt(sub(dataEnd, headStart), " <>
  -- TODO use a better revert
  T.pack (show dataSize) <> ") { revert(0, 0) }" :
  map add_indent (go types 0)
  where
    go (n:ns) slot =
      [ "{"
      , add_indent $ "let offset := " <> T.pack (show (slot * 32))
      , add_indent $ unVar (vars !! slot) <> " := "
        <> T.pack (case builtin_f n of MkAnyYulBuiltIn b -> yulB_fname b) <> "(add(headStart, offset), dataEnd)"
      , "}"
      ]
      ++ go ns (slot + 1)
    go [] _ = []
    dataSize = length types * 32

-- encoder

abienc_from_stack_builtin_f t = case t of
  INTx' @s @n _ _ -> MkAnyYulBuiltIn (MkYulBuiltIn @"__abienc_from_stack_t_" @(U256, INTx s n) @())
  BOOL'           -> MkAnyYulBuiltIn (MkYulBuiltIn @"__abienc_from_stack_t_" @(U256, BOOL) @())
  ADDR'           -> MkAnyYulBuiltIn (MkYulBuiltIn @"__abienc_from_stack_t_" @(U256, ADDR) @())
  BYTESn' @n _    -> MkAnyYulBuiltIn (MkYulBuiltIn @"__abienc_from_stack_t_" @(U256, BYTESn n) @())
  _               -> error ("abienc_from_stack_builtin_f unsupported: " <> show t)

abienc_main_body :: (ABICoreType -> AnyYulBuiltIn) -> [ABICoreType] -> [Var] -> [Code]
abienc_main_body builtin_f types vars =
  add_indent "tail := add(headStart, " <> T.pack (show dataSize) <> ")" :
  map add_indent (go types 0)
  where
    go (n:ns) slot =
      T.pack (case builtin_f n of MkAnyYulBuiltIn b -> yulB_fname b)
      <> "(add(headStart, " <> T.pack(show (slot * 32)) <> "), " <> unVar (vars !! slot) <> ")"
      : go ns (slot + 1)
    go _ _         = []
    dataSize = length types * 32
