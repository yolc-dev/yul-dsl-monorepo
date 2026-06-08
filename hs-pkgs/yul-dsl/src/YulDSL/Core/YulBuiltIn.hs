{-|
Copyright   : (c) 2025 Miao, ZhiCheng
License     : LGPL-3
Maintainer  : hellwolf@yolc.dev
Stability   : experimental

= Description

This module provides type class and data types for defining yul built-in functions.

-}
{-# LANGUAGE OverloadedStrings #-}
module YulDSL.Core.YulBuiltIn
  ( YulBuiltInPrefix
  ) where
-- base
import GHC.TypeLits                (KnownSymbol (symbolSing), Symbol, fromSSymbol)
import Ethereum.ContractABI

-- text
-- (codegen-util)


-- | Yul built-in definition.
class KnownSymbol prefix => YulBuiltInPrefix (prefix :: Symbol) a b where
  -- | Yul function name for the built-in.
  -- | Optional yul function body, which consists of in-vars, out-vars, lines of code, and built-in dependencies.

-- | Reference to an instance of yul built-in by its prefix @p@, domain and codomain types @a -> b@.
data YulBuiltIn p a b = MkYulBuiltIn



instance ( ABITypeable b, YulBuiltInPrefix "__cleanup_t_" U256 b
         ) => YulBuiltInPrefix "__abidec_from_calldata_t_" (U256, U256) b where

instance ABITypeable a => YulBuiltInPrefix "__abienc_from_stack_c_" (U256, a) U256 where

instance ( ABITypeable a, YulBuiltInPrefix "__cleanup_t_" U256 a
         ) => YulBuiltInPrefix "__abienc_from_stack_t_" (U256, a) () where

instance ABITypeable a => YulBuiltInPrefix "__keccak_c_" a B32 where

