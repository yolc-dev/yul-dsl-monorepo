{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LinearTypes            #-}
{-|
Copyright   : (c) 2023-2025 Miao, ZhiCheng
License     : LGPL-3
Maintainer  : hellwolf@yolc.dev
Stability   : experimental

= Description

[Yul](https://docs.soliditylang.org/en/latest/yul.html) is an intermediate language that is part of the [solidity
compiler](https://docs.soliditylang.org/en/latest/). It is by-design aspiring to be compiled to bytecode for different
backends, while at the moment it is for [Ethereum Virtual Machine](https://ethereum.org/en/developers/docs/evm/) (EVM).

This module provides an "Embedded (in Haskell) Domain Specific Language" (eDSL) for programming in Yul, called 'YulCat'.

YulCat is based on category theory. The objects in this category are instances of 'YulCatObj'.

Further more, the 'YulCat' is instantiated as a "Symmetric Monoidal Category" (SMC). Being a SMC enables the possibility
for compiling linearly-typed functions in Haskell directly to the 'YulCat', where linear-types can provide additional
safety to the practice of EVM programming.

-}
module YulDSL.Core.YulCat
  ( -- * YulCat, the Categorical DSL of Yul
    YulCat (..)
  -- * YulCat Stringify Functions
  , yulCatCompactShow
  ) where
-- base
import Data.Kind                    (Constraint, Type)
-- bytestring
-- memory
-- crypton
-- text
-- eth-abi
import Ethereum.ContractABI
--
import YulDSL.Core.YulBuiltIn
import YulDSL.Core.YulCatObj
import YulDSL.StdBuiltIns.ValueType ()


------------------------------------------------------------------------------------------------------------------------
-- The Cat
------------------------------------------------------------------------------------------------------------------------

-- | Use kind signature for the 'YulCat' to introduce the terminology in a lexical-orderly way.
type YulCat :: forall effKind. effKind -> Type -> Type -> Type

data YulCat eff a b where
  YulExtendType :: forall eff a b. (YulO2 a b, a ~ ABITypeDerivedOf b) => YulCat eff a b
  YulComp :: forall eff a b c.  YulCat eff c b %1-> YulCat eff a c %1-> YulCat eff a b
  YulJmpB :: forall eff a b p.
    ( YulO2 a b, YulBuiltInPrefix p a b
    ) =>
    YulBuiltIn p a b -> YulCat eff a b



yulCatCompactShow :: YulCat eff a b -> String
yulCatCompactShow = go
  where
    go :: YulCat eff' a' b' -> String
    go (YulExtendType @_ @a @b)    = "Te" <> abi_type_name @b
    go (YulComp cb ac)             = "(" <> go ac <> ");(" <> go cb <> ")"
    go (YulJmpB @_ @a @b p)        = "Jb "
    go _ = error "no segfault"
    -- A 'abi_type_name variant, enclosing name with "@()".
    abi_type_name :: forall a. ABITypeable a => String
    abi_type_name = abiTypeCompactName @a


