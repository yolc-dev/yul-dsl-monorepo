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
    YulCat (..), AnyYulCat (..)
  , NamedYulCat, ClassifiedYulCat (withClassifiedYulCat)
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
import YulDSL.Core.YulEffect
import YulDSL.StdBuiltIns.ValueType ()


------------------------------------------------------------------------------------------------------------------------
-- The Cat
------------------------------------------------------------------------------------------------------------------------

-- | Use kind signature for the 'YulCat' to introduce the terminology in a lexical-orderly way.
type YulCat :: forall effKind. effKind -> Type -> Type -> Type

-- | Existential wrapper of the 'YulCat'.
data AnyYulCat = forall eff a b. (YulO2 a b) => MkAnyYulCat (YulCat eff a b)

-- | Named YulCat morphism.
type NamedYulCat eff a b = (String, YulCat eff a b)

--  Note: Unlike its moniker name "Cat" may suggest, the constructors of this data type are morphisms of the Yul
--  category.
data YulCat eff a b where
  -- * Type Conversions
  --
  YulExtendType :: forall eff a b. (YulO2 a b, a ~ ABITypeDerivedOf b) => YulCat eff a b
  -- ^ Convert between coercible yul objects.
  YulCoerceType :: forall eff a b. (YulO2 a b, ABITypeCoercible a b) => YulCat eff a b

  -- * SMC
  --
  -- ** Category
  YulId   :: forall eff a.      YulCat eff a a
  YulComp :: forall eff a b c.  YulCat eff c b %1-> YulCat eff a c %1-> YulCat eff a b
  -- ** Monoidal Category
  YulProd :: forall eff a b c d.  YulCat eff a b %1-> YulCat eff c d %1-> YulCat eff (a, c) (b, d)
  YulSwap :: forall eff a b.      YulCat eff (a, b) (b, a)

  -- * Control Flow Primitives
  --
  -- ^ Embed a constant value @b@ and disregard any input object @a@.
  YulJmpB :: forall eff a b p.
    ( YulO2 a b, YulBuiltInPrefix p a b
    , If (IsYulBuiltInNonPure p) (AssertNonPureEffect eff) (() :: Constraint)
    ) =>
    YulBuiltIn p a b -> YulCat eff a b
  -- ^ Call an external contract at the address along with a possible msgValue.
  -- * Storage Primitives
  --

  -- ^ Unsafe coerce between different effects.
  YulUnsafeCoerceEffect :: forall k1 k2 (eff1 :: k1) (eff2 :: k2) a b.
    YulCat eff1 a b %1-> YulCat eff2 a b

-- | Yul morphisms with classified effect.
class ClassifiedYulCat fn (efc :: YulCatEffectClass) a b | fn -> efc a b where
  -- | Process the named YulCat morphism with its classified effect enclosed within a continuation.
  --
  -- The law of sound classification:
  -- @ fromSYulCatEffectClass (yulCatEffectClassSing @efc) == classifyYulCatEffect @eff @
  withClassifiedYulCat :: forall r.
    fn ->
    (forall k (eff :: k). NamedYulCat eff a b -> r) %1->
    r



------------------------------------------------------------------------------------------------------------------------
-- Base Library Instances
------------------------------------------------------------------------------------------------------------------------

--
-- YulCat Stringify Functions and Show Instance
--

-- | Compact and unique representation of 'YulCat', which can be used for generate its fingerprint.
--
--   Note:
--   * It is done so for the compactness of the string representation of the 'YulCat'.
yulCatCompactShow :: YulCat eff a b -> String
yulCatCompactShow = go
  where
    go :: YulCat eff' a' b' -> String
    go (YulExtendType @_ @a @b)    = "Te" <> abi_type_name @b
    go (YulComp cb ac)             = "(" <> go ac <> ");(" <> go cb <> ")"
    go (YulJmpB @_ @a @b p)        = "Jb "
    go (YulUnsafeCoerceEffect c)   = go c
    go _ = error "no segfault"
    -- A 'abi_type_name variant, enclosing name with "@()".
    abi_type_name :: forall a. ABITypeable a => String
    abi_type_name = abiTypeCompactName @a


instance Show (YulCat eff a b) where show = yulCatCompactShow
deriving instance Show AnyYulCat
