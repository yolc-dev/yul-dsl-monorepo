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
  , YulCallTarget, YulCallGasLimit, YulCallValue
  , NamedYulCat, ClassifiedYulCat (withClassifiedYulCat)
  -- * YulCat Stringify Functions
  , yulCatCompactShow, yulCatFingerprint
  ) where
-- base
import Data.Kind                    (Constraint, Type)
import Text.Printf                  (printf)
-- bytestring
import Data.ByteString              qualified as BS
import Data.ByteString.Char8        qualified as BS_Char8
-- memory
import Data.ByteArray               qualified as BA
-- crypton
import Crypto.Hash                  qualified as Hash
-- text
import Data.Text.Lazy               qualified as T
-- eth-abi
import Ethereum.ContractABI
--
import CodeGenUtils.CodeFormatters
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

type YulCallTarget   = ADDR
type YulCallGasLimit = U256
type YulCallValue    = U256

-- | A GADT-style DSL of Yul that constructs morphisms between objects (YulCatObj) of the "Yul Category".
--
--  Note: Unlike its moniker name "Cat" may suggest, the constructors of this data type are morphisms of the Yul
--  category.
data YulCat eff a b where
  -- * Type Conversions
  --
  -- ^ Convert from extended yul object to its core yul object.
  YulReduceType :: forall eff a b. (YulO2 a b, ABITypeDerivedOf a ~ b) => YulCat eff a b
  -- ^ Extend core yul object type.
  YulExtendType :: forall eff a b. (YulO2 a b, a ~ ABITypeDerivedOf b) => YulCat eff a b
  -- ^ Convert between coercible yul objects.
  YulCoerceType :: forall eff a b. (YulO2 a b, ABITypeCoercible a b) => YulCat eff a b

  -- * SMC
  --
  -- ** Category
  YulId   :: forall eff a.     YulO2 a a   => YulCat eff a a
  YulComp :: forall eff a b c. YulO3 a b c => YulCat eff c b %1-> YulCat eff a c %1-> YulCat eff a b
  -- ** Monoidal Category
  YulProd :: forall eff a b c d. YulO4 a b c d => YulCat eff a b %1-> YulCat eff c d %1-> YulCat eff (a, c) (b, d)
  YulSwap :: forall eff a b.     YulO2 a b     => YulCat eff (a, b) (b, a)
  -- ** Cartesian Category
  YulFork :: forall eff a b c. YulO3 a b c => YulCat eff a b %1-> YulCat eff a c %1-> YulCat eff a (b, c)
  YulExl  :: forall eff a b.   YulO2 a b   => YulCat eff (a, b) a
  YulExr  :: forall eff a b.   YulO2 a b   => YulCat eff (a, b) b
  YulDis  :: forall eff a. YulO1 a => YulCat eff a ()
  YulDup  :: forall eff a. YulO1 a => YulCat eff a (a, a)

  -- * Control Flow Primitives
  --
  -- ^ Embed a constant value @b@ and disregard any input object @a@.
  YulEmb :: forall eff b.
    YulO1 b =>
    b %1-> YulCat eff () b
  -- ^ If-then-else expression.
  YulITE :: forall eff a b.
    YulO2 a b =>
    YulCat eff a b %1-> YulCat eff a b %1-> YulCat eff (BOOL, a) b
  -- ^ Jump to an user-defined morphism.
  YulJmpU :: forall eff a b.
    YulO2 a b =>
    NamedYulCat eff a b %1-> YulCat eff a b
  -- ^ Jump to a built-in yul function.
  YulJmpB :: forall eff a b p.
    ( YulO2 a b, YulBuiltInPrefix p a b
    , If (IsYulBuiltInNonPure p) (AssertNonPureEffect eff) (() :: Constraint)
    ) =>
    YulBuiltIn p a b -> YulCat eff a b
  -- ^ Call an external contract at the address along with a possible msgValue.
  YulCall :: forall eff a b.
    ( YulO2 a b
    , AssertNonPureEffect eff
    ) =>
    SELECTOR -> YulCat eff ((YulCallTarget, YulCallValue, YulCallGasLimit), a) b

  -- * Storage Primitives
  --
  -- ^ Get storage word.
  YulSGet :: forall eff a.
    ( YulO1 a, ABIWordValue a
    , AssertNonPureEffect eff
    ) =>
    YulCat eff B32 a
  -- ^ Put storage word.
  YulSPut :: forall eff a.
    ( YulO1 a, ABIWordValue a
    , AssertNonPureEffect eff
    ) =>
    YulCat eff (B32, a) ()

  -- ^ Unsafe coerce between different effects.
  YulUnsafeCoerceEffect :: forall k1 k2 (eff1 :: k1) (eff2 :: k2) a b.
    YulO2 a b =>
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
    go (YulExtendType @_ @a @b)    = "Te" <> abi_type_name2 @a @b
    go (YulComp cb ac)             = "(" <> go ac <> ");(" <> go cb <> ")"
    go (YulEmb @_ @b x)            = "{"
    go (YulJmpU @_ @a @b (cid, _)) = "Ju "
    go (YulJmpB @_ @a @b p)        = "Jb "
    go (YulCall @_ @a @b sel)      = "C"
    go (YulUnsafeCoerceEffect c)   = go c
    go _ = error "a"
    -- A 'abi_type_name variant, enclosing name with "@()".
    abi_type_name :: forall a. ABITypeable a => String
    abi_type_name = "@" ++ abiTypeCompactName @a
    abi_type_name2 :: forall a b. (ABITypeable a, ABITypeable b) => String
    abi_type_name2 = abi_type_name @a ++ abi_type_name @b
    -- TODO escape the value of x
    -- escape = show

-- | Obtain the sha1 finger print of a 'YulCat'.
yulCatFingerprint :: YulCat eff a b -> String
yulCatFingerprint = concatMap (printf "%02x") . BS.unpack . BA.convert . hash . show
  where hash s = Hash.hash (BS_Char8.pack s) :: Hash.Digest Hash.Keccak_256

instance Show (YulCat eff a b) where show = yulCatCompactShow
deriving instance Show AnyYulCat
