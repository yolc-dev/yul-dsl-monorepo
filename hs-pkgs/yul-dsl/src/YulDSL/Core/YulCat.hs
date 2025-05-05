{-# LANGUAGE AllowAmbiguousTypes    #-}
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
  , NamedYulCat, KnownNamedYulCat (withKnownNamedYulCat, classifyKnownNamedYulCat), unsafeCoerceNamedYulCat
  , YulExp
  , YulCallTarget, YulCallGasLimit, YulCallValue
  , (<.<), (>.>)
    -- * YulCat Stringify Functions
  , yulCatCompactShow, yulCatToUntypedLisp, yulCatFingerprint
  ) where
-- base
import Data.Kind                   (Constraint, Type)
import Text.Printf                 (printf)
-- bytestring
import Data.ByteString             qualified as BS
import Data.ByteString.Char8       qualified as BS_Char8
-- memory
import Data.ByteArray              qualified as BA
-- crypton
import Crypto.Hash                 qualified as Hash
-- text
import Data.Text.Lazy              qualified as T
-- eth-abi
import Ethereum.ContractABI
--
import CodeGenUtils.CodeFormatters
import YulDSL.Core.YulBuiltIn
import YulDSL.Core.YulCatObj
import YulDSL.Core.YulEffect


------------------------------------------------------------------------------------------------------------------------
-- The Cat
------------------------------------------------------------------------------------------------------------------------

-- | Use the kind signature to introduce 'YulCat' before its definition.
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
  -- ^ Unsafe coerce between different effects.
  YulUnsafeCoerceEffect :: forall {k1} {k2} (eff1 :: k1) (eff2 :: k2) a b.
    YulO2 a b =>
    YulCat eff1 a b -> YulCat eff2 a b

  -- * SMC
  --
  -- ** Category
  YulId   :: forall eff a.     YulO1 a     => YulCat eff a a
  YulComp :: forall eff a b c. YulO3 a b c => YulCat eff c b -> YulCat eff a c -> YulCat eff a b
  -- ** Monoidal Category
  YulProd :: forall eff a b c d. YulO4 a b c d => YulCat eff a b -> YulCat eff c d -> YulCat eff (a, c) (b, d)
  YulSwap :: forall eff a b.     YulO2 a b     => YulCat eff (a, b) (b, a)
  -- ** Cartesian Category
  YulFork :: forall eff a b c. YulO3 a b c => YulCat eff a b -> YulCat eff a c -> YulCat eff a (b, c)
  YulExl  :: forall eff a b.   YulO2 a b   => YulCat eff (a, b) a
  YulExr  :: forall eff a b.   YulO2 a b   => YulCat eff (a, b) b
  YulDis  :: forall eff a.     YulO1 a     => YulCat eff a ()
  YulDup  :: forall eff a.     YulO1 a     => YulCat eff a (a, a)
  -- ** Co-cartesian Category (incomplete, WIP)
  -- ^ Embed a constant value @b@ as a new yul value, the duo of "dis".
  YulEmb :: forall eff b r. YulO2 b r => b -> YulCat eff r b

  -- * Control Flow Primitives
  -- ** Structural Control Flows
  -- ^ If-then-else expression.
  YulITE :: forall eff a b.
    YulO2 a b =>
    YulCat eff a b -> YulCat eff a b -> YulCat eff (BOOL, a) b
  -- ** Call Flows
  -- ^ Jump to an user-defined morphism.
  YulJmpU :: forall eff a b.
    YulO2 a b =>
    NamedYulCat eff a b -> YulCat eff a b
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
    , AssertOmniEffect eff
    ) =>
    YulCat eff (B32, a) ()

-- | Convenience operator for left to right composition of 'YulCat'.
(>.>) :: forall eff a b c. YulO3 a b c => YulCat eff a b -> YulCat eff b c -> YulCat eff a c
m >.> n = n `YulComp` m

-- | Convenience operator for right-to-left composition of 'YulCat'.
(<.<) :: forall eff a b c. YulO3 a b c => YulCat eff b c -> YulCat eff a b -> YulCat eff a c
(<.<) = YulComp

-- ^ Same precedence as (>>>) (<<<);
-- see https://hackage.haskell.org/package/base-4.20.0.1/docs/Control-Category.html
infixr 1 >.>, <.<


-- | Yul morphisms with classified effect.
--
-- The law of sound classification:
-- @
--   withKnownNamedYulCat fn (\(_ :: NamedYulCat eff a b) -> classifyYulCatEffect @eff)
--   =
--   fromSYulCatEffectClass (yulCatEffectClassSing @efc)
--   ==
--   classifyKnownNamedYulCat @eff
-- @
class KnownYulCatEffectClass efc => KnownNamedYulCat fn (efc :: YulCatEffectClass) a b | fn -> efc a b where
  -- | Process the named YulCat morphism with its known effect enclosed within a continuation.
  withKnownNamedYulCat :: forall r.
    fn ->
    (forall k (eff :: k). KnownYulCatEffect eff => NamedYulCat eff a b -> r) ->
    r

  -- | Classify the effect of the known named YulCat morphism.
  classifyKnownNamedYulCat :: fn -> YulCatEffectClass
  classifyKnownNamedYulCat _ = fromSYulCatEffectClass (yulCatEffectClassSing @efc)

-- | Unsafely convert between yul morphisms of different effects.
unsafeCoerceNamedYulCat :: forall eff1 eff2 a b. YulO2 a b  =>
  NamedYulCat eff1 a b -> NamedYulCat eff2 a b
unsafeCoerceNamedYulCat (n, cat) = (n, YulUnsafeCoerceEffect cat)

------------------------------------------------------------------------------------------------------------------------
-- SimpleNP Instances
------------------------------------------------------------------------------------------------------------------------

--
-- TranversableNP and DistributiveNP instances
--

instance (YulO3 x (NP xs) r, YulCat eff r ~ s) =>
         ConstructibleNP (YulCat eff r) x xs Many where
  consNP sx sxs = YulCoerceType `YulComp` YulFork sx sxs
  unconsNP xxs = (x, xs)
    where xxs' = YulCoerceType `YulComp` xxs
          x    = YulExl `YulComp` xxs'
          xs   = YulExr `YulComp` xxs'

instance YulO1 r => TraversableNP (YulCat eff r) '[] where
  sequenceNP _ = Nil
instance YulO1 r => DistributiveNP (YulCat eff r) '[] where
  distributeNP _ = YulEmb Nil `YulComp` YulDis

instance (YulO3 x (NP xs) r, TraversableNP (YulCat eff r) xs) =>
         TraversableNP (YulCat eff r) (x:xs)
instance (YulO3 x (NP xs) r, DistributiveNP (YulCat eff r) xs) =>
         DistributiveNP (YulCat eff r) (x:xs)

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
    go :: YulCat eff a b -> String
    go (YulReduceType @_ @a @b)    = "Tr" <> abi_type_name2 @a @b
    go (YulExtendType @_ @a @b)    = "Te" <> abi_type_name2 @a @b
    go (YulCoerceType @_ @a @b)    = "Tc" <> abi_type_name2 @a @b
    go (YulUnsafeCoerceEffect c)   = go c
    --
    go (YulId @_ @a)               = "id" <> abi_type_name @a
    go (YulComp cb ac)             = "(" <> go ac <> ");(" <> go cb <> ")"
    --
    go (YulProd ab cd)             = "(" <> go ab <> ")×(" <> go cd <> ")"
    go (YulSwap @_ @a @b)          = "σ" <> abi_type_name2 @a @b
    --
    go (YulFork ab ac)             = "(" <> go ab <> ")▵(" <> go ac <> ")"
    go (YulExl @_ @a @b)           = "π₁" <> abi_type_name2 @a @b
    go (YulExr @_ @a @b)           = "π₂" <> abi_type_name2 @a @b
    go (YulDis @_ @a)              = "ε" <> abi_type_name @a
    go (YulDup @_ @a)              = "δ" <> abi_type_name @a
    --
    go (YulEmb @_ @b @r x)         = "{" <> show x <> "}" <> abi_type_name2 @b @r
    --
    go (YulITE a b)                = "?" <> "(" <> go a <> "):(" <> go b <> ")"
    go (YulJmpU @_ @a @b (cid, _)) = "Ju " <> cid <> abi_type_name2 @a @b
    go (YulJmpB @_ @a @b p)        = "Jb " <> yulB_fname p <> abi_type_name2 @a @b
    go (YulCall @_ @a @b sel)      = "C" <> showSelectorOnly sel <> abi_type_name2 @a @b
    --
    go (YulSGet @_ @a)             = "Sg" <> abi_type_name @a
    go (YulSPut @_ @a)             = "Sp" <> abi_type_name @a
    -- A 'abi_type_name variant, enclosing name with "@()".
    abi_type_name :: forall a. ABITypeable a => String
    abi_type_name = "@" ++ abiTypeCompactName @a
    abi_type_name2 :: forall a b. (ABITypeable a, ABITypeable b) => String
    abi_type_name2 = abi_type_name @a ++ abi_type_name @b
    -- TODO escape the value of x
    -- escape = show

yulCatToUntypedLisp :: YulCat eff a b -> Code
yulCatToUntypedLisp cat = T.pack "(" <> go init_ind cat <> T.pack ")"
  where
    go :: Indenter -> YulCat eff a b -> Code
    go _ YulReduceType               = T.empty
    go _ YulExtendType               = T.empty
    go _ YulCoerceType               = T.empty
    go ind (YulUnsafeCoerceEffect c) = go ind c
    --
    go _ YulId                       = T.empty
    go ind (YulComp cb ac)           = gcomp ind cb ac
    --
    go ind (YulProd ab cd)           = g2 ind "prod" ab cd
    go ind YulSwap                   = ind $ T.pack "swap"
    --
    go ind (YulFork ab ac)           = g2 ind "fork" ab ac
    go ind YulExl                    = ind $ T.pack "exl"
    go ind YulExr                    = ind $ T.pack "exr"
    go ind YulDis                    = ind $ T.pack "dis"
    go ind YulDup                    = ind $ T.pack "dup"
    go ind (YulEmb x)                = ind $ T.pack ("emb {" ++ show x ++ "}")
    --
    go ind (YulITE a b)              = g2 ind "bool" a b
    go ind (YulJmpU (cid, _))        = ind $ T.pack ("(jmpu " ++ cid ++ ")")
    go ind (YulJmpB p)               = ind $ T.pack ("(jmpb " ++ yulB_fname p ++ ")")
    go ind (YulCall sel)             = ind $ T.pack ("(call " ++ showSelectorOnly sel ++ ")")
    go ind YulSGet                   = ind $ T.pack "sget"
    go ind YulSPut                   = ind $ T.pack "sput"
    --
    gcomp :: forall eff' a' b' c'. Indenter -> YulCat eff' c' b' -> YulCat eff' a' c' -> Code
    gcomp ind cb ac = let c1 = go ind ac
                          c2 = go ind cb
                      in if T.null c1 || T.null c2
                         then c1 <> c2
                         else c1 <> ind (T.pack ":>.>") <> c2
    g2 :: forall eff' m n p q. Indenter -> String -> YulCat eff' m n -> YulCat eff' p q -> Code
    g2 ind op c1 c2 =
      let op' = T.pack "(" <> T.pack op
          ind' = indent ind
          s1 = go ind' c1
          s2 = go ind' c2
          result
            | T.null s1 && T.null s2 = T.empty
            | T.null s1 = ind (op' <> T.pack " id (") <> s2 <> ind (T.pack "))")
            | T.null s2 = ind (op' <> T.pack " (") <> s1 <> ind' (T.pack ") id)")
            | otherwise = ind (op' <> T.pack " (") <> s1 <> ind' (T.pack ") (") <> s2 <> ind (T.pack "))")
      in result

-- | Obtain the sha1 finger print of a 'YulCat'.
yulCatFingerprint :: YulCat eff a b -> String
yulCatFingerprint = concatMap (printf "%02x") . BS.unpack . BA.convert . hash . show
  where hash s = Hash.hash (BS_Char8.pack s) :: Hash.Digest Hash.Keccak_256

-- Deriving stock Show instances

deriving instance Show (YulCat eff a b)
deriving instance Show AnyYulCat

--
-- Num instance
--

-- ^ 'Num' instance for INTx.
instance (YulO1 r, ValidINTx s n) => Num (YulCat eff r (INTx s n)) where
  a + b = YulJmpB (MkYulBuiltIn @"__checked_add_t_") `YulComp` YulProd a b `YulComp` YulDup
  a - b = YulJmpB (MkYulBuiltIn @"__checked_sub_t_") `YulComp` YulProd a b `YulComp` YulDup
  a * b = YulJmpB (MkYulBuiltIn @"__checked_mul_t_") `YulComp` YulProd a b `YulComp` YulDup
  abs = YulComp (YulJmpB (MkYulBuiltIn @"__checked_abs_t_"))
  signum = YulComp (YulJmpB (MkYulBuiltIn @"__checked_sig_t_"))
  fromInteger a = YulEmb (fromInteger a) `YulComp` YulDis
