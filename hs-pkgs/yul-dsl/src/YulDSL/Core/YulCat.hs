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
    YulCat (..), NamedYulCat, AnyYulCat (..)
    -- * YulCat Function Forms: Y and Fn
  , Y
  , NamedYulCatNP, Fn (MkFn, unFn), ClassifiedFn (withClassifiedFn), unsafeCoerceFn
  , ExternalFn (MkExternalFn), declareExternalFn
  -- * YulCat Stringify Functions
  , yulCatCompactShow, yulCatToUntypedLisp, yulCatFingerprint
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

-- | Named YulCat morphism.
type NamedYulCat eff a b = (String, YulCat eff a b)

-- | Existential wrapper of the 'YulCat'.
data AnyYulCat = forall eff a b. (YulO2 a b) => MkAnyYulCat (YulCat eff a b)

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
  YulEmb :: forall eff b. YulO1 b => b %1-> YulCat eff () b
  -- ^ If-then-else expression.
  YulITE :: forall eff a b. YulO2 a b => YulCat eff a b %1-> YulCat eff a b %1-> YulCat eff (BOOL, a) b
  -- ^ Jump to an user-defined morphism.
  YulJmpU :: forall eff a b. YulO2 a b => NamedYulCat eff a b %1-> YulCat eff a b
  -- ^ Jump to a built-in yul function.
  YulJmpB :: forall eff a b p.
    ( YulO2 a b, YulBuiltInPrefix p a b
    , If (IsYulBuiltInNonPure p) (AssertNonPureEffect eff) (() :: Constraint)
    ) =>
    YulBuiltIn p a b -> YulCat eff a b
  -- ^ Call an external contract at the address along with a possible msgValue.
  YulCall :: forall eff a b. (YulO2 a b, AssertNonPureEffect eff) =>
    SELECTOR -> YulCat eff ((ADDR, U256), a) b
  -- TODO: YulSCall
  -- TODO: YulDCall

  -- * Storage Primitives
  --
  -- ^ Get storage word.
  YulSGet :: forall eff a. (YulO1 a, AssertNonPureEffect eff, ABIWordValue a) => YulCat eff B32 a
  -- ^ Put storage word.
  YulSPut :: forall eff a. (YulO1 a, AssertNonPureEffect eff, ABIWordValue a) => YulCat eff (B32, a) ()

  -- ^ Unsafe coerce between different effects.
  YulUnsafeCoerceEffect :: forall k1 k2 (eff1 :: k1) (eff2 :: k2) a b. YulO2 a b =>
    YulCat eff1 a b %1-> YulCat eff2 a b

------------------------------------------------------------------------------------------------------------------------
-- YulCat Function Forms: Y and Fn
------------------------------------------------------------------------------------------------------------------------

-- | 'YulCat' n-ary function form, with each morphism on the arrow sharing the same domain @a@.
type Y eff f = forall a. YulO1 a => LiftFunction f (YulCat eff a) (YulCat eff a) Many

-- | Named YulCat morphism with its domain in @NP xs@.
type NamedYulCatNP eff xs b = NamedYulCat eff (NP xs) b

-- | 'Fn' is a 'NamedYulCatNP' wrapper with a function signature @f@.
data Fn eff f where
  MkFn :: forall k (eff :: k) f xs b.
    ( EquivalentNPOfFunction f xs b
    , YulO2 (NP xs) b
    ) =>
    { unFn :: NamedYulCatNP eff (UncurryNP'Fst f) (UncurryNP'Snd f) } ->
    Fn eff f

-- | YulCat Fn with classified effect.
class ClassifiedFn fn (efc :: YulCatEffectClass) | fn -> efc where
  -- | Process the classified YulCat Fn with a continuation.
  withClassifiedFn :: forall f r. (forall k (eff :: k). KnownYulCatEffect eff => Fn eff f -> r) %1-> fn f -> r

-- | Unsafely convert between yul functions of different effects.
unsafeCoerceFn :: forall eff1 eff2 f xs b.
  ( EquivalentNPOfFunction f xs b
  , YulO2 b (NP xs)
  ) =>
  Fn eff1 f -> Fn eff2 f
unsafeCoerceFn f = let (n, cat) = unFn f in MkFn (n, YulUnsafeCoerceEffect cat)

-- TODO: removed

-- | External contract functions that can be called via its selector.
data ExternalFn f where
  MkExternalFn :: forall f xs b. EquivalentNPOfFunction f xs b => SELECTOR -> ExternalFn f

-- | Create a 'ExternalFn' value by providing its function name function form @f@.
declareExternalFn :: forall f xs b.
                     ( EquivalentNPOfFunction f xs b
                     , YulO2 (NP xs) b
                     )
                  => String -> ExternalFn f
declareExternalFn fname = MkExternalFn (mkTypedSelector @(NP xs) fname)


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

--
-- UncurriableNP instances
--

-- ^ Base case: @uncurryingNP (x) => NP '[] -> x@
instance forall b r eff.
         ( YulO2 b r
         , EquivalentNPOfFunction b '[] b
         , LiftFunction b (YulCat eff r) (YulCat eff r) Many ~ YulCat eff r b
         ) =>
         UncurriableNP b '[] b (YulCat eff r) (YulCat eff r) (YulCat eff r) (YulCat eff r) Many where
  uncurryNP b _ = b

-- ^ Inductive case: @uncurryingNP (x -> ...xs -> b) => (x, uncurryingNP (... xs -> b)) => NP (x:xs) -> b@
instance forall g x xs b r eff.
         ( YulO4 x (NP xs) b r
         , UncurriableNP g xs b (YulCat eff r) (YulCat eff r) (YulCat eff r) (YulCat eff r) Many
         ) =>
         UncurriableNP (x -> g) (x:xs) b (YulCat eff r) (YulCat eff r) (YulCat eff r) (YulCat eff r) Many where
  uncurryNP f xxs = let (x, xs) = unconsNP xxs in uncurryNP @g @xs @b @(YulCat eff r) @(YulCat eff r) (f x) xs

--
-- CurriableNP instances
--

-- ^ Base case: @curryingNP (NP '[] -> b) => b@
instance forall b r eff.
         ( YulO2 b r
         , EquivalentNPOfFunction b '[] b
         , LiftFunction b (YulCat eff r) (YulCat eff r) Many ~ YulCat eff r b
         ) =>
         CurriableNP b '[] b (YulCat eff r) (YulCat eff r) (YulCat eff r) Many where
  curryNP fNP = fNP (YulReduceType `YulComp` YulDis)

-- ^ Inductive case: @curryingNP (NP (x:xs) -> b) => x -> curryingNP (NP xs -> b)@
instance forall g x xs b r eff.
         ( YulO5 x (NP xs) b (NP (x:xs)) r
         , CurriableNP g xs b (YulCat eff r) (YulCat eff r) (YulCat eff r) Many
         ) =>
         CurriableNP (x -> g) (x:xs) b (YulCat eff r) (YulCat eff r) (YulCat eff r) Many where
  curryNP fNP x = curryNP @g @xs @b @(YulCat eff r) @(YulCat eff r) (fNP . consNP x)

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
    go (YulReduceType @_ @a @b)    = "Tr" <> abi_type_name2 @a @b
    go (YulExtendType @_ @a @b)    = "Te" <> abi_type_name2 @a @b
    go (YulCoerceType @_ @a @b)    = "Tc" <> abi_type_name2 @a @b
    --
    go (YulId @_ @a)               = "id" <> abi_type_name @a
    go (YulComp cb ac)             = "(" <> go ac <> ");(" <> go cb <> ")"
    go (YulProd ab cd)             = "(" <> go ab <> ")×(" <> go cd <> ")"
    go (YulSwap @_ @a @b)          = "σ" <> abi_type_name2 @a @b
    go (YulFork ab ac)             = "(" <> go ab <> ")▵(" <> go ac <> ")"
    go (YulExl @_ @a @b)           = "π₁" <> abi_type_name2 @a @b
    go (YulExr @_ @a @b)           = "π₂" <> abi_type_name2 @a @b
    go (YulDis @_ @a)              = "ε" <> abi_type_name @a
    go (YulDup @_ @a)              = "δ" <> abi_type_name @a
    --
    go (YulEmb @_ @b x)            = "{" <> show x <> "}" <> abi_type_name @b
    go (YulITE a b)                = "?" <> "(" <> go a <> "):(" <> go b <> ")"
    go (YulJmpU @_ @a @b (cid, _)) = "Ju " <> cid <> abi_type_name2 @a @b
    go (YulJmpB @_ @a @b p)        = "Jb " <> yulB_fname p <> abi_type_name2 @a @b
    go (YulCall @_ @a @b sel)      = "C" <> showSelectorOnly sel <> abi_type_name2 @a @b
    --
    go (YulSGet @_ @a)             = "Sg" <> abi_type_name @a
    go (YulSPut @_ @a)             = "Sp" <> abi_type_name @a
    --
    go (YulUnsafeCoerceEffect c)   = go c
    -- A 'abi_type_name variant, enclosing name with "@()".
    abi_type_name :: forall a. ABITypeable a => String
    abi_type_name = "@" ++ abiTypeCompactName @a
    abi_type_name2 :: forall a b. (ABITypeable a, ABITypeable b) => String
    abi_type_name2 = abi_type_name @a ++ abi_type_name @b
    -- TODO escape the value of x
    -- escape = show

yulCatToUntypedLisp :: forall eff a b. YulCat eff a b -> Code
yulCatToUntypedLisp = go init_ind
  where
    go :: forall eff' a' b'. Indenter -> YulCat eff' a' b' -> Code
    go _ YulReduceType               = T.empty
    go _ YulExtendType               = T.empty
    go _ YulCoerceType               = T.empty
    --
    go _ YulId                       = T.empty
    go ind (YulComp cb ac)           = gcomp ind cb ac
    go ind (YulProd ab cd)           = g2 ind "prod" ab cd
    go ind YulSwap                   = ind $ T.pack "swap"
    go ind (YulFork ab ac)           = g2 ind "fork" ab ac
    go ind YulExl                    = ind $ T.pack "exl"
    go ind YulExr                    = ind $ T.pack "exr"
    go ind YulDis                    = ind $ T.pack "dis"
    go ind YulDup                    = ind $ T.pack "dup"
    go ind (YulEmb x)                = ind $ T.pack (show x)
    go ind (YulITE a b)              = g2 ind "ite" a b
    go ind (YulJmpU (cid, _))        = ind $ T.pack ("(jmpu " ++ cid ++ ")")
    go ind (YulJmpB p)               = ind $ T.pack ("(jmpb " ++ yulB_fname p ++ ")")
    go ind (YulCall sel)             = ind $ T.pack ("(call " ++ showSelectorOnly sel ++ ")")
    go ind YulSGet                   = ind $ T.pack "sget"
    go ind YulSPut                   = ind $ T.pack "sput"
    go ind (YulUnsafeCoerceEffect c) = go ind c
    --
    gcomp :: forall eff' a' b' c'. Indenter -> YulCat eff' c' b' -> YulCat eff' a' c' -> Code
    gcomp ind cb ac = let c1 = go ind ac
                          c2 = go ind cb
                      in if T.null c1 || T.null c2
                         then c1 <> c2
                         else c1 <> ind (T.pack ";;") <> c2
    g2 :: forall eff' m n p q. Indenter -> String -> YulCat eff' m n -> YulCat eff' p q -> Code
    g2 ind op c1 c2 =
      let op' = T.pack "(" <> T.pack op
          ind' = indent ind
          s1 = go ind' c1
          s2 = go ind' c2
      in if T.null s1 && T.null s2
         then T.empty
         else if T.null s1
              then ind (op' <> T.pack " id (") <> s2 <> ind (T.pack "))")
              else if T.null s2
                   then ind (op' <> T.pack " (") <> s1 <> ind' (T.pack ") id)")
                   else ind (op' <> T.pack " (") <> s1 <> ind' (T.pack ") (") <> s2 <> ind (T.pack "))")

-- | Obtain the sha1 finger print of a 'YulCat'.
yulCatFingerprint :: YulCat eff a b -> String
yulCatFingerprint = concatMap (printf "%02x") . BS.unpack . BA.convert . hash . show
  where hash s = Hash.hash (BS_Char8.pack s) :: Hash.Digest Hash.Keccak_256

instance Show (YulCat eff a b) where show = yulCatCompactShow
deriving instance Show AnyYulCat
deriving instance Show (Fn eff f)

--
-- Num Instance
--

-- ^ 'Num' instance for INTx.
instance (YulO1 r, ValidINTx s n) => Num (YulCat eff r (INTx s n)) where
  a + b = YulJmpB (MkYulBuiltIn @"__checked_add_t_") `YulComp` YulProd a b `YulComp` YulDup
  a - b = YulJmpB (MkYulBuiltIn @"__checked_sub_t_") `YulComp` YulProd a b `YulComp` YulDup
  a * b = YulJmpB (MkYulBuiltIn @"__checked_mul_t_") `YulComp` YulProd a b `YulComp` YulDup
  abs = YulComp (YulJmpB (MkYulBuiltIn @"__checked_abs_t_"))
  signum = YulComp (YulJmpB (MkYulBuiltIn @"__checked_sig_t_"))
  fromInteger a = YulEmb (fromInteger a) `YulComp` YulDis
