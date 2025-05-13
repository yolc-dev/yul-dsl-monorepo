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
  , yulFlip, yulSwitch
  , cleanYulCat
  ) where
-- base
import Data.Bifunctor         (second)
import Data.Functor.Const     (Const (Const))
import Data.Kind              (Constraint, Type)
import Data.Typeable          (Typeable)
-- eth-abi
import Ethereum.ContractABI
--
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

-- | An exponential object /b^a/ in the YulCat as a cartesian closed category.
type YulExp eff a b = a -> YulCat eff a b

-- External call parameters:

type YulCallTarget   = ADDR
type YulCallGasLimit = U256
type YulCallValue    = U256

-- | A GADT-style DSL of Yul that constructs morphisms between objects (YulCatObj) of the "Yul Category".
--
--  Note: Unlike its moniker name "Cat" may suggest, the constructors of this data type are morphisms of the Yul
--  category.
data YulCat eff a b where
  -- * Type Coercion
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

  -- * Categories
  --
  -- ** Category
  YulId   :: forall eff a.     YulO1 a     => YulCat eff a a
  YulComp :: forall eff a b c. YulO3 a b c => YulCat eff c b -> YulCat eff a c -> YulCat eff a b
  -- ** Symmetric Monoidal Category
  YulProd :: forall eff a b c d. YulO4 a b c d => YulCat eff a b -> YulCat eff c d -> YulCat eff (a ⊗ c) (b ⊗ d)
  YulSwap :: forall eff a b.     YulO2 a b     => YulCat eff (a ⊗ b) (b ⊗ a)
  -- ** Cartesian Category
  YulFork :: forall eff a b c. YulO3 a b c => YulCat eff a b -> YulCat eff a c -> YulCat eff a (b ⊗ c)
  YulExl  :: forall eff a b.   YulO2 a b   => YulCat eff (a ⊗ b) a
  YulExr  :: forall eff a b.   YulO2 a b   => YulCat eff (a ⊗ b) b
  YulDis  :: forall eff a.     YulO1 a     => YulCat eff a ()
  YulDup  :: forall eff a.     YulO1 a     => YulCat eff a (a ⊗ a)
  -- ** Cartesian Closed
  YulApply :: forall eff a b.   YulO2 a b   => YulCat eff (YulExp eff a b ⊗ a) b
  YulCurry :: forall eff a b c. YulO3 a b c => YulCat eff (a ⊗ b) c -> YulCat eff a (YulExp eff b c)
  -- ** Co-cartesian: Create New Objects (duo of "dis"; but with "r" inlined for convenience.)
  --
  -- ^ Embed a constant value @b@ as a new yul value, the duo of "dis" ().
  YulEmb :: forall eff b r. YulO2 b r => b -> YulCat eff r b
  -- ^ Embed a dynamic value @k b@ which can be used by the evaluator.
  YulDyn :: forall eff c b r. (Typeable c, Show (c b), YulO2 b r) => c b -> YulCat eff r b

  -- * Control Flow Primitives
  --
  -- ** Structural Control Flows
  --
  -- ^ Map a haskell function between two yul morphisms: /r ~> a -> r ~> b/ to an curriable object /r⊗a ~> b/.
  YulMapHask :: forall eff a b r.
    YulO3 a b r =>
    (YulCat eff r a -> YulCat eff r b) ->
    YulCat eff (r ⊗ a) b
  -- ^ Switch expression.
  YulSwitch :: forall eff a b.
    YulO2 a b =>
    YulCat eff a U256 ->        -- ^ case function
    [(U256, YulCat eff a b)] -> -- ^ switch cases
    YulCat eff a b ->           -- ^ default case
    YulCat eff a b
  -- ** Call Flows
  --
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

-- | Flip domains of an exponential object: c ~> a -> b => a ~> c -> b
yulFlip :: forall eff a b c.
  YulO3 a b c =>
  (YulCat eff c a -> YulCat eff c b) ->
  YulCat eff a (YulExp eff c b)
yulFlip g = YulCurry (YulMapHask \ac -> YulApply <.< YulFork (ac >.> YulCurry (YulMapHask g)) YulId)

-- | Build a YulSwitch through object-wise haskell functions.
yulSwitch :: forall eff a b r.
  YulO3 a b r =>
  (YulCat eff r a -> YulCat eff r U256) ->        -- ^ case function
  [(U256, YulCat eff r a -> YulCat eff r b)] ->   -- ^ switch cases
  (YulCat eff r a -> YulCat eff r b) ->           -- ^ default case
  YulCat eff r (YulExp eff a b)
yulSwitch cf cs cdef = YulCurry (YulMapHask \ra -> YulSwitch (cf ra) (fmap (\(i, c) -> (i, c ra)) cs) (cdef ra))

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
-- Exponential Object as YulCatObj
------------------------------------------------------------------------------------------------------------------------

instance YulO2 a b => Show (YulExp eff a b) where
  show _ = abiTypeCanonName @b ++ "^" ++ abiTypeCanonName @a

instance ABITypeable (YulExp eff a b) where
  type instance ABITypeDerivedOf (YulExp eff a b) = B32
  abiDefault = error "cannot instantiate exponential object"
  abiToCoreType _ = error "cannot instantiate exponential object"
  abiFromCoreType = error "cannot instantiate exponential object"

instance ABITypeCodec (YulExp eff a b)
instance YulO2 a b => YulCatObj (YulExp eff a b)

------------------------------------------------------------------------------------------------------------------------
-- SimpleNP Instances
------------------------------------------------------------------------------------------------------------------------

--
-- TranversableNP and DistributiveNP instances
--

instance (YulO3 x (NP xs) r, YulCat eff r ~ s) =>
         ConstructibleNP (YulCat eff r) x xs Many where
  consNP sx sxs = YulFork sx sxs >.> YulCoerceType
  unconsNP xxs = (x, xs)
    where xxs' = YulCoerceType <.< xxs
          x    = YulExl <.< xxs'
          xs   = YulExr <.< xxs'

instance YulO1 r => TraversableNP (YulCat eff r) '[] where
  sequenceNP _ = Nil
instance YulO1 r => DistributiveNP (YulCat eff r) '[] where
  distributeNP _ = YulEmb Nil <.< YulDis

instance (YulO3 x (NP xs) r, TraversableNP (YulCat eff r) xs) =>
         TraversableNP (YulCat eff r) (x:xs)
instance (YulO3 x (NP xs) r, DistributiveNP (YulCat eff r) xs) =>
         DistributiveNP (YulCat eff r) (x:xs)

------------------------------------------------------------------------------------------------------------------------
-- Base Library Instances
------------------------------------------------------------------------------------------------------------------------

--
-- Show instance
--

-- | Clean the yul cat from recursions for its show instance.
cleanYulCat :: YulCat eff a b -> YulCat eff a b
cleanYulCat = go
  where
    go :: YulCat eff a b -> YulCat eff a b
    go (YulUnsafeCoerceEffect cat) = YulUnsafeCoerceEffect (go cat)
    go (YulComp cb ac)             = YulComp (go cb) (go ac)
    go (YulProd ab cd)             = YulProd (go ab) (go cd)
    go (YulFork ab ac)             = YulFork (go ab) (go ac)
    go (YulCurry ab2c)             = YulCurry (go ab2c)
    go (YulSwitch cf cs cdef)      = YulSwitch (go cf) (map (second go) cs) (go cdef)
    go (YulJmpU (name, _))         = YulJmpU (name, YulDyn (Const ()))
    go cat                         = cat

-- ^ Visualizing a exponential object using a placeholder of Const functor value.
instance YulO2 r a => Show (YulCat eff r a -> YulCat eff r b) where
  show f = show (f (YulDyn (Const ())))
deriving instance Show (YulCat eff a b)
deriving instance Show AnyYulCat

--
-- Num instance
--

-- ^ 'Num' instance for INTx.
instance (YulO1 r, ValidINTx s n) => Num (YulCat eff r (INTx s n)) where
  a + b = YulJmpB (MkYulBuiltIn @"__checked_add_t_") <.< YulProd a b <.< YulDup
  a - b = YulJmpB (MkYulBuiltIn @"__checked_sub_t_") <.< YulProd a b <.< YulDup
  a * b = YulJmpB (MkYulBuiltIn @"__checked_mul_t_") <.< YulProd a b <.< YulDup
  abs = YulComp (YulJmpB (MkYulBuiltIn @"__checked_abs_t_"))
  signum = YulComp (YulJmpB (MkYulBuiltIn @"__checked_sig_t_"))
  fromInteger a = YulEmb (fromInteger a) <.< YulDis
