module YulDSL.Core.YulLib
  ( -- * Smart Constructors
    yulSafeCast, yulTryCast
  , yulEmb, yulNoop
  , yulIfThenElse
    -- * SimplNP
  , yulNil, yulCons
    -- * Control and Exceptions
  , yulRevert
  , yulKeccak256
  ) where
-- eth-abi
import Ethereum.ContractABI
--
import YulDSL.Core.YulBuiltIn
import YulDSL.Core.YulCat
import YulDSL.Core.YulCatObj
--
import YulDSL.StdBuiltIns.ABICodec  ()
import YulDSL.StdBuiltIns.Runtime   ()
import YulDSL.StdBuiltIns.ValueType ()



------------------------------------------------------------------------------------------------------------------------
-- Smart Constructors
------------------------------------------------------------------------------------------------------------------------

-- ^ Safe value casting.
yulSafeCast :: forall eff a b.
  (YulO2 a b, YulSafeCastable a b, IsYulBuiltInNonPure (YulSafeCastBuiltin a b) ~ False) =>
  YulCat eff a b
yulSafeCast = YulJmpB (MkYulBuiltIn @(YulSafeCastBuiltin a b) @a @b)

-- ^ Value casting with boolean for capturing casting failures.
yulTryCast :: forall eff a b.
  (YulO2 a b, YulCastable a b, IsYulBuiltInNonPure (YulCastBuiltin a b) ~ False) =>
  YulCat eff a (BOOL, b)
yulTryCast = YulJmpB (MkYulBuiltIn @(YulCastBuiltin a b) @a @(BOOL, b))

-- | Embed a constant in a yul morphism.
yulEmb :: forall eff r b. YulO2 r b => b -> YulCat eff r b
yulEmb = YulEmb

-- | Create any no-op morphisms.
yulNoop :: forall. AnyYulCat
yulNoop = MkAnyYulCat (YulDis @_ @())

-- | Helper function for if-then-else expression in yul.
yulIfThenElse :: forall eff b r. YulO2 b r =>
  YulCat eff r BOOL -> YulCat eff r b -> YulCat eff r b -> YulCat eff r b
yulIfThenElse c a b = YulFork c YulId >.> YulITE a b

-- -- | Helper function for if-then-else expression in yul.
-- yulIfThenElse :: forall eff b r. YulO2 b r =>
--   YulCat eff r BOOL -> YulCat eff r b -> YulCat eff r b -> YulCat eff r b
-- yulIfThenElse c a b = YulApply <.< YulFork (YulSwitch [(1, a), (0, b)] yulRevert) (c >.> yulSafeCast)

------------------------------------------------------------------------------------------------------------------------
-- Control and Exceptions
------------------------------------------------------------------------------------------------------------------------

-- | Revert without any message.
yulRevert :: forall eff a b. (YulO2 a b) => YulCat eff a b
yulRevert = YulDis >.> YulJmpB (MkYulBuiltIn @"__const_revert0_c_" @() @b)

-- | Wrapper for built-in keccak256 yul function.
yulKeccak256 :: forall eff a. YulO1 a => YulCat eff a B32
yulKeccak256 = YulJmpB (MkYulBuiltIn @"__keccak_c_" @a @B32)

------------------------------------------------------------------------------------------------------------------------
-- SimpleNP Utilities
------------------------------------------------------------------------------------------------------------------------

-- | Embed a NP Nil yul morphism.
yulNil :: forall eff a. YulO1 a => YulCat eff a (NP '[])
yulNil = yulEmb Nil

-- | Construct a NP yul morphism.
yulCons :: forall x xs eff r m.
  ( YulO3 x (NP xs) r
  , YulCat eff r ~ m
  ) =>
  m x -> m (NP xs) -> m (NP (x:xs))
yulCons mx mxs = YulFork mx mxs >.> YulCoerceType

-- same as (:) or (:*)
infixr 5 `yulCons`
