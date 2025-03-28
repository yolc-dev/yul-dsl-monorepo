{-# LANGUAGE LinearTypes #-}
module YulDSL.Core.YulLib
  ( -- * Smart Constructors
    (<.<), (>.>)
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
import YulDSL.StdBuiltIns.Exception ()

------------------------------------------------------------------------------------------------------------------------
-- Smart Constructors
------------------------------------------------------------------------------------------------------------------------

-- | Convenience operator for left to right composition of 'YulCat'.
(>.>) :: forall eff a b c. YulO3 a b c => YulCat eff a b %1-> YulCat eff b c %1-> YulCat eff a c
m >.> n = n `YulComp` m

-- | Convenience operator for right-to-left composition of 'YulCat'.
(<.<) :: forall eff a b c. YulO3 a b c => YulCat eff b c %1-> YulCat eff a b %1-> YulCat eff a c
(<.<) = YulComp

-- ^ Same precedence as (>>>) (<<<);
-- see https://hackage.haskell.org/package/base-4.20.0.1/docs/Control-Category.html
infixr 1 >.>, <.<

-- | Embed a constant in a yul morphism.
yulEmb :: forall eff a b. YulO2 a b => b -> YulCat eff a b
yulEmb b = YulDis >.> YulEmb b

-- | Create any no-op morphisms.
yulNoop :: forall. AnyYulCat
yulNoop = MkAnyYulCat (YulDis @_ @())

-- | Helper function for 'YulITE'.
yulIfThenElse :: forall eff a r. YulO2 a r =>
  YulCat eff r BOOL %1 -> YulCat eff r a %1 -> YulCat eff r a %1 -> YulCat eff r a
yulIfThenElse c a b = YulFork c YulId >.> YulITE a b

------------------------------------------------------------------------------------------------------------------------
-- Control and Exceptions
------------------------------------------------------------------------------------------------------------------------

-- | Revert without any message.
yulRevert :: forall eff a b. (YulO2 a b) => YulCat eff a b
yulRevert = YulDis >.> YulJmpB (MkYulBuiltIn @"__const_revert0_c_" @() @b)

-- | Wrapper for built-in keccak256 yul function.
yulKeccak256 :: forall eff a r. YulO2 r a => YulCat eff r a -> YulCat eff r B32
yulKeccak256 x = x >.> YulJmpB (MkYulBuiltIn @"__keccak_c_" @a @B32)

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
