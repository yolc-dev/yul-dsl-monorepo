{-# LANGUAGE LinearTypes #-}
module YulDSL.Core.YulLib
  ( -- * SimplNP
    yulNil, yulCons
    -- * Control and Exceptions
  , yulNoop
  , yulIfThenElse
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
-- Control and Exceptions
------------------------------------------------------------------------------------------------------------------------

-- | No-op pure morphism.
yulNoop :: AnyYulCat
yulNoop = MkAnyYulCat (YulDis @_ @())

-- | Helper function for 'YulITE'.
yulIfThenElse :: forall eff a r. YulO2 a r =>
  YulCat eff r BOOL %1 -> YulCat eff r a %1 -> YulCat eff r a %1 -> YulCat eff r a
yulIfThenElse c a b = YulFork c YulId >.> YulITE a b

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
yulNil = YulEmb Nil

-- | Construct a NP yul morphism.
yulCons :: forall x xs eff r m.
  ( YulO3 x (NP xs) r
  , YulCat eff r ~ m
  ) =>
  m x -> m (NP xs) -> m (NP (x:xs))
yulCons mx mxs = YulFork mx mxs >.> YulCoerceType

-- same as (:) or (:*)
infixr 5 `yulCons`
