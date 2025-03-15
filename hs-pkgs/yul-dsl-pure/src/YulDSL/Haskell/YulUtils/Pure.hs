{-# LANGUAGE LinearTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module YulDSL.Haskell.YulUtils.Pure
  -- * YulDSL/Haskell's pure effect support
  ( module YulDSL.Haskell.Effects.Pure
  -- * Extra YulCat Helpers
  , yulNil, yulCons
  , yulKeccak256
  , yulRevert
  -- * YulCat Control Flows
  , module Control.IfThenElse
  , module Control.PatternMatchable
  -- * Extra Yul Object Helpers
  , emptyCtor
  ) where
-- eth-abi
import Ethereum.ContractABI
-- yul-dsl
import YulDSL.Core
import YulDSL.StdBuiltIns.ABICodec     ()
import YulDSL.StdBuiltIns.Exception    ()
import YulDSL.StdBuiltIns.ValueType    ()
-- (control-extra)
import Control.IfThenElse
import Control.PatternMatchable
import Data.MPOrd
--
import YulDSL.Haskell.Effects.Pure
--
import YulDSL.Haskell.YulCatObj.Maybe  ()
import YulDSL.Haskell.YulCatObj.NP     ()
import YulDSL.Haskell.YulCatObj.TUPLEn ()


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
infixr 5 `yulCons`

-- | Revert without any message.
yulRevert :: forall eff a b. (YulO2 a b) => YulCat eff a b
yulRevert = YulDis >.> YulJmpB (MkYulBuiltIn @"__const_revert0_c_" @() @b)

-- | Wrapper for built-in keccak256 yul function.
yulKeccak256 :: forall eff a r. YulO2 r a => YulCat eff r a -> YulCat eff r B32
yulKeccak256 x = x >.> YulJmpB (MkYulBuiltIn @"__keccak_c_" @a @B32)

-- | Empty object constructor.
emptyCtor :: AnyYulCat
emptyCtor = MkAnyYulCat (YulDis @Pure @())

-- ^ 'MPEq' instance for YulCat INTx.
instance (YulO1 r, ValidINTx s n) => MPEq (YulCat eff r (INTx s n)) (YulCat eff r BOOL) where
  a == b = YulJmpB (MkYulBuiltIn @"__cmp_eq_t_") <.< YulProd a b <.< YulDup
  a /= b = YulJmpB (MkYulBuiltIn @"__cmp_ne_t_") <.< YulProd a b <.< YulDup

-- ^ 'MPOrd' instance for YulCat INTx.
instance (YulO1 r, ValidINTx s n) => MPOrd (YulCat eff r (INTx s n)) (YulCat eff r BOOL) where
  a  < b = YulJmpB (MkYulBuiltIn @"__cmp_lt_t_") <.< YulProd a b <.< YulDup
  a <= b = YulJmpB (MkYulBuiltIn @"__cmp_le_t_") <.< YulProd a b <.< YulDup
  a  > b = YulJmpB (MkYulBuiltIn @"__cmp_gt_t_") <.< YulProd a b <.< YulDup
  a >= b = YulJmpB (MkYulBuiltIn @"__cmp_ge_t_") <.< YulProd a b <.< YulDup

-- ^ 'Num' instance for INTx.
instance (YulO1 r, ValidINTx s n) => Num (YulCat eff r (INTx s n)) where
  a + b = YulJmpB (MkYulBuiltIn @"__checked_add_t_") <.< YulProd a b <.< YulDup
  a - b = YulJmpB (MkYulBuiltIn @"__checked_sub_t_") <.< YulProd a b <.< YulDup
  a * b = YulJmpB (MkYulBuiltIn @"__checked_mul_t_") <.< YulProd a b <.< YulDup
  abs = YulComp (YulJmpB (MkYulBuiltIn @"__checked_abs_t_"))
  signum = YulComp (YulJmpB (MkYulBuiltIn @"__checked_sig_t_"))
  fromInteger = YulEmb . fromInteger

-- ^ 'IfThenElse' instance for yul object 'BOOL'.
instance YulO2 a r => IfThenElse (YulCat eff r BOOL) (YulCat eff r a) where
  ifThenElse c a b = YulFork c YulId >.> YulITE a b
