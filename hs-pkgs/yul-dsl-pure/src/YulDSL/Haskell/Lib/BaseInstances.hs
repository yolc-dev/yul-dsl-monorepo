{-# OPTIONS_GHC -Wno-orphans #-}
module YulDSL.Haskell.Lib.BaseInstances () where
-- yul-dsl
import YulDSL.Core
import YulDSL.StdBuiltIns.ValueType ()
-- (data-control-extra)
import Control.IfThenElse
import Data.MPOrd


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
