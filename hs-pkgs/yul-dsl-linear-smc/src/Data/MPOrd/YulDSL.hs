{-# OPTIONS_GHC -Wno-orphans #-}
module Data.MPOrd.YulDSL where

-- linear-base
import Prelude.Linear               (Bool (False, True), Consumable, lseq)
-- yul-dsl
import YulDSL.Core
import YulDSL.StdBuiltIns.ValueType ()
--
import Data.MPOrd

-- | 'MPEq' instance for yul category morphisms.
instance (YulO1 r, ValidINTx s n) => MPEq (YulCat eff r (INTx s n)) (YulCat eff r BOOL) where
  a == b = YulJmpB (MkYulBuiltIn @"__cmp_eq_t_") <.< YulProd a b <.< YulDup
  a /= b = YulJmpB (MkYulBuiltIn @"__cmp_ne_t_") <.< YulProd a b <.< YulDup

-- | 'MPOrd' instance for yul category morphisms.
instance (YulO1 r, ValidINTx s n) => MPOrd (YulCat eff r (INTx s n)) (YulCat eff r BOOL) where
  a  < b = YulJmpB (MkYulBuiltIn @"__cmp_lt_t_") <.< YulProd a b <.< YulDup
  a <= b = YulJmpB (MkYulBuiltIn @"__cmp_le_t_") <.< YulProd a b <.< YulDup
  a  > b = YulJmpB (MkYulBuiltIn @"__cmp_gt_t_") <.< YulProd a b <.< YulDup
  a >= b = YulJmpB (MkYulBuiltIn @"__cmp_ge_t_") <.< YulProd a b <.< YulDup

-- | Default if-then-else instance for Haskell Bool.
instance Consumable a => IfThenElse Bool a where
  ifThenElse True  a b = lseq b a
  ifThenElse False a b = lseq a b
