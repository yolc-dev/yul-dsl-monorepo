{-# OPTIONS_GHC -Wno-orphans #-}
module Data.Num.Linear.YulDSL where
-- base
import Prelude                      qualified as BasePrelude
-- yul-dsl-pure
import YulDSL.Haskell.YulUtils.Pure ()
-- linear-base
import Prelude.Linear
import Unsafe.Linear                qualified as UnsafeLinear
-- yul-dsl
import YulDSL.Core


--
-- FromInteger instances for ABI types
--

instance FromInteger Integer where
  fromInteger = id

instance ValidINTx s n => FromInteger (INTx s n) where
  fromInteger = UnsafeLinear.toLinear BasePrelude.fromInteger

--
--  Num instances for (YulCat r (INTx s n))
--

instance (YulO1 r, ValidINTx s n) => Additive (YulCat eff r (INTx s n)) where
  (+) = UnsafeLinear.toLinear2 (BasePrelude.+)
instance (YulO1 r, ValidINTx s n) => AddIdentity (YulCat eff r (INTx s n)) where
  zero = YulEmb (fromIntegral (0 :: Integer))
instance (YulO1 r, ValidINTx s n) => AdditiveGroup (YulCat eff r (INTx s n)) where
  (-) = UnsafeLinear.toLinear2 (BasePrelude.-)
instance (YulO1 r, ValidINTx s n) => Multiplicative (YulCat eff r (INTx s n)) where
  (*) = UnsafeLinear.toLinear2 (BasePrelude.*)
instance (YulO1 r, ValidINTx s n) => FromInteger (YulCat eff r (INTx s n)) where
  fromInteger = UnsafeLinear.toLinear BasePrelude.fromInteger

instance (YulO1 r, ValidINTx s n) => Additive (YulCat eff r (Maybe (INTx s n))) where
  (+) = UnsafeLinear.toLinear2 (BasePrelude.+)
instance (YulO1 r, ValidINTx s n) => AddIdentity (YulCat eff r (Maybe (INTx s n))) where
  zero = YulEmb (fromIntegral (0 :: Integer))
instance (YulO1 r, ValidINTx s n) => AdditiveGroup (YulCat eff r (Maybe (INTx s n))) where
  (-) = UnsafeLinear.toLinear2 (BasePrelude.-)
instance (YulO1 r, ValidINTx s n) => Multiplicative (YulCat eff r (Maybe (INTx s n))) where
  (*) = UnsafeLinear.toLinear2 (BasePrelude.*)
instance (YulO1 r, ValidINTx s n) => FromInteger (YulCat eff r (Maybe (INTx s n))) where
  fromInteger = UnsafeLinear.toLinear BasePrelude.fromInteger
