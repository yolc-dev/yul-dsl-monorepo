{-# OPTIONS_GHC -Wno-orphans #-}
module Data.Num.Linear.YulDSL where
-- base
import Prelude                qualified as BasePrelude
-- yul-dsl-pure
import YulDSL.Haskell.LibPure ()
-- linear-base
import Prelude.Linear
import Unsafe.Linear          qualified as UnsafeLinear
-- yul-dsl
import YulDSL.Core


--
-- FromInteger instances for ABI types
--

instance FromInteger Integer where
  fromInteger = id

--  Num instances for (YulCat r (INTx s n))
--

instance (ValidINTx s n) => Additive (INTx s n) where
  (+) = UnsafeLinear.toLinear2 (BasePrelude.+)
instance (ValidINTx s n) => AddIdentity (INTx s n) where
  zero = fromIntegral (0 :: Integer)
instance (ValidINTx s n) => AdditiveGroup (INTx s n) where
  (-) = UnsafeLinear.toLinear2 (BasePrelude.-)
instance (ValidINTx s n) => Multiplicative (INTx s n) where
  (*) = UnsafeLinear.toLinear2 (BasePrelude.*)
instance (ValidINTx s n) => FromInteger (INTx s n) where
  fromInteger = UnsafeLinear.toLinear BasePrelude.fromInteger

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
