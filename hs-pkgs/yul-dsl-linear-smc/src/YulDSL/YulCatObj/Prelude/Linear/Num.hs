{-# OPTIONS_GHC -Wno-orphans #-}
module YulDSL.YulCatObj.Prelude.Linear.Num where

-- base
import Prelude        qualified as Prelude.Base
-- linear-base
import Prelude.Linear
import Unsafe.Linear  qualified as UnsafeLinear
-- yul-dsl
import YulDSL.Core


--
-- FromInteger instances for ABI types
--

instance FromInteger Integer where
  fromInteger = id

instance ValidINTx s n => FromInteger (INTx s n) where
  fromInteger = UnsafeLinear.toLinear Prelude.Base.fromInteger

--
--  Num instances for (YulCat r a)
--

instance (YulO1 r, YulNum a) => Additive (YulCat eff r a) where
  a + b = YulJmpB (yulB_NumAdd @a) <.< YulProd a b <.< YulDup

instance (YulO1 r, YulNum a) => AddIdentity (YulCat eff r a) where
  zero = YulEmb (fromIntegral (0 :: Integer))

instance (YulO1 r, YulNum a) => AdditiveGroup (YulCat eff r a) where
  a - b = YulJmpB (yulB_NumSub @a) <.< YulProd a b <.< YulDup

instance (YulO1 r, ValidINTx s n) => FromInteger (YulCat eff r (INTx s n)) where
  fromInteger x = YulEmb (fromInteger x)
