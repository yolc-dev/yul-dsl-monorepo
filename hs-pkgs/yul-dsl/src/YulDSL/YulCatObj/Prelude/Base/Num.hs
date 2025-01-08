{-# OPTIONS_GHC -Wno-orphans #-}
{-|

Copyright   : (c) 2023-2024 Miao, ZhiCheng
License     : LGPL-3
Maintainer  : hellwolf@yolc.dev
Stability   : experimental

= Description

This module defines the 'Num' instance from base library for 'YulNum' objects.

-}
module YulDSL.YulCatObj.Prelude.Base.Num where
--
import YulDSL.Core.YulCat
import YulDSL.Core.YulNum


instance (YulO2 a r, YulNum a) => Num (YulCat eff r a) where
  a + b = YulJmpB (yulB_NumAdd @a) <.< YulProd a b <.< YulDup
  a - b = YulJmpB (yulB_NumSub @a) <.< YulProd a b <.< YulDup
  a * b = YulJmpB (yulB_NumMul @a) <.< YulProd a b <.< YulDup
  abs = YulComp (YulJmpB (yulB_NumAbs @a))
  signum = YulComp (YulJmpB (yulB_NumSig @a))
  fromInteger = YulEmb . fromInteger
