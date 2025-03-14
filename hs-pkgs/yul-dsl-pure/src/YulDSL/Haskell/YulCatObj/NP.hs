{-# OPTIONS_GHC -Wno-orphans #-}
{-|

Copyright   : (c) 2023-2025 Miao, ZhiCheng
License     : LGPL-3
Maintainer  : hellwolf@yolc.dev
Stability   : experimental

= Description

This module provides the instances for yul morphisms to NP structures.

-}
module YulDSL.Haskell.YulCatObj.NP where
-- yul-dsl
import YulDSL.Core


-- ^ A yul morphism to a NP structure is sequenceable.
instance ( YulO3 x (NP xs) r
         , SequenceableNP (YulCat eff r) xs) =>
         SequenceableNP (YulCat eff r) (x:xs) where
  sequenceNP sxxs = sx :* sequenceNP @(YulCat eff r) @xs sxs
    where sxxs' = sxxs  >.> YulCoerceType
          sx    = sxxs' >.> YulExl
          sxs   = sxxs' >.> YulExr
