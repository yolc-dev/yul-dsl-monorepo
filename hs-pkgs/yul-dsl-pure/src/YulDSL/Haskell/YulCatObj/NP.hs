{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE UndecidableInstances #-}
{-|

Copyright   : (c) 2023-2025 Miao, ZhiCheng
License     : LGPL-3
Maintainer  : hellwolf@yolc.dev
Stability   : experimental

= Description

This module provides the pattern matching instances for all n-ary product (NP).

-}
module YulDSL.Haskell.YulCatObj.NP where
-- yul-dsl
import YulDSL.Core


yulSplitNP :: forall eff r m x xs.
              (YulCat eff r ~ m, YulO3 r x (NP xs))
  => m (NP (x:xs)) -> (m x, m (NP xs))
yulSplitNP pat =
      let pat' = pat  >.> YulCoerceType
          mx   = pat' >.> YulExl
          mxs  = pat' >.> YulExr
      in (mx, mxs)
