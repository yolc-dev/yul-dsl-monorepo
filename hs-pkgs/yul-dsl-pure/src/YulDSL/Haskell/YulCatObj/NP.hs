{-# OPTIONS_GHC -Wno-orphans #-}
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
  ( YulCat eff r ~ m
  , YulO3 r x (NP xs)
  ) =>
  m (NP (x:xs)) ->
  (m x, m (NP xs))
yulSplitNP pat =
      let pat' = pat  >.> YulCoerceType
          mx   = pat' >.> YulExl
          mxs  = pat' >.> YulExr
      in (mx, mxs)

yulSequenceNP ::
  () =>
  m (NP xs) ->
  NP (MapList m xs)
yulSequenceNP = undefined

yulNPToTupleN :: forall eff r m xs.
  ( YulCat eff r ~ m
  , YulO2 r (NP xs)
  , ConvertibleNPtoTupleN (NP (MapList m xs))
  ) =>
  m (NP xs) ->
  NPtoTupleN (NP (MapList m xs))
yulNPToTupleN = fromNPtoTupleN . yulSequenceNP
