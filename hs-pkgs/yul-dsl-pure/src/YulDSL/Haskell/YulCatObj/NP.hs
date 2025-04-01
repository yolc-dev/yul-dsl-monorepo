{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE UndecidableInstances #-}
{-|

Copyright   : (c) 2023-2025 Miao, ZhiCheng
License     : LGPL-3
Maintainer  : hellwolf@yolc.dev
Stability   : experimental

= Description

This module provides the instances for yul morphisms to NP structures.

-}
module YulDSL.Haskell.YulCatObj.NP () where
-- yul-dsl
import YulDSL.Core
-- (control-extra)
import Control.PatternMatchable


--
-- SingleCasePattern instances
--

instance YulO1 r => SingleCasePattern (YulCat eff r) (NP '[]) (NP '[]) YulCatObj Many where
  is _ =  Nil

instance ( YulO3 x (NP xs) r
         , YulCat eff r ~ m
         , MapList m xs ~ mxs
         , MapList m (x:xs) ~ mxxs
         , TraversableNP m (x:xs)
         , DistributiveNP m (x:xs)
         , SingleCasePattern m (NP xs) (NP mxs) YulCatObj Many
         ) =>
         SingleCasePattern (YulCat eff r) (NP (x:xs)) (NP mxxs) YulCatObj Many where
  is = sequenceNP

--
-- PatternMatchable instances
--

instance YulO1 r => PatternMatchable (YulCat eff r) (NP '[]) (NP '[]) YulCatObj Many where
  couldBe = distributeNP

instance ( YulO3 x (NP xs) r
         , YulCat eff r ~ m
         , MapList m xs ~ mxs
         , MapList m (x:xs) ~ mxxs
         , DistributiveNP m (x:xs)
         , TraversableNP m (x:xs)
         , SingleCasePattern m (NP xs) (NP mxs) YulCatObj Many
         ) =>
         PatternMatchable (YulCat eff r) (NP (x:xs)) (NP mxxs) YulCatObj Many where
  couldBe = distributeNP
