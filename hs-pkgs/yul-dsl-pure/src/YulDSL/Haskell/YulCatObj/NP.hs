{-# OPTIONS_GHC -Wno-orphans #-}
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

instance YulO1 r  =>
         SingleCasePattern (YulCat eff r) (NP I '[]) (NP (YulCat eff r) '[]) YulCatObj Many where
  is _ =  Nil

instance ( YulO3 x (NP I xs) r
         , TraversableNP (YulCat eff r) (x:xs)
         , DistributiveNP (YulCat eff r) (x:xs)
         , SingleCasePattern (YulCat eff r) (NP I xs) (NP (YulCat eff r) xs) YulCatObj Many
         ) =>
         SingleCasePattern (YulCat eff r) (NP I (x:xs)) (NP (YulCat eff r) (x:xs)) YulCatObj Many where
  is = sequenceNP

--
-- PatternMatchable instances
--

instance YulO1 r =>
         PatternMatchable (YulCat eff r) (NP I '[]) (NP (YulCat eff r) '[]) YulCatObj Many where
instance YulO1 r =>
         InjectivePattern (YulCat eff r) (NP I '[]) (NP (YulCat eff r) '[]) YulCatObj Many where
  be = distributeNP

instance ( YulO3 x (NP I xs) r
         , DistributiveNP (YulCat eff r) (x:xs)
         , TraversableNP (YulCat eff r) (x:xs)
         , SingleCasePattern (YulCat eff r) (NP I xs) (NP (YulCat eff r) xs) YulCatObj Many
         ) =>
         PatternMatchable (YulCat eff r) (NP I (x:xs)) (NP (YulCat eff r) (x:xs)) YulCatObj Many where
instance ( YulO3 x (NP I xs) r
         , DistributiveNP (YulCat eff r) (x:xs)
         , TraversableNP (YulCat eff r) (x:xs)
         , SingleCasePattern (YulCat eff r) (NP I xs) (NP (YulCat eff r) xs) YulCatObj Many
         ) =>
         InjectivePattern (YulCat eff r) (NP I (x:xs)) (NP (YulCat eff r) (x:xs)) YulCatObj Many where
  be = distributeNP
