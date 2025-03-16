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
module YulDSL.Haskell.YulCatObj.NP where
-- yul-dsl
import YulDSL.Core
-- (control-extra)
import Control.PatternMatchable


--
-- sequenceNP instance
--

instance ( YulO3 x (NP xs) r
         , YulCat eff r ~ s
         ) =>
         ConstructibleNP (YulCat eff r) x xs where
  consNP sx sxs = YulFork sx sxs >.> YulCoerceType
  unconsNP xxs = (x, xs)
    where xxs' = xxs  >.> YulCoerceType
          x    = xxs' >.> YulExl
          xs   = xxs' >.> YulExr

instance YulO1 r => SequenceableNP (YulCat eff r) '[] where
  sequenceNP _ = Nil
  unsequenceNP _ = YulEmb Nil

-- ^ A yul morphism to a NP structure is sequenceable.
instance ( YulO3 x (NP xs) r
         , YulCat eff r ~ s
         , SequenceableNP s xs
         ) =>
         SequenceableNP (YulCat eff r) (x:xs) where

--
-- SingleCasePattern instances
--

instance YulO1 r => SingleCasePattern (YulCat eff r) YulCatObj (NP '[]) (NP '[]) where
  is _ =  Nil

instance ( YulO3 x (NP xs) r
         , YulCat eff r ~ m
         , MapList m xs ~ mxs
         , MapList m (x:xs) ~ mxxs
         , SequenceableNP m (x:xs)
         , SingleCasePattern m YulCatObj (NP xs) (NP mxs)
         ) =>
         SingleCasePattern (YulCat eff r) YulCatObj (NP (x:xs)) (NP mxxs) where
  is = sequenceNP

--
-- PatternMatchable instances
--

instance YulO1 r => PatternMatchable (YulCat eff r) YulCatObj (NP '[]) (NP '[]) where
  couldBe = unsequenceNP

instance ( YulO3 x (NP xs) r
         , YulCat eff r ~ m
         , MapList m xs ~ mxs
         , MapList m (x:xs) ~ mxxs
         , SequenceableNP m (x:xs)
         , SingleCasePattern m YulCatObj (NP xs) (NP mxs)
         ) =>
         PatternMatchable (YulCat eff r) YulCatObj (NP (x:xs)) (NP mxxs) where
  couldBe = unsequenceNP
