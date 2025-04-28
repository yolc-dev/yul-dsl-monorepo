{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_HADDOCK hide #-}
{-|

Copyright   : (c) 2023-2025 Miao, ZhiCheng
License     : LGPL-3
Maintainer  : hellwolf@yolc.dev
Stability   : experimental

= Description

This module provides type class instance for BOOL yul objects.

-}
module YulDSL.Haskell.YulCatObj.BOOL where
-- yul-dsl
import YulDSL.Core
import YulDSL.StdBuiltIns.ValueType ()
--
import Control.IfThenElse
import Control.PatternMatchable


-- ^ 'IfThenElse' instance for yul object 'BOOL'.
instance YulO2 a r => IfThenElse (YulCat eff r BOOL) (YulCat eff r a) where
  ifThenElse c a b = YulFork c YulId >.> YulITE a b

instance YulO1 r => PatternMatchable (YulCat eff r) BOOL Bool YulCatObj Many where
  match a f = yulIfThenElse a (f True) (f False)
  couldBe b = if b then (yulEmb true) else (yulEmb false)
