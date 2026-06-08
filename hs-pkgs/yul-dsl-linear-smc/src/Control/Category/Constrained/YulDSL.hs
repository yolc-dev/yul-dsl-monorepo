{-# OPTIONS_GHC -Wno-orphans #-}
{-|

Copyright   : (c) 2023 Miao, ZhiCheng
License     : LGPL-3
Maintainer  : hellwolf@yolc.dev
Stability   : experimental

= Description

Categories required for being a symmetric monoidal category.

-}

module Control.Category.Constrained.YulDSL () where

import Prelude (undefined)
-- base
-- constraints
import Data.Constraint              (Dict (Dict))
-- linear-smc
import Control.Category.Constrained (Cartesian (..), Category (..), Monoidal (..), ProdObj (..))
--
import YulDSL.Core.YulCat           (YulCat (..), YulCatObj )

-- | Instance for linear-smc 'ProdObj' for the objects in the category.
instance ProdObj YulCatObj where
  prodobj = Dict
  objprod = undefined
  objunit = Dict

instance Category YulCat where
  type Obj YulCat = YulCatObj
  id  = undefined
  (∘) = YulComp

instance Monoidal YulCat where
  (×)     = undefined
  unitor  = undefined
  unitor' = undefined
  assoc   = undefined
  assoc'  = undefined
  swap    = undefined

