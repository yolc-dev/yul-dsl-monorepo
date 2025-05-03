{-# OPTIONS_GHC -Wno-orphans #-}
module YulDSL.Haskell.YulCat
  ( YulFunctor
  ) where
-- yul-dsl
import YulDSL.Core
--
import Control.Category
import Data.ExoFunctor


instance Category (YulCat eff) where
  type instance Obj (YulCat eff) = YulCatObj
  idₖ = YulId
  (∘) = YulComp

type YulFunctor f eff r = HexoFunctor f (YulCat eff) r (YulCat eff) r
