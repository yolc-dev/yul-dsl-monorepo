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

type YulFunctor eff f = EndoFunctor (YulCat eff) f

instance (YulO1 r, YulFunctor eff f) => ExoFunctor (HaskCatFunction (YulCat eff) r) (YulCat eff) f where
  -- goal: f a ~ f b
  -- endomap (a ~> b) : f a ~> f b
  -- \case
  --   (MkHaskCatFunction g) ->
  --     g : (r ~> a) -> (r ~> b)
  --     g YulCont: r ~> b
  --     YulRunCont (g YulCont): a ~ b
  exomap (MkHaskCatFunction g) = endomap (YulRunCont (g YulCont))
