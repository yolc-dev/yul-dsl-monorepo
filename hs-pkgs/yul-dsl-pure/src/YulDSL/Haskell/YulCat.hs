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

instance YulFunctor eff f => ExoFunctor (HaskCatFunction (YulCat eff) ()) (YulCat eff) f where
  -- goal: f a ~ f b
  -- endomap (a ~> b) : f a ~> f b
  -- \case
  --   (MkHaskCatFunction g) ->
  --     g : (() ~> a) -> (() ~> b)
  --     YulHaskFunc g: a ~> b
  exomap (MkHaskCatFunction g) = endomap (YulHaskFunc g)
