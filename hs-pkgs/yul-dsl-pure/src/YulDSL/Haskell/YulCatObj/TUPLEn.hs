{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE UndecidableInstances #-}
{-|

Copyright   : (c) 2023-2025 Miao, ZhiCheng
License     : LGPL-3
Maintainer  : hellwolf@yolc.dev
Stability   : experimental

= Description

This module provides the pattern matching instances for all n-tuples.

-}
module YulDSL.Haskell.YulCatObj.TUPLEn where
-- base
import Control.Monad            (replicateM)
-- template-haskell
import Language.Haskell.TH      qualified as TH
-- yul-dsl
import YulDSL.Core
-- (control-extra)
import Control.PatternMatchable


instance ( YulCat eff r ~ m
         , YulO1 r
         , YulO1 a1, YulO1 a2
         ) => PatternMatchable m YulCatObj (a1, a2) (m a1, m a2) where
  be (x1, x2) = YulFork x1 x2
  match pat f =
    let x1 = pat >.> YulExl
        x2 = pat >.> YulExr
    in f (x1, x2)

do
  let mk_tuple_n_t xs = foldl' TH.appT (TH.tupleT (length xs)) (map TH.varT xs)
  let mk_mtuple_n_t m xs = foldl' (\b x -> b `TH.appT` (TH.varT m `TH.appT` x))
                           (TH.tupleT (length xs)) (map TH.varT xs)
  insts <- mapM (\n -> do
    m <- TH.newName "m"
    x <- TH.newName "a"
    xs' <- replicateM (n - 1) (TH.newName "a")
    let xs = x : xs'
    let tpl  = mk_tuple_n_t xs
    let mtpl = mk_mtuple_n_t m xs
    let clist = foldr (\a b -> b `TH.appT` (TH.conT ''YulO1 `TH.appT` TH.varT a)) (TH.tupleT n) xs
    [d| instance ( YulCat eff r ~ $(TH.varT m), YulO1 r, $(clist)
                 ) => PatternMatchable $(TH.varT m) YulCatObj $(tpl) $(mtpl) where
          -- be (x1, x2, x3) = YulFork x1 (be (x2, x3) >.> YulReduceType)
          be $(TH.tupP (fmap TH.varP xs)) =
            YulFork $(TH.varE x) ($(TH.varE 'be `TH.appE` TH.tupE (fmap TH.varE xs')) >.> YulReduceType)
            >.> YulCoerceType
            >.> YulExtendType
          match pat f =
            let pat' = pat >.> YulReduceType >.> YulCoerceType
                x1_ = pat' >.> YulExl
                xs_ = pat' >.> YulExr >.> YulExtendType
               -- match xs (\(x2, x3) -> f (x1, x2, x3))
            in match xs_ (\ $(TH.tupP (fmap TH.varP xs')) ->
                            $(TH.varE 'f `TH.appE` TH.tupE (TH.varE 'x1_ : fmap TH.varE xs')))
      |]) [3..15]
  pure (concat insts)
