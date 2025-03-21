{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE UndecidableInstances #-}
{-|

Copyright   : (c) 2023-2025 Miao, ZhiCheng
License     : LGPL-3
Maintainer  : hellwolf@yolc.dev
Stability   : experimental

= Description

This module provides the pattern matching instances for yul morphisms to n-tuples.

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


-- Tuple1 is Solo and special.

instance (YulO2 a r, YulCat eff r ~ m) =>
         SingleCasePattern (YulCat eff r) YulCatObj (Solo a) (m a) where
  is ma = ma >.> YulCoerceType
instance (YulO2 a r, YulCat eff r ~ m) =>
         PatternMatchable (YulCat eff r) YulCatObj (Solo a) (YulCat eff r a)
instance YulO2 a r =>
         InjectivePattern (YulCat eff r) YulCatObj (Solo a) (YulCat eff r a) where
  be ma = ma >.> YulCoerceType

-- Tuple2 is the base case.

instance (YulO3 a1 a2 r, YulCat eff r ~ m) =>
         SingleCasePattern (YulCat eff r) YulCatObj (a1, a2) (m a1, m a2) where
  is mtpl =
    let mx1 = mtpl >.> YulExl
        mx2 = mtpl >.> YulExr
    in (mx1, mx2)
instance (YulO3 a1 a2 r, YulCat eff r ~ m) =>
         PatternMatchable (YulCat eff r) YulCatObj (a1, a2) (m a1, m a2)
instance (YulO3 a1 a2 r, YulCat eff r ~ m) =>
         InjectivePattern (YulCat eff r) YulCatObj (a1, a2) (m a1, m a2) where
  be (mx1, mx2) = YulFork mx1 mx2

-- Tuple3 code is the example for the TH to generate inductively:

instance (YulO4 a1 a2 a3 r, YulCat eff r ~ m) =>
         SingleCasePattern (YulCat eff r) YulCatObj (a1, a2, a3) (m a1, m a2, m a3) where
  is mtpl =
    let mxxs = mtpl >.> YulReduceType >.> YulCoerceType
        mx1  = mxxs >.> YulExl
        mxs  = mxxs >.> YulExr >.> YulExtendType :: YulCat eff r (a2, a3)
        (mx2, mx3) = is mxs
    in (mx1, mx2, mx3)
instance (YulO4 a1 a2 a3 r, YulCat eff r ~ m) =>
         PatternMatchable (YulCat eff r) YulCatObj (a1, a2, a3) (m a1, m a2, m a3)
instance (YulO4 a1 a2 a3 r, YulCat eff r ~ m) =>
         InjectivePattern (YulCat eff r) YulCatObj (a1, a2, a3) (m a1, m a2, m a3) where
  be (mx1, mx2, mx3) =
    let mnpxs = (be (mx2, mx3) :: YulCat eff r (a2, a3)) >.> YulReduceType
    in YulFork mx1 mnpxs >.> YulCoerceType >.> YulExtendType

do
  insts <- mapM (\n -> do
    -- type variables: r, a, as...
    r <- TH.newName "r"
    a <- TH.newName "a"
    as <- replicateM (n - 1) (TH.newName "a")
    -- term variables: x, xs...
    x <- TH.newName "x"
    xs <- replicateM (n - 1) (TH.newName "x")
    -- m
    m <- [t| YulCat $(TH.varT =<< TH.newName "eff") $(TH.varT r) |]
    [d| instance ( $(tupleNFromVarsTWith (TH.conT ''YulO1 `TH.appT`) (r : a : as))
                 , SingleCasePattern $(pure m) YulCatObj
                                     $(tupleNFromVarsT as)
                                     $(tupleNFromVarsTWith (pure m `TH.appT`) as)
                 ) =>
                 SingleCasePattern $(pure m) YulCatObj
                                   $(tupleNFromVarsT (a : as))
                                   $(tupleNFromVarsTWith (pure m `TH.appT`) (a : as)) where
          is mtpl_ =
            let mxxs_ = mtpl_ >.> YulReduceType >.> YulCoerceType
                mx1_  = mxxs_  >.> YulExl
                $(TH.tupP (fmap TH.varP xs)) = is (mxxs_  >.> YulExr >.> YulExtendType
                                                   :: $(pure m) $(tupleNFromVarsT as))
            in $(TH.tupE (TH.varE 'mx1_ : fmap TH.varE xs))

        instance $(tupleNFromVarsTWith (TH.conT ''YulO1 `TH.appT`) (r : a : as)) =>
                 PatternMatchable $(pure m) YulCatObj
                                  $(tupleNFromVarsT (a : as))
                                  $(tupleNFromVarsTWith (pure m `TH.appT`) (a : as)) where

        instance $(tupleNFromVarsTWith (TH.conT ''YulO1 `TH.appT`) (r : a : as)) =>
                 InjectivePattern $(pure m) YulCatObj $(tupleNFromVarsT (a : as))
                                  $(tupleNFromVarsTWith (pure m `TH.appT`) (a : as)) where
          be $(TH.tupP (fmap TH.varP (x : xs))) =
            let mnpxs_ = ( $(TH.varE 'be `TH.appE` TH.tupE (fmap TH.varE xs))
                           :: $(pure m) $(tupleNFromVarsT as)
                         ) >.> YulReduceType
            in YulFork $(TH.varE x) mnpxs_ >.> YulCoerceType >.> YulExtendType
      |]) [4..15]
  pure (concat insts)
