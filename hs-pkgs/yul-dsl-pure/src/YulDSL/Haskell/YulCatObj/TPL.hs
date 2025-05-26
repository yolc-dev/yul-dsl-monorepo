{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE LinearTypes #-}
{-|

Copyright   : (c) 2023-2025 Miao, ZhiCheng
License     : LGPL-3
Maintainer  : hellwolf@yolc.dev
Stability   : experimental

= Description

This module provides the pattern matching instances for yul morphisms to n-tuples.

-}
module YulDSL.Haskell.YulCatObj.TPL (getSolo) where
-- base
import Control.Monad            (replicateM)
-- TODO: - Fixed inability to re-export the ``Data.Tuple.MkSolo`` constructor (:ghc-ticket:`25182`)
import Data.Tuple               (Solo (MkSolo))
-- template-haskell
import Language.Haskell.TH      qualified as TH
-- yul-dsl
import YulDSL.Core
-- (control-extra)
import Control.PatternMatchable


-- | Arrow-polymorphic version of the getSolo.
getSolo :: forall a p. Solo a %p -> a
getSolo (MkSolo a) = a

-- Tuple1 is Solo and special.

instance (YulO2 a r) =>
         SingleCasePattern (YulCat eff r) (Solo a) (Solo (YulCat eff r a))
         YulCatObj Many where
  is a = MkSolo (a >.> YulCoerceType)
instance (YulO2 a r, YulCat eff r ~ m) =>
         PatternMatchable (YulCat eff r) (Solo a) (Solo (YulCat eff r a))
         YulCatObj Many where
-- Make injective pattern free from MkSolo.
instance YulO2 a r =>
         InjectivePattern (YulCat eff r) (Solo a) (Solo (YulCat eff r a))
         YulCatObj Many where
  be (MkSolo a) = a >.> YulCoerceType

-- Tuple2 is the base case.

instance (YulO3 a1 a2 r) =>
         SingleCasePattern
         (YulCat eff r)
         (a1, a2)
         (YulCat eff r a1, YulCat eff r a2)
         YulCatObj Many where
  is mtpl =
    let mx1 = mtpl >.> YulExl
        mx2 = mtpl >.> YulExr
    in (mx1, mx2)
instance (YulO3 a1 a2 r) =>
         PatternMatchable
         (YulCat eff r)
         (a1, a2)
         (YulCat eff r a1, YulCat eff r a2)
         YulCatObj Many
instance (YulO3 a1 a2 r, YulCat eff r ~ m) =>
         InjectivePattern
         (YulCat eff r)
         (a1, a2)
         (YulCat eff r a1, YulCat eff r a2)
         YulCatObj Many where
  be (mx1, mx2) = YulFork mx1 mx2

-- Tuple{[3..16]} instances

-- Tuple3 code is the example for the TH to mimic how to generate more instances inductively:

instance (YulO4 a1 a2 a3 r) =>
         SingleCasePattern
         (YulCat eff r)
         (a1, a2, a3)
         (YulCat eff r a1, YulCat eff r a2, YulCat eff r a3)
         YulCatObj Many where
  is mtpl =
    let mxxs = mtpl >.> YulReduceType >.> YulCoerceType
        mx1  = mxxs >.> YulExl
        mxs  = mxxs >.> YulExr >.> YulExtendType :: YulCat eff r (a2, a3)
        (mx2, mx3) = is mxs
    in (mx1, mx2, mx3)
instance (YulO4 a1 a2 a3 r) =>
         PatternMatchable
         (YulCat eff r)
         (a1, a2, a3)
         (YulCat eff r a1, YulCat eff r a2, YulCat eff r a3)
         YulCatObj Many
instance (YulO4 a1 a2 a3 r) =>
         InjectivePattern
         (YulCat eff r)
         (a1, a2, a3)
         (YulCat eff r a1, YulCat eff r a2, YulCat eff r a3)
         YulCatObj Many where
  be (mx1, mx2, mx3) =
    let mxs = (be (mx2, mx3) :: YulCat eff r (a2, a3)) >.> YulReduceType
    in YulFork mx1 mxs >.> YulCoerceType >.> YulExtendType

do
  let mkT_YulO1 = (TH.conT ''YulO1 `TH.appT`)
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
    [d| instance ( $(tupleNFromVarsTWith mkT_YulO1 (r : a : as))
                 , SingleCasePattern $(pure m)
                                     $(tupleNFromVarsT as)
                                     $(tupleNFromVarsTWith (pure m `TH.appT`) as)
                                     YulCatObj Many
                 ) =>
                 SingleCasePattern $(pure m)
                                   $(tupleNFromVarsT (a : as))
                                   $(tupleNFromVarsTWith (pure m `TH.appT`) (a : as))
                                   YulCatObj Many where
          is mtpl_ =
            let mxxs_ = mtpl_ >.> YulReduceType >.> YulCoerceType
                mx1_  = mxxs_  >.> YulExl
                $(TH.tupP (fmap TH.varP xs)) =
                  is (mxxs_  >.> YulExr >.> YulExtendType
                      :: $(pure m) $(tupleNFromVarsT as))
            in $(TH.tupE (TH.varE 'mx1_ : fmap TH.varE xs))

        instance $(tupleNFromVarsTWith mkT_YulO1 (r : a : as)) =>
                 PatternMatchable $(pure m)
                                  $(tupleNFromVarsT (a : as))
                                  $(tupleNFromVarsTWith (pure m `TH.appT`) (a : as))
                                  YulCatObj Many

        instance $(tupleNFromVarsTWith mkT_YulO1 (r : a : as)) =>
                 InjectivePattern $(pure m)
                                  $(tupleNFromVarsT (a : as))
                                  $(tupleNFromVarsTWith (pure m `TH.appT`) (a : as))
                                  YulCatObj Many where
          be $(TH.tupP (fmap TH.varP (x : xs))) =
            let mnpxs_ = ( $(TH.varE 'be `TH.appE` TH.tupE (fmap TH.varE xs))
                           :: $(pure m) $(tupleNFromVarsT as)
                         ) >.> YulReduceType
            in YulFork $(TH.varE x) mnpxs_ >.> YulCoerceType >.> YulExtendType
      |]) [4..16]
  pure (concat insts)
