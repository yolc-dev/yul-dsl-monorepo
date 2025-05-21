{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-|

Copyright   : (c) 2024-2025 Miao, ZhiCheng
License     : MIT

Maintainer  : hellwolf@yolc.dev
Stability   : experimental
Portability : GHC2024

= Description

This module contains template haskell generated code to work with n-ary tuples. It includes type families to convert
between the TupleN types and their isomorphic SimpleNP type, and functions that actually convert between their values.

It supports up to 16-ary tuple.

-}
module Data.TupleN
  ( TupleNtoNP, HavingFromTupleNtoNP (fromTupleNtoNP)
  , NPtoTupleN, HavingFromNPtoTupleN (fromNPtoTupleN)
  , ConvertibleTupleNtoNP, ConvertibleNPtoTupleN
  , module Data.TupleN.TH
  -- re-export solo tuple type
  , Solo (MkSolo)
  ) where
-- base
import Control.Monad       (replicateM)
import Data.Tuple          (Solo (MkSolo))
-- template-haskell
import Language.Haskell.TH qualified as TH
--
import Data.SimpleNP
import Data.TupleN.TH


--
-- TupleNtoNP, FromTupleNtoNP (fromTupleNtoNP)
--
do
  let maxTupleN = 16
  let nilE = TH.conE 'Nil
  let consE = TH.conE '(:*)
  tfName <- TH.newName "TupleNtoNP"
  clsName <- TH.newName "HavingFromTupleNtoNP"
  fnName <- TH.newName "fromTupleNtoNP"
  t_m <- TH.newName "m"
  t_tpl <- TH.newName "tpl"
  t_r <- TH.newName "r"
  t_p <- TH.newName "p" -- multiplicity

  -- type family TupleNtoNP m tpl = r | r -> m tpl where
  --   TupleNtoNP m () = NP m '[]
  --   TupleNtoNP m (Solo (m x)) = NP m '[x]
  --   TupleNtoNP m (m x1, m x2) = NP m '[x1, x2]
  tfDec <- do
    TH.closedTypeFamilyD tfName [TH.plainTV t_m, TH.plainTV t_tpl]
      -- injectivity: r -> m tpl
      (TH.tyVarSig (TH.plainTV t_r)) (Just (TH.injectivityAnn t_r [t_m, t_tpl]))
      -- equations
      ((\n -> do
           xs <- replicateM n (TH.newName "x")
           TH.tySynEqn Nothing
             -- lhs: TupleNtoNP m (m x1, .. m x_n)
             (TH.conT tfName `TH.appT` TH.varT t_m `TH.appT` tupleNFromVarsTWith (TH.varT t_m `TH.appT`) xs)
             -- rhs: NP m '[x1, ... xn]
             (TH.conT ''NP `TH.appT` TH.varT t_m `TH.appT` promotedListFromVarsT xs)
       ) <$> [0..maxTupleN])

  -- class HavingFromTupleNPtoNP m tpl | tpl -> m where
  --   fromTupleNtoNP :: tpl %p -> TupleNtoNP m tpl
  -- -- instance HavingFromTupleNPtoNP m () -- bad: non-injective
  -- instance HavingFromTupleNPtoNP m (Solo (m a))
  -- instance HavingFromTupleNPtoNP m (m a1, m a2)
  clsInstsDec <- do
    -- class definition
    cls <- TH.classD
           (pure []) -- context
           clsName
           [TH.plainTV t_m, TH.plainTV t_tpl] -- bound variables
           [TH.funDep [t_tpl] [t_m]]
           [TH.sigD fnName ( TH.mulArrowT `TH.appT` TH.varT t_p `TH.appT` TH.varT t_tpl `TH.appT`
                             (TH.conT tfName `TH.appT` TH.varT t_m `TH.appT` TH.varT t_tpl)
                           )]
    insts <- mapM
      (\n -> do
          xs <- replicateM n (TH.newName "x")
          TH.instanceD
            (pure []) -- context
            (TH.conT clsName `TH.appT` TH.varT t_m `TH.appT` tupleNFromVarsTWith (TH.varT t_m `TH.appT`) xs)
            -- fromTupleNtoNP (x1, .. xn) = x1 :* ... xn :* Nil
            [TH.funD fnName
             [ TH.clause
               [TH.tupP (map TH.varP xs)]
               (TH.normalB $ foldr ((\a b -> TH.infixE (Just a) consE (Just b)) . TH.varE) nilE xs)
               []]]
      ) [1..maxTupleN]
    pure $ cls : insts

  pure $ tfDec : clsInstsDec

--
-- NPtoTupleN, FromNPtoTupleN (fromNPtoTupleN)
--
do
  let maxTupleN = 16
  tfName <- TH.newName "NPtoTupleN"
  clsName <- TH.newName "HavingFromNPtoTupleN"
  fnName <- TH.newName "fromNPtoTupleN"
  t_m <- TH.newName "m"
  t_np <- TH.newName "np"
  t_r <- TH.newName "r"
  t_p <- TH.newName "p" -- multiplicity

  -- type family NPtoTupleN m np = r | r -> m np where
  --   -- NPtoTupleN m (NP m '[]) = () -- this violates the injectivity
  --   NPtoTupleN m (NP m '[x]) = (Solo (m x))
  --   NPtoTupleN m (NP m '[x1, x2]) = (m x1, m x2)
  tfDec <- do
    TH.closedTypeFamilyD tfName [TH.plainTV t_m, TH.plainTV t_np]
      (TH.tyVarSig (TH.plainTV t_r)) (Just (TH.injectivityAnn t_r [t_m, t_np]))
      ((\n -> do
           xs <- replicateM n (TH.newName "x")
           TH.tySynEqn Nothing
             (TH.conT tfName `TH.appT`
               TH.varT t_m `TH.appT`
               (TH.conT ''NP `TH.appT` TH.varT t_m `TH.appT` promotedListFromVarsT xs))
             (tupleNFromVarsTWith (TH.varT t_m `TH.appT`) xs)
       ) <$> ([1..maxTupleN]))

  -- class HavingFromNPtoTupleN m np | np -> m where
  --   fromNPtoTupleN :: np %p -> NPtoTupleN m a
  -- instance HavingFromNPtoTupleN m (NP m '[]) where
  -- instance HavingFromNPtoTupleN m (NP m '[a]) where
  -- instance HavingFromNPtoTupleN m (NP m '[a1, a2]) where
  clsInstsDec <- do
    let np_p = foldr ((\a b -> TH.infixP a '(:*) b) . TH.varP) (TH.conP 'Nil [])
    cls <- TH.classD
           (pure []) -- context
           clsName
           [TH.plainTV t_m, TH.plainTV t_np] -- bound variables
           [TH.funDep [t_np] [t_m]]
           [TH.sigD fnName (TH.mulArrowT `TH.appT` TH.varT t_p `TH.appT` TH.varT t_np `TH.appT`
                            (TH.conT tfName `TH.appT` TH.varT t_m `TH.appT` TH.varT t_np)
                           )]
    insts <- mapM
      (\n -> do
          xs <- replicateM n (TH.newName "x")
          TH.instanceD (pure [])
            (TH.conT clsName `TH.appT`
             TH.varT t_m `TH.appT`
             (TH.conT ''NP `TH.appT` TH.varT t_m `TH.appT` promotedListFromVarsT xs))
            -- fromNPtoTupleN (x1 :* .. :* Nil) = (x1, ..)
            [TH.funD fnName
              [ TH.clause
                [np_p xs]
                (TH.normalB $ TH.tupE $ fmap TH.varE xs)
                []]]
      ) [1..maxTupleN]
    pure $ cls : insts

  pure $ tfDec : clsInstsDec

-- | A constraint alias for TupleN types that are convertible to NP and vice versa.
type ConvertibleTupleNtoNP m tpl = ( NPtoTupleN m (TupleNtoNP m tpl) ~ tpl
                                   , HavingFromTupleNtoNP m tpl
                                   , HavingFromNPtoTupleN m (TupleNtoNP m tpl)
                                   )

-- | A constraint alias for NP types that are convertible to TupleN and vice versa.
type ConvertibleNPtoTupleN m np = ( TupleNtoNP m (NPtoTupleN m np) ~ np
                                  , HavingFromTupleNtoNP m (NPtoTupleN m np)
                                  , HavingFromNPtoTupleN m np
                                  )
