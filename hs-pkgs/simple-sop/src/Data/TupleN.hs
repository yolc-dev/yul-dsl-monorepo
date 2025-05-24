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
  , TupleN, TupleN_M
  , ConvertibleTupleNtoNP, ConvertibleNPtoTupleN
  , TupleNWithSameM
  , module Data.TupleN.TH
  -- re-export TupleN
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


do
  let maxTupleN = 16
  --
  t_m <- TH.newName "m"
  t_np <- TH.newName "np"
  t_as <- TH.newName "as"
  t_tpl <- TH.newName "tpl"
  t_r <- TH.newName "r"
  t_p <- TH.newName "p" -- multiplicity

  ----------------------------------------------------------------------------------
  -- TupleN, TupleN_M
  ----------------------------------------------------------------------------------

  tf_tpl <- TH.newName "TupleN"
  tf_tplm <- TH.newName "TupleN_M"

  -- type family TupleN xs = r | r -> xs where
  --   TupleN '[] = ()
  --   TupleN '[x] = (Solo x)
  --   TupleN '[x1, x2] = (x1, x2)
  dec_tpl <- do
    TH.closedTypeFamilyD tf_tpl [TH.plainTV t_as]
      (TH.tyVarSig (TH.plainTV t_r)) (Just (TH.injectivityAnn t_r [t_as]))
      ((\n -> do
           xs <- replicateM n (TH.newName "x")
           TH.tySynEqn Nothing
             (TH.conT tf_tpl `TH.appT` (promotedListFromVarsT xs))
             (tupleNFromVarsT xs)
       ) <$> [0..maxTupleN])

  -- type family TupleN_M m xs = r | r -> m xs where
  --   -- TupleN_M _ '[] = () -- injectivity violation
  --   TupleN_M m '[x] = (Solo (m x))
  --   TupleN_M m '[x1, x2] = (m x1, m x2)
  dec_tplm <- do
    TH.closedTypeFamilyD tf_tplm [TH.plainTV t_m, TH.plainTV t_as]
      (TH.tyVarSig (TH.plainTV t_r)) (Just (TH.injectivityAnn t_r [t_m, t_as]))
      ((\n -> do
           xs <- replicateM n (TH.newName "x")
           TH.tySynEqn Nothing
             (TH.conT tf_tplm `TH.appT` TH.varT t_m `TH.appT` (promotedListFromVarsT xs))
             (tupleNFromVarsTWith (TH.varT t_m `TH.appT`) xs)
       ) <$> [1..maxTupleN])

  ----------------------------------------------------------------------------------
  -- TupleNtoNP, HavingFromTupleNtoNP
  ----------------------------------------------------------------------------------

  tf_tpl2np <- TH.newName "TupleNtoNP"
  cls_tpl2np <- TH.newName "HavingFromTupleNtoNP"
  fn_tpl2np <- TH.newName "fromTupleNtoNP"

  -- type family TupleNtoNP m tpl = r | r -> m tpl where
  --   TupleNtoNP m () = NP m '[]
  --   TupleNtoNP m (Solo (m x)) = NP m '[x]
  --   TupleNtoNP m (m x1, m x2) = NP m '[x1, x2]
  dec_tf_tpl2np <- do
    TH.closedTypeFamilyD tf_tpl2np [TH.plainTV t_m, TH.plainTV t_tpl]
      -- injectivity: r -> m tpl
      (TH.tyVarSig (TH.plainTV t_r)) (Just (TH.injectivityAnn t_r [t_m, t_tpl]))
      -- equations
      ((\n -> do
           xs <- replicateM n (TH.newName "x")
           TH.tySynEqn Nothing
             -- lhs: TupleNtoNP m (m x1, .. m x_n)
             (TH.conT tf_tpl2np `TH.appT` TH.varT t_m `TH.appT` tupleNFromVarsTWith (TH.varT t_m `TH.appT`) xs)
             -- rhs: NP m '[x1, ... xn]
             (TH.conT ''NP `TH.appT` TH.varT t_m `TH.appT` promotedListFromVarsT xs)
       ) <$> [0..maxTupleN])

  -- class HavingFromTupleNPtoNP m tpl | tpl -> m where
  --   fromTupleNtoNP :: tpl %p -> TupleNtoNP m tpl
  -- -- instance HavingFromTupleNPtoNP m () -- bad: non-injective
  -- instance HavingFromTupleNPtoNP m (Solo (m a))
  -- instance HavingFromTupleNPtoNP m (m a1, m a2)
  decs_cls_tpl2np <- do
    -- class definition
    cls <- TH.classD
           (pure []) -- context
           cls_tpl2np
           [TH.plainTV t_m, TH.plainTV t_tpl] -- bound variables
           [TH.funDep [t_tpl] [t_m]]
           [TH.sigD fn_tpl2np ( TH.mulArrowT `TH.appT` TH.varT t_p `TH.appT` TH.varT t_tpl `TH.appT`
                                (TH.conT tf_tpl2np `TH.appT` TH.varT t_m `TH.appT` TH.varT t_tpl)
                              )]
    insts <- mapM
      (\n -> do
          xs <- replicateM n (TH.newName "x")
          TH.instanceD
            (pure []) -- context
            (TH.conT cls_tpl2np `TH.appT` TH.varT t_m `TH.appT` tupleNFromVarsTWith (TH.varT t_m `TH.appT`) xs)
            -- fromTupleNtoNP (x1, .. xn) = x1 :* ... xn :* Nil
            [TH.funD fn_tpl2np
             [ TH.clause
               [TH.tupP (map TH.varP xs)]
               (TH.normalB $ foldr ((\a b -> TH.infixE (Just a) (TH.conE '(:*)) (Just b)) . TH.varE) (TH.conE 'Nil) xs)
               []]]
      ) [1..maxTupleN]
    pure $ cls : insts

  ----------------------------------------------------------------------------------
  -- NPtoTupleN, HavingFromNPtoTupleN
  ----------------------------------------------------------------------------------

  tf_np2tpl <- TH.newName "NPtoTupleN"
  cls_np2tpl <- TH.newName "HavingFromNPtoTupleN"
  fn_np2tpl <- TH.newName "fromNPtoTupleN"

  -- type family NPtoTupleN m np = r | r -> m np where
  --   -- NPtoTupleN m (NP m '[]) = () -- this violates the injectivity
  --   NPtoTupleN m (NP m '[x]) = (Solo (m x))
  --   NPtoTupleN m (NP m '[x1, x2]) = (m x1, m x2)
  dec_tf_np2tpl <- do
    TH.closedTypeFamilyD tf_np2tpl [TH.plainTV t_m, TH.plainTV t_np]
      (TH.tyVarSig (TH.plainTV t_r)) (Just (TH.injectivityAnn t_r [t_m, t_np]))
      ((\n -> do
           xs <- replicateM n (TH.newName "x")
           TH.tySynEqn Nothing
             (TH.conT tf_np2tpl `TH.appT` TH.varT t_m `TH.appT`
              (TH.conT ''NP `TH.appT` TH.varT t_m `TH.appT` promotedListFromVarsT xs))
             (tupleNFromVarsTWith (TH.varT t_m `TH.appT`) xs)
       ) <$> [1..maxTupleN])

  -- class HavingFromNPtoTupleN m np | np -> m where
  --   fromNPtoTupleN :: np %p -> NPtoTupleN m np
  -- -- instance HavingFromNPtoTupleN m (NP m '[]) where -- no NPtoTupleN
  -- instance HavingFromNPtoTupleN m (NP m '[a]) where
  -- instance HavingFromNPtoTupleN m (NP m '[a1, a2]) where
  decs_cls_np2tpl <- do
    let np_p = foldr ((\a b -> TH.infixP a '(:*) b) . TH.varP) (TH.conP 'Nil [])
    cls <- TH.classD
           (pure []) -- context
           cls_np2tpl
           [TH.plainTV t_m, TH.plainTV t_np] -- bound variables
           [TH.funDep [t_np] [t_m]]
           [ TH.sigD fn_np2tpl
             (TH.mulArrowT `TH.appT` TH.varT t_p `TH.appT` TH.varT t_np `TH.appT`
              -- (TH.conT tf_np2tpl `TH.appT` TH.varT t_m `TH.appT` TH.varT t_np)
              (TH.conT tf_tplm `TH.appT` TH.varT t_m `TH.appT` (TH.conT ''NP2List `TH.appT` TH.varT t_np))
             )
           ]
    insts <- mapM
      (\n -> do
          xs <- replicateM n (TH.newName "x")
          TH.instanceD (pure [])
            (TH.conT cls_np2tpl `TH.appT`
             TH.varT t_m `TH.appT`
             (TH.conT ''NP `TH.appT` TH.varT t_m `TH.appT` promotedListFromVarsT xs))

            [ -- fromNPtoTupleN (x1 :* .. :* Nil) = (x1, ..)
              TH.funD fn_np2tpl
              [ TH.clause
                [np_p xs]
                (TH.normalB $ TH.tupE $ fmap TH.varE xs)
                []]]
      ) [1..maxTupleN]
    pure $ cls : insts

  pure $
    (dec_tf_tpl2np : decs_cls_tpl2np) <>
    (dec_tf_np2tpl : decs_cls_np2tpl) <>
    [dec_tpl, dec_tplm]

-- FIXME: to move
class TupleNWithSameM tpl
instance TupleNWithSameM (Solo (m x))
instance m1 ~ m2 => TupleNWithSameM (m1 x1, m2 x2)
instance (m1 ~ m2, m2 ~ m3) => TupleNWithSameM (m1 x1, m2 x2, m3 x3)

-- | A constraint alias for TupleN types that are convertible to NP and vice versa.
type ConvertibleTupleNtoNP m tpl = ( NPtoTupleN m (TupleNtoNP m tpl) ~ tpl
                                   , TupleN_M m (NP2List (TupleNtoNP m tpl)) ~ tpl
                                   , HavingFromTupleNtoNP m tpl
                                   , HavingFromNPtoTupleN m (TupleNtoNP m tpl)
                                   )

-- | A constraint alias for NP types that are convertible to TupleN and vice versa.
type ConvertibleNPtoTupleN m np = ( TupleNtoNP m (NPtoTupleN m np) ~ np
                                  , TupleN_M m (NP2List np) ~ NPtoTupleN m np
                                  , HavingFromTupleNtoNP m (NPtoTupleN m np)
                                  , HavingFromNPtoTupleN m np
                                  )
