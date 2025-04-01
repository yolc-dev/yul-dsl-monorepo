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

It supports up to 64-ary tuple.

-}
module Data.TupleN
  ( TupleNtoNP, FromTupleNtoNP (fromTupleNtoNP)
  , NPtoTupleN, FromNPtoTupleN (fromNPtoTupleN)
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
  tfName <- TH.newName "TupleNtoNP"
  clsName <- TH.newName "FromTupleNtoNP"
  fnName <- TH.newName "fromTupleNtoNP"

  -- type family TupleNtoNP t = r | r -> t where
  --   TupleNtoNP () = NP '[]
  --   TupleNtoNP (Solo x) = NP '[x]
  --   TupleNtoNP (x1, x2) = NP '[x1, x2]
  tfDec <- do
    tfArg <- TH.newName "t"
    tfResult <- TH.newName "r"
    TH.closedTypeFamilyD tfName [TH.plainTV tfArg]
      (TH.tyVarSig (TH.plainTV tfResult)) (Just (TH.injectivityAnn tfResult [tfArg]))
      ( map (\n -> do
                xs <- replicateM n (TH.newName "x")
                TH.tySynEqn Nothing
                  -- lhs: TupleNtoNP (x1, .. xm)
                  (TH.conT tfName `TH.appT` tupleNFromVarsT xs)
                  -- rhs: NP '[x1, ... xn]
                  (TH.conT ''NP `TH.appT` promotedListFromVarsT xs)
            ) [0..64]
      )

  -- class FromTupleNPtoNP a where
  clsInstsDec <- do
    clsArg <- TH.newName "a"
    pArg <- TH.newName "p" -- multiplicity
    cls <- TH.classD (pure []) clsName [TH.plainTV clsArg] []
           -- fromTupleNtoNP :: forall. a -> TupleNtoNP a
           [TH.sigD fnName (TH.mulArrowT `TH.appT` TH.varT pArg `TH.appT`
                            TH.varT clsArg `TH.appT`
                            (TH.conT tfName `TH.appT` TH.varT clsArg))]
    insts <- mapM (\n -> do
                      xs <- replicateM n (TH.newName "x")
                      TH.instanceD (pure [])
                        (TH.conT clsName `TH.appT` tupleNFromVarsT xs)
                        [TH.funD fnName [ TH.clause
                                          [TH.tupP (map TH.varP xs)]
                                          (TH.normalB $
                                            foldr
                                            ((\a b -> TH.infixE (Just a) (TH.conE '(:*)) (Just b)) . TH.varE)
                                            (TH.conE 'Nil)
                                            xs)
                                          []
                                        ]
                        ]
                 ) [0..64]
    pure $ cls : insts

  pure $ tfDec : clsInstsDec

--
-- NPtoTupleN, FromNPtoTupleN (fromNPtoTupleN)
--
do
  tfName <- TH.newName "NPtoTupleN"
  clsName <- TH.newName "FromNPtoTupleN"
  fnName <- TH.newName "fromNPtoTupleN"

  -- type family NPtoTupleN t = r | r -> t where
  --   NPtoTupleN (NP '[]) = ()
  --   NPtoTupleN (NP '[x]) = (Solo x)
  --   NPtoTupleN (NP '[x1, x2]) = (x1, x2)
  tfDec <- do
    --x <- fmap TH.varT (TH.newName "x") -- for Solo
    tfArg <- TH.newName "t"
    tfResult <- TH.newName "r"
    TH.closedTypeFamilyD tfName [TH.plainTV tfArg]
      (TH.tyVarSig (TH.plainTV tfResult)) (Just (TH.injectivityAnn tfResult [tfArg]))
      ( map (\n -> do
                xs <- replicateM n (TH.newName "x")
                TH.tySynEqn Nothing
                  (TH.conT tfName `TH.appT` (TH.conT ''NP `TH.appT` promotedListFromVarsT xs))
                  (tupleNFromVarsT xs)
            ) ([0..64])
      )

  -- class FromNPtoTupleN a where
  --   fromNPtoTupleN :: forall. a -> NPtoTupleN a
  clsInstsDec <- do
    let np_p = foldr ((\a b -> TH.infixP a '(:*) b) . TH.varP) (TH.conP 'Nil [])
    clsArg <- TH.newName "a"
    pArg <- TH.newName "p" -- multiplicity
    cls <- TH.classD (pure []) clsName [TH.plainTV clsArg] []
           [TH.sigD fnName (TH.mulArrowT `TH.appT` TH.varT pArg `TH.appT`
                            TH.varT clsArg `TH.appT`
                            (TH.conT tfName `TH.appT` TH.varT clsArg))]
    insts <- mapM (\n -> do
                      xs <- replicateM n (TH.newName "x")
                      -- fromNPtoTupleN (x1 :* .. :* Nil) = (x1, ..)
                      TH.instanceD (pure [])
                        (TH.conT clsName `TH.appT` (TH.conT ''NP `TH.appT` promotedListFromVarsT xs))
                        [TH.funD fnName [ TH.clause [np_p xs] (TH.normalB $ TH.tupE $ map TH.varE xs) []]]
                  ) ([0..64])
    pure $ cls : insts

  pure $ tfDec : clsInstsDec

-- | A constraint alias for TupleN types that are convertible to NP and vice versa.
type ConvertibleTupleNtoNP tpl = ( NPtoTupleN (TupleNtoNP tpl) ~ tpl
                                 , FromTupleNtoNP tpl
                                 , FromNPtoTupleN (TupleNtoNP tpl)
                                 )

-- | A constraint alias for NP types that are convertible to TupleN and vice versa.
type ConvertibleNPtoTupleN np = ( TupleNtoNP (NPtoTupleN np) ~ np
                                , FromTupleNtoNP (NPtoTupleN np)
                                , FromNPtoTupleN np
                                )
