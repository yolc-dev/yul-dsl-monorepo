{-# LANGUAGE TemplateHaskell #-}
{-|

Copyright   : (c) 2024 Miao, ZhiCheng
License     : MIT

Maintainer  : hellwolf@yolc.dev
Stability   : experimental
Portability : GHC2024

The template haskell code for TupleN and NP utilities.

-}
module Data.TupleN.TH
  ( -- | Define TupleNtoNP closed type family using template haskell.
    TupleNtoNP
    -- | Convert a TupleN to its corresponding NP.
  , FromTupleNtoNP (fromTupleNtoNP)
    -- | Define NPtoTupleN closed type family using template haskell.
  , NPtoTupleN
    -- | Convert a NP to its corresponding tupleN.
  , FromNPtoTupleN (fromNPtoTupleN)
  ) where

-- base
import Control.Monad       (replicateM)
-- template-haskell
import Language.Haskell.TH qualified as TH
--
import Data.SimpleNP


do
  let tuple_n_t xs = foldl' TH.appT (TH.tupleT (length xs)) (map TH.varT xs)
  let promoted_list_t = foldr (TH.appT . TH.appT TH.promotedConsT . TH.varT) TH.promotedNilT
  tfName <- TH.newName "TupleNtoNP"
  -- type family TupleNtoNP t where
  --   TupleNtoNP () = NP '[]
  --   TupleNtoNP (Solo x) = NP '[x]
  --   TupleNtoNP (x1, x2) = NP '[x1, x2]
  tfDec <- do
    tfArg <- TH.newName "t"
    TH.closedTypeFamilyD tfName [TH.plainTV tfArg] TH.noSig Nothing
      ( map (\n -> do
                xs <- replicateM n (TH.newName "x")
                TH.tySynEqn Nothing
                  -- lhs: TupleNtoNP (x1, .. xm)
                  (TH.conT tfName `TH.appT` tuple_n_t xs)
                  -- rhs: NP '[x1, ... xn]
                  (TH.conT ''NP `TH.appT` promoted_list_t xs)
            ) [0..64]
      )
  -- class FromTupleNPtoNP a where
  clsInstsDec <- do
    clsName <- TH.newName "FromTupleNtoNP"
    fnName <- TH.newName "fromTupleNtoNP"
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
                        (TH.conT clsName `TH.appT` tuple_n_t xs)
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

do
  let tuple_n_t xs = foldl' TH.appT (TH.tupleT (length xs)) (map TH.varT xs)
  let promoted_list_t = foldr (TH.appT . TH.appT TH.promotedConsT . TH.varT) TH.promotedNilT
  tfName <- TH.newName "NPtoTupleN"
  -- type family NPtoTupleN t where
  --   NPtoTupleN (NP '[]) = ()
  --   NPtoTupleN (NP '[x]) = x -- We don't like Solo.
  --   NPtoTupleN (NP '[x1, x2]) = (x1, x2)
  tfDec <- do
    --x <- fmap TH.varT (TH.newName "x") -- for Solo
    tfArg <- TH.newName "t"
    TH.closedTypeFamilyD tfName [TH.plainTV tfArg] TH.noSig Nothing $
      -- Special equation for Solo
      -- [ TH.tySynEqn Nothing
      --   (TH.conT tfName `TH.appT`
      --     (TH.conT ''NP `TH.appT` (TH.appT TH.promotedConsT x `TH.appT` TH.promotedNilT))
      --   )
      --   x
      -- ] ++
      -- Equations for unit, and 2+ tuples
      map (\n -> do
              xs <- replicateM n (TH.newName "x")
              TH.tySynEqn Nothing
                (TH.conT tfName `TH.appT` (TH.conT ''NP `TH.appT` promoted_list_t xs))
                (tuple_n_t xs)
          ) ([0..64])
  -- class FromNPtoTupleN a where
  --   fromNPtoTupleN :: forall. a -> NPtoTupleN a
  clsInstsDec <- do
    let np_p = foldr ((\a b -> TH.infixP a '(:*) b) . TH.varP) (TH.conP 'Nil [])
    clsName <- TH.newName "FromNPtoTupleN"
    fnName <- TH.newName "fromNPtoTupleN"
    clsArg <- TH.newName "a"
    pArg <- TH.newName "p" -- multiplicity
    cls <- TH.classD (pure []) clsName [TH.plainTV clsArg] []
           [TH.sigD fnName (TH.mulArrowT `TH.appT` TH.varT pArg `TH.appT`
                            TH.varT clsArg `TH.appT`
                            (TH.conT tfName `TH.appT` TH.varT clsArg))]
    -- special instance for Solo:
    -- fromNPtoTupleN (x :* Nil) = x -- Not: (MkSolo s)
    -- soloInst <- do
    --   x <- TH.newName "x"
    --   TH.instanceD (pure [])
    --     (TH.conT clsName `TH.appT` (TH.conT ''NP `TH.appT` promoted_list_t [x]))
    --     [TH.funD fnName [TH.clause [np_p [x]] (TH.normalB $ TH.varE x) []]]
    insts <- mapM (\n -> do
                      xs <- replicateM n (TH.newName "x")
                      -- fromNPtoTupleN (x1 :* .. :* Nil) = (x1, ..)
                      TH.instanceD (pure [])
                        (TH.conT clsName `TH.appT` (TH.conT ''NP `TH.appT` promoted_list_t xs))
                        [TH.funD fnName [ TH.clause [np_p xs] (TH.normalB $ TH.tupE $ map TH.varE xs) []]]
                  ) ([0..64])
    pure $ cls : insts
  pure $ tfDec : clsInstsDec
