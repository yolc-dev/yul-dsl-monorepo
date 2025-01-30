{-# LANGUAGE TemplateHaskell #-}
{-|

Copyright   : (c) 2023-2025 Miao, ZhiCheng
License     : LGPL-3
Maintainer  : hellwolf@yolc.dev
Stability   : experimental

= Description

This module defines the objects of the YulCat category.

-}
module YulDSL.Core.YulCatObj
  ( YulCatObj (yul_prod_objs)
  ) where
-- base
import Control.Monad        (replicateM)
-- constraints
import Data.Constraint      (Dict (Dict))
-- template-haskell
import Language.Haskell.TH  qualified as TH
-- eth-abi
import Ethereum.ContractABI


-- | All objects in the yul category is simply a 'YulCatObj'.
class (ABITypeable a, ABITypeCodec a, Show a) => YulCatObj a where
  -- | Possible breakdown of the product object of the category.
  yul_prod_objs :: forall b c. a ~ (b, c) => Dict (YulCatObj b, YulCatObj c)
  yul_prod_objs = error "yul_prod_objs should only be implemented by the product of YulCatObj"

-- Enumerate known YulCat objects:

instance YulCatObj a => YulCatObj (I a)
-- NP
instance YulCatObj (NP '[])
instance (YulCatObj x, YulCatObj (NP xs)) => YulCatObj (NP (x:xs))
-- Value Types
instance YulCatObj BOOL
instance ValidINTx s n => YulCatObj (INTx s n)
instance YulCatObj ADDR
instance ValidINTn n => YulCatObj (BYTESn n)
-- TupleN (3..15)
instance YulCatObj ()
instance YulCatObj a => YulCatObj (Solo a)
instance (YulCatObj a1, YulCatObj a2) => YulCatObj (a1, a2) where yul_prod_objs = Dict
do
  let mk_tuple_n_t xs = foldl' TH.appT (TH.tupleT (length xs)) (map TH.varT xs)
  insts <- mapM (\n -> do
    xs <- replicateM n (TH.newName "a")
    let tpl = mk_tuple_n_t xs
    let clist = foldr (\x b -> b `TH.appT` (TH.conT ''YulCatObj `TH.appT` TH.varT x)) (TH.tupleT n) xs
    -- NOTE! Haskell2010 only demands the Show instance to support up to Tuple15
    [d| instance $(clist) => YulCatObj $(tpl) |]) [3..15]
  pure (concat insts)
-- REF
instance YulCatObj a => YulCatObj (REF a)
