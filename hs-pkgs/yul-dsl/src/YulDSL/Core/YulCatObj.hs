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
  , YulO1, YulO2, YulO3, YulO4, YulO5, YulO6
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

--
-- Shorthand for declaring multi-objects constraint:
--

type YulO1 a = YulCatObj a
type YulO2 a b = (YulCatObj a, YulO1 b)
type YulO3 a b c = (YulCatObj a, YulO2 b c)
type YulO4 a b c d = (YulCatObj a, YulO3 b c d)
type YulO5 a b c d e = (YulCatObj a, YulO4 b c d e)
type YulO6 a b c d e g = (YulCatObj a, YulO5 b c d e g)

--
-- Enumerate known YulCat objects:
--

-- NP
instance YulCatObj (NP '[])
instance (YulCatObj x, YulCatObj (NP xs)) => YulCatObj (NP (x:xs))

-- TupleN (3..15)
instance YulCatObj ()
instance YulCatObj a => YulCatObj (Solo a)
instance (YulCatObj a1, YulCatObj a2) => YulCatObj (a1, a2) where yul_prod_objs = Dict
do
  insts <- mapM
    (\n -> do
      as <- replicateM n (TH.newName "a")
      -- NOTE! Haskell2010 only demands the Show instance to support up to Tuple15
      [d| instance $(tupleNFromVarsTWith (TH.conT ''YulCatObj `TH.appT`) as) =>
                   YulCatObj $(tupleNFromVarsT as)
        |]
    ) [3..15]
  pure (concat insts)

-- Value Types
instance YulCatObj BOOL
instance ValidINTx s n => YulCatObj (INTx s n)
instance YulCatObj ADDR
instance ValidINTn n => YulCatObj (BYTESn n)

-- REF
instance YulCatObj a => YulCatObj (REF a)
