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
  , YulSafeCastable (YulSafeCastBuiltin), YulCastable (YulCastBuiltin)
  , YulO1, YulO2, YulO3, YulO4, YulO5, YulO6
  , type (⊗)
  ) where
-- base
import Control.Monad        (replicateM)
-- constraints
import Data.Constraint      (Dict (Dict))
-- template-haskell
import Language.Haskell.TH  qualified as TH
-- eth-abi
import Ethereum.ContractABI
--
import YulDSL.Core.YulBuiltIn
import YulDSL.StdBuiltIns.ValueType ()


-- | All objects in the yul category is simply a 'YulCatObj'.
class (ABITypeable a, ABITypeCodec a, Show a) => YulCatObj a where
  -- | Possible breakdown of the product object of the category.
  yul_prod_objs :: forall b c. a ~ (b, c) => Dict (YulCatObj b, YulCatObj c)
  yul_prod_objs = error "yul_prod_objs should only be implemented by the product of YulCatObj"

class ( YulBuiltInPrefix (YulSafeCastBuiltin a b) a b
      , IsYulBuiltInNonPure (YulSafeCastBuiltin a b) ~ False
      ) =>
      YulSafeCastable a b where
  type family YulSafeCastBuiltin a b :: Symbol

class ( YulBuiltInPrefix (YulCastBuiltin a b) a (BOOL, b)
      , IsYulBuiltInNonPure (YulCastBuiltin a (BOOL, b)) ~ False
      ) =>
      YulCastable a b where
  type family YulCastBuiltin a b :: Symbol

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

instance YulCatObj a => YulCatObj (I a)

-- NP
instance YulCatObj (NP I '[])
instance (YulCatObj x, YulCatObj (NP I xs)) => YulCatObj (NP I (x:xs))

-- Unit / Terminal Object
instance YulCatObj ()

-- Solo tuple
instance YulCatObj a => YulCatObj (Solo a)

-- Tuple2
instance (YulCatObj a1, YulCatObj a2) => YulCatObj (a1, a2) where yul_prod_objs = Dict
type (⊗) a b = (a, b)
infixr 7 ⊗

-- Tuple 3..16
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

-- All unsigned int can be casted to u256
instance ValidINTn n => YulSafeCastable (INTx False n) U256 where
  type instance YulSafeCastBuiltin (INTx False n) U256 = "__safecast_uint_t_"
-- Boolean can be casted to any intx
instance ValidINTx s n => YulSafeCastable BOOL (INTx s n) where
  type instance YulSafeCastBuiltin BOOL (INTx s n) = "__safecast_bool_t_"

instance ValidINTx s n => YulCatObj (INTx s n)
instance YulCatObj ADDR
instance ValidINTn n => YulCatObj (BYTESn n)

-- REF
instance YulCatObj a => YulCatObj (REF a)
