{-|
Copyright   : (c) 2025 Miao, ZhiCheng
License     : LGPL-3
Maintainer  : hellwolf@yolc.dev
Stability   : experimental

= Description

This module provides type class and data types for defining yul built-in functions.

-}
{-# LANGUAGE OverloadedStrings #-}
module YulDSL.Core.YulBuiltIn
  ( YulBuiltInPrefix (yulB_prefix , yulB_fname)
  ) where
-- base
import GHC.TypeLits                (KnownSymbol (symbolSing), Symbol, fromSSymbol)
-- text
-- (codegen-util)


-- | Yul built-in definition.
class KnownSymbol prefix => YulBuiltInPrefix (prefix :: Symbol) a b where
  yulB_prefix :: forall. YulBuiltIn prefix a b -> String
  yulB_prefix _ = fromSSymbol $ symbolSing @prefix
  -- | Yul function name for the built-in.
  yulB_fname :: forall. YulBuiltIn prefix a b -> String
  -- | Optional yul function body, which consists of in-vars, out-vars, lines of code, and built-in dependencies.

-- | Reference to an instance of yul built-in by its prefix @p@, domain and codomain types @a -> b@.
data YulBuiltIn p a b where
  MkYulBuiltIn :: forall p a b. YulBuiltInPrefix p a b => YulBuiltIn p a b

