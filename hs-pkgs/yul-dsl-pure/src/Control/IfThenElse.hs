{-# LANGUAGE LinearTypes #-}
{-|

Copyright   : (c) 2024-2025 Miao, ZhiCheng
License     : LGPL-3

Maintainer  : hellwolf@yolc.dev
Stability   : experimental
Portability : GHC2024

This module provides the 'IfThenElse' type class for rebindable syntax.

-}
module Control.IfThenElse where
-- yul-dsl
import YulDSL.Core
import YulDSL.StdBuiltIns.ValueType ()


-- | IfThenElse type class useful for rebindable syntax.
class IfThenElse a b where
  -- | The ifThenElse function.
  ifThenElse :: forall w. a %w -> b %w -> b %w -> b

--
-- BOOL instance
--

-- ^ 'IfThenElse' instance for yul object 'BOOL'.
instance YulO2 a r => IfThenElse (YulCat eff r BOOL) (YulCat eff r a) where
  ifThenElse c a b = YulFork c YulId >.> YulITE a b
