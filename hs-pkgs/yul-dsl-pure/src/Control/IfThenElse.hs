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

-- | IfThenElse type class useful for rebindable syntax.
class IfThenElse a b where
  -- | The ifThenElse function.
  ifThenElse :: forall. a -> b -> b -> b
