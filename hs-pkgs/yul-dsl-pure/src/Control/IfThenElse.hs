{-# LANGUAGE LinearTypes #-}
{-|

Copyright   : (c) 2024-2025 Miao, ZhiCheng
License     : LGPL-3

Maintainer  : hellwolf@yolc.dev
Stability   : experimental
Portability : GHC2024

-}
module Control.IfThenElse where

-- | IfThenElse type class for enabling rebindable syntax.
class IfThenElse a b where
  -- | The ifThenElse function.
  ifThenElse :: forall w. a %w -> b %w -> b %w -> b
