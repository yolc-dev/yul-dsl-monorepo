{-# LANGUAGE LinearTypes #-}
module Control.IfThenElse where

-- | IfThenElse for enabling rebindable syntax.
class IfThenElse a b where
  ifThenElse :: forall w. a %w -> b %w -> b %w -> b
