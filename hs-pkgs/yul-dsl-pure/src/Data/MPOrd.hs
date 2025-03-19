{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LinearTypes            #-}
{-|

Copyright   : (c) 2024-2025 Miao, ZhiCheng
License     : LGPL-3

Maintainer  : hellwolf@yolc.dev
Stability   : experimental
Portability : GHC2024

This module provides the ordering related type classes suitable for eDSLs using multi-parameters (MP) type classes.

-}
module Data.MPOrd where

-- | Multi-parameter equality type class where boolean type is @b@
class MPEq a b | a -> b where
  (==) :: forall. a %1-> a %1-> b
  (/=) :: forall. a %1-> a %1-> b

-- | Multi-parameter ordering type class where boolean type is @b@
class MPEq a b => MPOrd a b | a -> b where
  ( <) :: forall. a %1-> a %1-> b
  (<=) :: forall. a %1-> a %1-> b
  ( >) :: forall. a %1-> a %1-> b
  (>=) :: forall. a %1-> a %1-> b

-- To be consistent with base library.
infixr 4 <, <=, >, >=, ==, /=
