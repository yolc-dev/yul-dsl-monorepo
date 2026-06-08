{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LinearTypes            #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-|

Copyright   : (c) 2024-2025 Miao, ZhiCheng
License     : MIT

Maintainer  : hellwolf@yolc.dev
Stability   : experimental
Portability : GHC2024

= Description

This module provides a set of type families and classes to work with function signatures that can be converted back and
forth between their currying forms and uncurrying forms.

Additionally, the design of this module is highly polymorphic including multiplicity-polymorphic on function arrows.

-}
module Data.Type.Function
  (
  ) where
-- base
