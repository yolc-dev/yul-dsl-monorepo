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
  ( UncurryNP'Fst, UncurryNP'Snd
  , EquivalentNPOfFunction
  ) where
-- base
import Data.Kind     (Type)
--
import Data.SimpleNP
import Data.TupleN


type family UncurryNP'Fst f :: [Type] where
  UncurryNP'Fst (x1 %_-> g) = x1 : UncurryNP'Fst (g)
  UncurryNP'Fst         (b) = '[]

-- | Uncurry the result of a function.
type family UncurryNP'Snd (f :: Type) where
  UncurryNP'Snd (_ %_-> g) = UncurryNP'Snd (g)
  UncurryNP'Snd        (b) = b

type EquivalentNPOfFunction f xs b =
  ( UncurryNP'Fst f ~ xs
  , UncurryNP'Snd f ~ b
  )
