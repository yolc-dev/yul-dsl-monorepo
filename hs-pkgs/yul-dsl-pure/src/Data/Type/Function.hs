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
  ( LiftFunction
  , UncurryNP'Fst, UncurryNP'Snd, UncurryNP'Multiplicity, UncurryNP
  , CurryNP, CurryNP'Head, CurryNP'Tail
  , EquivalentNPOfFunction
  , UncurriableNP (uncurryNP)
  , CurriableNP (curryNP)
  , CallableFunctionNP (call), CallableFunctionN (callN, (<$*>))
  ) where
-- base
import Data.Kind     (Type)
--
import Data.SimpleNP
import Data.TupleN


-- | Lift a currying function type from its simplified form, denoted as @f@, into a new form.
--
--   This lifted function consists of a type function, @m@, for each argument, followed by a multiplicity arrow of @p@,
--   and uses a type function @mb@, for the result of the lifted function.
type family LiftFunction f (m  :: Type -> Type) (mb :: Type -> Type) (p :: Multiplicity) where
  LiftFunction (x1 -> g) m mb p = m x1 %p-> LiftFunction g m mb p
  LiftFunction       (b) _ mb _ = mb b

-- | Uncurry the arguments of a function to a list of types.
type family UncurryNP'Fst f :: [Type] where
  UncurryNP'Fst (x1 %_-> g) = x1 : UncurryNP'Fst (g)
  UncurryNP'Fst         (b) = '[]

-- | Uncurry the result of a function.
type family UncurryNP'Snd (f :: Type) where
  UncurryNP'Snd (_ %_-> g) = UncurryNP'Snd (g)
  UncurryNP'Snd        (b) = b

-- | Uncurry and extract the multiplicity of the last arrow.
type family UncurryNP'Multiplicity f :: Multiplicity where
  UncurryNP'Multiplicity (x1 %p-> b) = p
  UncurryNP'Multiplicity         (b) = Many

-- | Uncurry a function to its NP form whose multiplicity of the last arrow is preserved.
type UncurryNP f = NP (UncurryNP'Fst f) %(UncurryNP'Multiplicity f)-> UncurryNP'Snd f

-- | Convert a function in ts NP form @np -> b@ to a curried function with multiplicity arrows in @p@.
--
--   Note: To add multiplicity-polymorphic arrows or to decorate arguments with additional type function, use
--   'LiftFunction'.
type family CurryNP np b where
  CurryNP (NP    '[]) b = b
  CurryNP (NP (x:xs)) b = x -> CurryNP (NP xs) b

-- | The type of the head of arguments of an currying function.
type family CurryNP'Head f where
  CurryNP'Head (a1 %_-> g) = a1
  CurryNP'Head         (b) = ()

-- | The type of the tail of an currying function.
type family CurryNP'Tail f where
  CurryNP'Tail (_ %_-> g) = g
  CurryNP'Tail        (b) = b

-- | Declare the equivalence between a currying function form @f@ and @NP xs -> b@.
type EquivalentNPOfFunction f xs b =
  ( CurryNP (NP xs) b ~ f
  , UncurryNP'Fst f ~ xs
  , UncurryNP'Snd f ~ b
  )

-- | Uncurry a function into a function of @NP xs@ to @b@.
class ( EquivalentNPOfFunction f xs b
      , LiftFunction b m1 m1b p1 ~ m1b b
      -- rewrite the second lift function into its one-arity form
      , LiftFunction (NP xs -> b) m2 m2b p2 ~ (m2 (NP xs) %p2 -> m2b b)
      ) =>
      UncurriableNP f xs b m1 m1b p1 m2 m2b p2 | m1 m1b -> p1, m2 -> p2 where
  uncurryNP :: forall.
    LiftFunction           f  m1 m1b p1 %p2 -> -- ^ from this lifted function. NOTE: using p2 to be consumed by m2.
    LiftFunction (NP xs -> b) m2 m2b p2        -- ^ to this lifted function

-- | Curry a function of @NP xs@ to @b@.
class ( EquivalentNPOfFunction f xs b
      , LiftFunction b m1 mb p1 ~ mb b
      -- rewrite the first lift function into its one-arity form
      , LiftFunction (NP xs -> b) m2 mb p1 ~ (m2 (NP xs) %p1 -> mb b)
      ) =>
      CurriableNP f xs b m2 mb p2 m1 p1 | m2 mb -> p2, m1 -> p1 where
  curryNP :: forall.
    LiftFunction (NP xs -> b) m2 mb p2 %p1 -> -- ^ from this lifted function. NOTE: using p1 to be consumed by m1.
    LiftFunction           f  m1 mb p1        -- ^ to this lifted function

class ( EquivalentNPOfFunction f (x:xs) b
      ) =>
      CallableFunctionNP fn f x xs b m mb p | fn m -> mb p where
  call :: forall. fn f -> (m x %p -> LiftFunction (CurryNP (NP xs) b) m mb p)

class ( EquivalentNPOfFunction f xs b
      , ConvertibleNPtoTupleN (NP (MapList m xs))
      ) =>
      CallableFunctionN fn f xs b m mb p | fn mb -> m p where
  callN, (<$*>) :: forall. fn f -> NPtoTupleN (NP (MapList m xs)) %p -> mb b
  (<$*>) = callN
