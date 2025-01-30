{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LinearTypes         #-}
{-|

Copyright   : (c) 2024 Miao, ZhiCheng
License     : MIT

Maintainer  : hellwolf@yolc.dev
Stability   : experimental
Portability : GHC2024

= Description

A simple n-ary product without any type function.

Instead, it comes with a set of type families to work with function signatures that can be converted back and forth
between their currying forms and uncurrying forms.

Additionally, these type families are multiplicity-polymorphic to function arrows.

-}
module Data.SimpleNP
  ( Multiplicity (Many, One)
  , NP (Nil, (:*))
  , LiftFunction
  , UncurryNP'Fst, UncurryNP'Snd, UncurryNP'Multiplicity, UncurryNP, EquivalentNPOfFunction
  , CurryNP
  , CurryingNP'Head, CurryingNP'Tail
  , CurryingNP (curryingNP), UncurryingNP(uncurryingNP)
  , module Internal.Data.Type.List
  ) where

-- base
import Data.Kind               (Type)
import GHC.Base                (Multiplicity (..))
--
import Internal.Data.Type.List


-- | N-ary product without a type function comparing to its homonym in the "sop" package.
data NP :: [Type] -> Type where
  Nil  :: NP '[]
  (:*) :: x %1-> NP xs %1-> NP (x : xs)
infixr 5 :*

--
-- Type level functions for NP
--

-- | Lift a currying function type from its simplified form, denoted as @f@, into a new form.
--
--   This lifted function consists of a type function, @m@, for each argument, followed by a multiplicity arrow of @p@,
--   and uses a type function @mb@, for the result of the lifted function.
type family LiftFunction (f :: Type) (m  :: Type -> Type) (mb :: Type -> Type) (p :: Multiplicity) where
  LiftFunction  (x1 -> g) m mb p = m x1 %p-> LiftFunction g m mb p
  LiftFunction        (b) _ mb _ = mb b

-- | Uncurry the arguments of a function to a list of types.
type family UncurryNP'Fst f :: [Type] where
  UncurryNP'Fst (x1 %_-> g) = x1 : UncurryNP'Fst (g)
  UncurryNP'Fst         (b) = '[]

-- | Uncurry the result of a function.
type family UncurryNP'Snd (f :: Type) where
  UncurryNP'Snd (_ %_-> g) = UncurryNP'Snd (g)
  UncurryNP'Snd        (b) = b

-- | Uncurry and extract the multiplicity of the last arrow.
type family UncurryNP'Multiplicity (f :: Type) :: Multiplicity where
  UncurryNP'Multiplicity         (x1 %p-> b) = p
  UncurryNP'Multiplicity                 (b) = Many

-- | Uncurry a function to its NP form whose multiplicity of the last arrow is preserved.
type UncurryNP f = NP (UncurryNP'Fst f) %(UncurryNP'Multiplicity f)-> UncurryNP'Snd f

-- | Convert a function in ts NP form @np -> b@ to a curried function with multiplicity arrows in @p@.
--
--   Note: To add multiplicity-polymorphic arrows or to decorate arguments with additional type function, use
--   'LiftFunction'.
type family CurryNP (np :: Type) (b :: Type) where
  CurryNP (NP    '[]) b = b
  CurryNP (NP (x:xs)) b = x -> CurryNP (NP xs) b

-- | Declare the equivalence between a currying function form @f@ and @NP xs -> b@.
type EquivalentNPOfFunction f xs b =
  ( CurryNP (NP xs) b ~ f -- Note! The order of this constraint line seems matter here.
  , UncurryNP'Fst f ~ xs
  , UncurryNP'Snd f ~ b
  )

--
-- Type classes for defining uncurrying/currying functions for NP
--

-- | The type of the head of arguments of an currying function.
type family CurryingNP'Head f where
  CurryingNP'Head (a1 %_-> g) = a1
  CurryingNP'Head         (b) = ()

-- | The type of the tail of an currying function.
type family CurryingNP'Tail f where
  CurryingNP'Tail (_ %_-> g) = g
  CurryingNP'Tail        (b) = b

-- | Uncurrying a function into a function of @NP xs@ to @b@.
class UncurryingNP f (xs :: [Type]) b
      (m1 :: Type -> Type) (m1b :: Type -> Type)
      (m2 :: Type -> Type) (m2b :: Type -> Type)
      (p :: Multiplicity) where
  uncurryingNP :: forall.
                  ( UncurryNP'Fst f ~ xs
                  , UncurryNP'Snd f ~ b
                  -- rewrite the second lift function into its one-arity form
                  , LiftFunction (NP xs -> b) m2 m2b p ~ (m2 (NP xs) %p-> m2b b)
                  )
               => LiftFunction           f  m1 m1b p  -- ^ from this lifted function
             %p-> LiftFunction (NP xs -> b) m2 m2b p  -- ^ to this lifted function

-- | Currying a function of @NP xs@ to @b@.
class CurryingNP (xs :: [Type]) b
      (m1 :: Type -> Type) (mb :: Type -> Type)
      (m2 :: Type -> Type)
      (p :: Multiplicity) where
  curryingNP :: forall f.
                ( CurryNP (NP xs) b ~ f
                -- rewrite the first lift function into its one-arity form
                , LiftFunction (NP xs -> b) m2 mb p ~ (m2 (NP xs) %p-> mb b)
                )
             => LiftFunction (NP xs -> b) m2 mb p -- ^ from this lifted function
           %p-> LiftFunction           f  m1 mb p -- ^ to this lifted function

--
-- base instances
--

deriving instance Eq (NP ('[]))
deriving instance (Eq x, Eq (NP xs)) => Eq (NP (x:xs))

instance Show (NP '[]) where
  show _ = "Nil"

instance (Show x, Show (NP xs)) => Show (NP (x:xs)) where
  show (x :* xs) = "(" ++ show x ++ " :* " ++ show xs ++ ")"
