{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LinearTypes            #-}
{-|

Copyright   : (c) 2024-2025 Miao, ZhiCheng
License     : MIT

Maintainer  : hellwolf@yolc.dev
Stability   : experimental
Portability : GHC2024

= Description

A set of type families to work with function signatures that can be converted back and forth between their currying
forms and uncurrying forms.

Additionally, these type families are multiplicity-polymorphic to function arrows.

-}
module Data.Type.Function
  ( LiftFunction
  , UncurryNP'Fst, UncurryNP'Snd, UncurryNP'Multiplicity, UncurryNP
  , CurryNP, CurryingNP'Head, CurryingNP'Tail
  , EquivalentNPOfFunction
  , UncurryingNP(uncurryingNP), UncurriableNP
  , CurryingNP (curryingNP), CurriableNP
  , CallableFunction (callNP, (<$*>))
  -- re-export multiplicity types
  , Multiplicity (Many, One)
  ) where
-- base
import Data.Kind     (Type)
import GHC.Base      (Multiplicity (..))
--
import Data.SimpleNP


-- | Lift a currying function type from its simplified form, denoted as @f@, into a new form.
--
--   This lifted function consists of a type function, @m@, for each argument, followed by a multiplicity arrow of @p@,
--   and uses a type function @mb@, for the result of the lifted function.
type family LiftFunction (f :: Type) (m  :: Type -> Type) (mb :: Type -> Type) (p :: Multiplicity) where
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
type family UncurryNP'Multiplicity (f :: Type) :: Multiplicity where
  UncurryNP'Multiplicity (x1 %p-> b) = p
  UncurryNP'Multiplicity         (b) = Many

-- | Uncurry a function to its NP form whose multiplicity of the last arrow is preserved.
type UncurryNP f = NP (UncurryNP'Fst f) %(UncurryNP'Multiplicity f)-> UncurryNP'Snd f

-- | Convert a function in ts NP form @np -> b@ to a curried function with multiplicity arrows in @p@.
--
--   Note: To add multiplicity-polymorphic arrows or to decorate arguments with additional type function, use
--   'LiftFunction'.
type family CurryNP (np :: Type) (b :: Type) where
  CurryNP (NP    '[]) b = b
  CurryNP (NP (x:xs)) b = x -> CurryNP (NP xs) b

-- | The type of the head of arguments of an currying function.
type family CurryingNP'Head f where
  CurryingNP'Head (a1 %_-> g) = a1
  CurryingNP'Head         (b) = ()

-- | The type of the tail of an currying function.
type family CurryingNP'Tail f where
  CurryingNP'Tail (_ %_-> g) = g
  CurryingNP'Tail        (b) = b

-- | Declare the equivalence between a currying function form @f@ and @NP xs -> b@.
type EquivalentNPOfFunction f xs b =
  ( UncurryNP'Fst f ~ xs
  , UncurryNP'Snd f ~ b
  , CurryNP (NP xs) b ~ f
  )

-- | Uncurrying a function into a function of @NP xs@ to @b@.
class UncurryingNP f (xs :: [Type]) b
      (m1 :: Type -> Type) (m1b :: Type -> Type)
      (m2 :: Type -> Type) (m2b :: Type -> Type)
      (p :: Multiplicity) where
  uncurryingNP :: forall.
    ( UncurryNP'Fst f ~ xs, UncurryNP'Snd f ~ b
      -- rewrite the second lift function into its one-arity form
    , LiftFunction (NP xs -> b) m2 m2b p ~ (m2 (NP xs) %p-> m2b b)
    ) =>
    LiftFunction           f  m1 m1b p %p-> -- ^ from this lifted function
    LiftFunction (NP xs -> b) m2 m2b p      -- ^ to this lifted function

type UncurriableNP f xs b m1 m1b m2 m2b p =
  ( EquivalentNPOfFunction f xs b
  , UncurryingNP f xs b m1 m1b m2 m2b p
  , LiftFunction b m2 m2b p ~ m2b b
  )

-- | Currying a function of @NP xs@ to @b@.
class CurryingNP (xs :: [Type]) b
      (m1 :: Type -> Type) (mb :: Type -> Type)
      (m2 :: Type -> Type)
      (p :: Multiplicity) where
  curryingNP :: forall f.
    ( CurryNP (NP xs) b ~ f
      -- rewrite the first lift function into its one-arity form
    , LiftFunction (NP xs -> b) m2 mb p ~ (m2 (NP xs) %p-> mb b)
    ) =>
    LiftFunction (NP xs -> b) m2 mb p %p-> -- ^ from this lifted function
    LiftFunction           f  m1 mb p      -- ^ to this lifted function

type CurriableNP xs b m1 mb m2 p =
  ( CurryingNP xs b m1 mb m2 p
  , LiftFunction b m2 mb p ~ mb b
  )

class CallableFunction fn m mb p | fn -> m, fn -> mb, fn -> p where
  callNP, (<$*>) :: forall f x xs b.
    EquivalentNPOfFunction f xs b =>
    fn f -> (m x %p -> LiftFunction (CurryNP (NP xs) b) m mb p)
  (<$*>) = callNP @_ @_ @_ @_ @f @x @xs @b

{-|
>>> f foo a b c = (foo `callNP` a b c, foo <$*> a b c)
>>> :type f
-}
infixl 4 `callNP`, <$*>
