{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LinearTypes         #-}
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
  , UncurryNP'Head, UncurryNP'Tail
  , CurryNP, CurryNP_I
  , EquivalentNPOfFunction
  , UncurriableNP (uncurryNP), UncurriableNPDistributed, uncurryNPDistributed
  , CurriableNP (curryNP)
  , CallableFunctionNP (call), CallableFunctionN (callN)
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
  UncurryNP'Fst (x1 -> g) = x1 : UncurryNP'Fst (g)
  UncurryNP'Fst       (b) = '[]

-- | Uncurry the result of a function.
type family UncurryNP'Snd (f :: Type) :: Type where
  UncurryNP'Snd (_ -> g) = UncurryNP'Snd (g)
  UncurryNP'Snd      (b) = b

-- | Uncurry and extract the multiplicity of the last arrow.
type family UncurryNP'Multiplicity f :: Multiplicity where
  UncurryNP'Multiplicity (x1 %p-> b) = p
  UncurryNP'Multiplicity         (b) = Many

-- | Uncurry a function to its NP form whose multiplicity of the last arrow is preserved.
type UncurryNP m f = NP m (UncurryNP'Fst f) %(UncurryNP'Multiplicity f) -> UncurryNP'Snd f

-- | The type of the tail of an currying function.
type family UncurryNP'Tail f where
  UncurryNP'Tail (_ -> g) = g
  UncurryNP'Tail      (b) = b

-- | The type of the head of arguments of an currying function.
type family UncurryNP'Head f where
  UncurryNP'Head (a1 -> g) = a1
  UncurryNP'Head       (b) = ()

-- | Convert a function in ts "NP m" form @np -> b@ to a curried function with multiplicity arrows in @p@.
type family CurryNP np mb p where
  CurryNP (NP m    '[]) mb _ = mb
  CurryNP (NP m (x:xs)) mb p = m x %p -> CurryNP (NP m xs) mb p

-- | Convert a function in ts "NP I" form @np -> b@ to a curried function.
type family CurryNP_I np b where
  CurryNP_I (NP I    '[]) b = b
  CurryNP_I (NP I (x:xs)) b = x -> CurryNP_I (NP I xs) b

-- | Declare the equivalence between a currying function form @f@ and @NP xs -> b@.
type EquivalentNPOfFunction f xs b =
  ( CurryNP_I (NP I xs) b ~ f
  , UncurryNP'Fst f ~ xs
  , UncurryNP'Snd f ~ b
  )

-- | Uncurry a function into a function of @NP m2 xs@ to @m2b b@.
class UncurriableNP xs b m1 m1b p1 m2 m2b p2 | m1 m1b -> p1, m2 -> p2 where
  -- | Uncurry a NP-curried n-ary function into a sequenced-NP function 2-ary function.
  uncurryNP :: forall.
    CurryNP (NP m1 xs) (m1b b) p1 %p2 -> -- ^ from this lifted function. NOTE: using p2 to be consumed by m2.
    (m2 (NP I xs) %p2 -> m2b b)          -- ^ to this lifted function

type UncurriableNPDistributed xs b m1 m1b m2 m2b p2 =
  ( UncurriableNP xs b m1 m1b Many m2 m2b p2
  , TraversableNP m2 xs
  )

uncurryNPDistributed :: forall m1 m1b m2 m2b p2 xs b.
  UncurriableNPDistributed xs b m1 m1b m2 m2b p2 =>
  CurryNP (NP m1 xs) (m1b b) Many %p2 ->
  (NP m2 xs -> m2b b)
uncurryNPDistributed f xs_np = uncurryNP @xs @b @m1 @m1b @_ @m2 @m2b @_ f (sequence_NP xs_np)

-- | Curry a function of @NP m1 xs@ to @mb b@.
class CurriableNP xs b m2 mb p2 m1 p1 | m2 mb -> p2, m1 -> p1 where
  curryNP :: forall.
    (m2 (NP I xs) %p2 -> mb b) %p1 -> -- ^ from this lifted function. NOTE: using p1 to be consumed by m1.
    CurryNP (NP m1 xs) (mb b) p1      -- ^ to this lifted function

class EquivalentNPOfFunction f xs b =>
      CallableFunctionNP fn f xs b m mb p | fn mb -> m p where
  call :: forall. fn f -> CurryNP (NP m xs) (mb b) p

class ( EquivalentNPOfFunction f xs b
      , ConvertibleNPtoTupleN m (NP m xs)
      ) =>
      CallableFunctionN fn f xs b m mb p | fn mb -> m p where
  callN :: forall. fn f -> TupleN_M m xs %p -> mb b
