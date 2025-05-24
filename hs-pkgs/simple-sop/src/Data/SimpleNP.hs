{-# LANGUAGE LinearTypes          #-}
{-# LANGUAGE UndecidableInstances #-}
{-|

Copyright   : (c) 2024-2025 Miao, ZhiCheng
License     : MIT

Maintainer  : hellwolf@yolc.dev
Stability   : experimental
Portability : GHC2024

= Description

A simplistic n-ary product implementation.

-}
module Data.SimpleNP
  ( -- * N-ary Product
    I (I)
  , NP (Nil, (:*)), NP2List
  , NonEmptyNP, splitNonEmptyNP
    -- re-export multiplicity types
  , Multiplicity (Many, One)
    -- * Traversable and Distributive for NP
  , TraversableNP (sequence_NP), DistributiveNP (distribute_NP)
  , ConstructibleNP (nil_NP, cons_NP, uncons_NP)
  , LinearTraversableNP (lsequence_NP), LinearDistributiveNP (ldistribute_NP)
  , LinearlyConstructibleNP (lunit2nil_NP, lnil2unit_NP, lcons_NP, luncons_NP)
  ) where
-- base
import Data.Kind (Type)
import GHC.Base  (Multiplicity (Many, One))


-- | An Identity type with shorter notation.
newtype I (a :: Type) = I a deriving (Functor, Foldable, Traversable, Show)

-- | N-ary product without a type function comparing to its homonym in the "sop" package.
data NP :: (k -> Type) -> [k] -> Type where
  Nil  :: NP f '[]
  (:*) :: f x %1 -> NP f xs %1 -> NP f (x : xs)

-- ^ Same as in sop-core package.
infixr 5 :*

-- | Extract the type-level list of an NP.
type family NP2List np where NP2List (NP _ xs) = xs

-- | A type alias for empty NP.
type EmptyNP f = NP f '[]

-- | A type alias to non-empty NP.
type NonEmptyNP f x xs = NP f (x : xs)

-- | Split a non-empty NP into its head and tail safely.
splitNonEmptyNP :: forall f x xs p. NonEmptyNP f x xs %p -> (f x, NP f xs)
splitNonEmptyNP (x :* xs) = (x, xs)

--
-- Eq insatnces
--
deriving stock instance Eq (NP f ('[]))
deriving stock instance (Eq (f x), Eq (NP f xs)) => Eq (NonEmptyNP f x xs)

--
-- Show instances
--
instance Show (EmptyNP f) where
  show _ = "Nil"
instance (Show (f x), Show (NP f xs)) => Show (NonEmptyNP f x xs) where
  show (x :* xs) = "(" ++ show x ++ " :* " ++ show xs ++ ")"

------------------------------------------------------------------------------------------------------------------------
-- Traversable and Distributive for NP
------------------------------------------------------------------------------------------------------------------------

--
-- Non-linear
--

-- | A traversable NP with its components @xs@ is parameterized to allow terminating empty NP instance.
class TraversableNP f xs where
  -- | Sequence effect @f@ for all elements of a NP.
  sequence_NP :: NP f xs -> f (NP I xs)

-- | A distributive NP is the duo of 'TraversableNP'.
class DistributiveNP f xs where
  -- | Distribute effect @f@ throughout an NP.
  distribute_NP :: f (NP I xs) -> NP f xs

-- | Construct and deconstruct NP within the effect @f@.
class ConstructibleNP f c | f -> c where
  -- | Create an effectful Nil.
  nil_NP :: forall. f (EmptyNP I)
  -- | Add an element of a NP, within the effect @f@.
  cons_NP :: forall x xs. (c x, c (NP I xs)) => f x -> f (NP I xs) -> f (NonEmptyNP I x xs)
  -- | Deconstruct a non-empty NP to its first element and the rest, within the effect @f.
  uncons_NP :: forall x xs. (c x, c (NP I xs)) => f (NonEmptyNP I x xs) -> (f x, f (NP I xs))

instance ConstructibleNP f c => TraversableNP f '[] where
  sequence_NP _ = nil_NP

instance (ConstructibleNP f c, c x, c (NP I xs), TraversableNP f xs) =>
         TraversableNP f (x:xs) where
  sequence_NP (x :* xs) = cons_NP x (sequence_NP xs)

instance ConstructibleNP f c => DistributiveNP f '[] where
  distribute_NP _ = Nil

instance (ConstructibleNP f c, c x, c (NP I xs), DistributiveNP f xs) =>
         DistributiveNP f (x:xs) where
  distribute_NP fxxs = let (x, fxs) = uncons_NP fxxs in x :* distribute_NP fxs

--
-- Linearly ConstructibleNP
--

-- | A linear-typed 'TraversableNP'.
class LinearTraversableNP f xs where
  -- | A linear-typed 'sequence_NP', where @f ()@ is supplied for the initial distribution process.
  --
  --   /Why @t ()@ is needed?/
  --
  --   In some linear-typed system, conjuring up @t ()@ from nothing is impossible. In such a system, to start the
  --   distribution process, a nil value is provided, instead.
  lsequence_NP :: forall. NP f xs %1 -> f () %1 -> f (NP I xs)

-- | A linear-typed 'DistributiveNP'.
class LinearDistributiveNP f xs where
  -- | A linear-typed 'distribute_NP', where @f ()@ is the waste unit "product" to be linearly discarded.
  ldistribute_NP :: forall. f (NP I xs) %1 -> (NP f xs, f ())

-- | Linearly construct and deconstruct NP within the effect @f@.
class LinearlyConstructibleNP f c | f -> c where
  -- | Create an empty NP from unit, within the effect @f@.
  lunit2nil_NP :: forall. f () %1 -> f (EmptyNP I)
  -- | Reverse of 'lunit2nil_NP'.
  lnil2unit_NP :: forall. f (EmptyNP I) %1 -> f ()
  -- | Add an element of a NP, within the effect @f@.
  lcons_NP :: forall x xs. (c x, c (NP I xs)) => f x %1 -> f (NP I xs) %1 -> f (NonEmptyNP I x xs)
  -- | Deconstruct a non-empty NP to its first element and the rest, within the effect @f.
  luncons_NP :: forall x xs. (c x, c (NP I xs)) => f (NonEmptyNP I x xs) %1 -> (f x, f (NP I xs))

instance LinearlyConstructibleNP f c => LinearTraversableNP f '[] where
  lsequence_NP Nil = lunit2nil_NP

instance (LinearlyConstructibleNP f c, c x, c (NP I xs), LinearTraversableNP f xs) =>
         LinearTraversableNP f (x:xs) where
  lsequence_NP (x :* xs) fnil = lcons_NP x (lsequence_NP xs fnil)

instance LinearlyConstructibleNP f c => LinearDistributiveNP f '[] where
  ldistribute_NP fnil = (Nil, lnil2unit_NP fnil)

instance (LinearlyConstructibleNP f c, c x, c (NP I xs), LinearDistributiveNP f xs) =>
         LinearDistributiveNP f (x:xs) where
  ldistribute_NP fxxs =
    let !(x, fxs) = luncons_NP fxxs
        !(xs, fnil) = ldistribute_NP fxs
    in (x :* xs, fnil)
