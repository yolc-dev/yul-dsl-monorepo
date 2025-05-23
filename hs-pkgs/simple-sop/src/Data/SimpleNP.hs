{-# LANGUAGE LinearTypes #-}
{-|

Copyright   : (c) 2024-2025 Miao, ZhiCheng
License     : MIT

Maintainer  : hellwolf@yolc.dev
Stability   : experimental
Portability : GHC2024

= Description

A simple n-ary product without any type function that is present in the sop-core package.

-}
module Data.SimpleNP
  ( -- * N-ary Product
    I (I)
  , NP (Nil, (:*)), NP2List
  , NonEmptyNP, splitNonEmptyNP
    -- re-export multiplicity types
  , Multiplicity (Many, One)
    -- * Applicative-like Classes For NP
  , ConstructibleNP (consNP, unconsNP)
  , TraversableNP (sequenceNP), DistributiveNP (distributeNP)
  , LinearTraversableNP (linearSequenceNP), LinearDistributiveNP (linearDistributeNP)
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

-- | A type alias to non-empty N-ary products.
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
instance Show (NP f '[]) where
  show _ = "Nil"
instance (Show (f x), Show (NP f xs)) => Show (NonEmptyNP f x xs) where
  show (x :* xs) = "(" ++ show x ++ " :* " ++ show xs ++ ")"

------------------------------------------------------------------------------------------------------------------------
-- Applicative-like classes for NP. TODO: Defer this to the actual applicative framework, instead.
------------------------------------------------------------------------------------------------------------------------

-- | Construct and deconstruct NP within the effect @f@
class ConstructibleNP f x xs p | f -> p where
  -- | Add an element of a NP, within the effect @f@.
  consNP :: forall. f x %p -> f (NP I xs) %p -> f (NonEmptyNP I x xs)
  -- | Deconstruct a non-empty NP to its first element and the rest, within the effect @f.
  unconsNP :: forall. f (NonEmptyNP I x xs) %p -> (f x, f (NP I xs))

-- | A traversable NP with its components @xs@ is parameterized to allow terminating empty NP instance.
class TraversableNP f xs where
  -- | Sequence a NP under the context of @f@ into a NP with each component under the same context.
  sequenceNP :: forall. f (NP I xs) -> NP f xs

-- ^ The terminal case of sequence should be universally Nil.
instance TraversableNP f '[] where
  sequenceNP _ = Nil

-- ^ The default implementation of non-empty 'TraversableNP' when it is also a 'constructibleNP'.
instance ( ConstructibleNP f x xs Many
         , TraversableNP f xs
         ) =>
         TraversableNP f (x:xs) where
    sequenceNP txxs = let (x, txs) = unconsNP txxs in x :* sequenceNP txs

-- | A distributive NP is the duo of 'TraversableNP'.
class DistributiveNP f xs where
  -- | The dual of 'sequenceNP'.
  distributeNP :: forall. NP f xs -> f (NP I xs)

-- ^ The default implementation for non-empty 'DistributiveNP' when it is also an 'constructibleNP'.
instance ( ConstructibleNP f x xs Many
         , DistributiveNP f xs
         ) =>
         DistributiveNP f (x:xs) where
  distributeNP (x :* xs) = consNP x (distributeNP xs)

-- | A linear-typed 'TraversableNP'.
class LinearTraversableNP f xs where
  -- | A linear-typed 'sequenceNP', where @t ()@ is the waste unit "product" to be linearly discarded.
  linearSequenceNP :: forall. f (NP I xs) %1 -> (NP f xs, f ())

-- ^ The default implementation for non-empty 'linearSequenceNP' when it is also an 'constructibleNP'.
instance ( ConstructibleNP f x xs One
         , LinearTraversableNP f xs
         ) =>
         LinearTraversableNP f (x:xs) where
  linearSequenceNP txxs =
    let !(x, txs) = unconsNP txxs
        !(xs, tnil) = linearSequenceNP txs
    in (x :* xs, tnil)

-- | A linear-typed 'DistributiveNP'.
class LinearDistributiveNP f xs where
  -- | A linear-typed 'distributeNP', where @t ()@ is supplied for the initial distribution process.
  --
  --   /Why @t ()@ is needed?/
  --
  --   In some linear-typed system, conjuring up @t ()@ from nothing is impossible. In such a system, to start the
  --   distribution process, a nil value is provided, instead.
  linearDistributeNP :: forall. NP f xs %1 -> f () %1 -> f (NP I xs)


-- ^ The default implementation for non-empty 'linearDistributeNP' when it is also an 'constructibleNP'.
instance ( ConstructibleNP f x xs One
         , LinearDistributiveNP f xs
         ) =>
         LinearDistributiveNP f (x:xs) where
  linearDistributeNP (x :* xs) tnil = consNP x (linearDistributeNP xs tnil)
