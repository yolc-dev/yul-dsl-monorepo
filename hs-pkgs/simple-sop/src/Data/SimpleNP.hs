{-# LANGUAGE DefaultSignatures      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LinearTypes            #-}
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
  ( NP (Nil, (:*))
  , MapList, MapNP
  , NonEmptyNP, splitNonEmptyNP
  , ConstructibleNP (consNP, unconsNP)
  , TraversableNP (sequenceNP), DistributiveNP (distributeNP)
  , LinearTraversableNP (linearSequenceNP), LinearDistributiveNP (linearDistributeNP)
  -- re-export multiplicity types
  , Multiplicity (Many, One)
  ) where
-- base
import Data.Kind (Type)
import GHC.Base  (Multiplicity (Many, One))


-- | N-ary product without a type function comparing to its homonym in the "sop" package.
data NP :: [Type] -> Type where
  Nil  :: NP '[]
  (:*) :: x %1 -> NP xs %1 -> NP (x : xs)

infixr 5 :*

-- | Map one type-level list to another with a type function.
type family MapList (f :: Type -> Type) (xs :: [Type]) :: [Type] where
  MapList _ '[] = '[]
  MapList f (x : xs) = f x : MapList f xs

-- | Map the components of NP from one type to another type with a type function.
type family MapNP (f :: Type -> Type) np where
  MapNP f (NP xs) = NP (MapList f xs)

-- | A type alias to any non-empty N-ary products.
type NonEmptyNP x xs = NP (x : xs)

-- | Split a non-empty NP into its head and tail safely.
splitNonEmptyNP :: forall x xs. NonEmptyNP x xs %1 -> (x, NP xs)
splitNonEmptyNP (x :* xs) = (x, xs)

-- | Evaluate the components of NP from left to right within the context of @s@, then produce a new NP with its element
-- in the context of @s@ too.
class ConstructibleNP t x xs p | t -> p where
  consNP :: forall. t x %p -> t (NP xs) %p -> t (NP (x:xs))
  unconsNP :: forall. t (NP (x:xs)) %p -> (t x, t (NP xs))

-- | A traversable NP with its components @xs@ is parameterized to allow terminating empty NP instance.
class TraversableNP t xs where
  -- | Sequence a NP under the context of @t@ into a NP with each component under the same context.
  sequenceNP :: forall. t (NP xs) -> NP (MapList t xs)
  -- ^ The default implementation for 'sequenceNP' when it is also a 'constructibleNP'.
  default sequenceNP :: forall x' xs'.
    ( x':xs' ~ xs
    , ConstructibleNP t x' xs' Many
    , TraversableNP t xs'
    ) =>
    t (NP xs) -> NP (MapList t xs)
  sequenceNP txxs = let (x, txs) = unconsNP txxs in x :* sequenceNP txs

-- | A distributive NP is the duo of 'TraversableNP'.
class DistributiveNP t xs where
  -- | The dual of 'sequenceNP'.
  distributeNP :: forall. NP (MapList t xs) -> t (NP xs)
  -- ^ The default implementation for 'distributeNP' when it is also an 'constructibleNP'.
  default distributeNP :: forall x' xs'.
    ( x':xs' ~ xs
    , ConstructibleNP t x' xs' Many
    , DistributiveNP t xs'
    ) =>
    NP (MapList t xs) -> t (NP xs)
  distributeNP (x :* xs) = consNP x (distributeNP xs)

-- | A linear-typed 'TraversableNP'.
class LinearTraversableNP t xs where
  -- | A linear-typed 'sequenceNP', where @t ()@ is the waste unit "product" to be linearly discarded.
  linearSequenceNP :: forall. t (NP xs) %1 -> (NP (MapList t xs), t ())
  -- ^ The default implementation for 'linearSequenceNP' when it is also an 'constructibleNP'.
  default linearSequenceNP :: forall x' xs'.
    ( x':xs' ~ xs
    , ConstructibleNP t x' xs' One
    , LinearTraversableNP t xs'
    ) =>
    t (NP xs) %1 -> (NP (MapList t xs), t ())
  linearSequenceNP txxs = let !(x, txs) = unconsNP txxs
                              !(xs, tnil) = linearSequenceNP txs
                          in (x :* xs, tnil)

-- | A linear-typed 'DistributiveNP'.
class LinearDistributiveNP t xs where
  -- | A linear-typed 'distributeNP', where @t ()@ is supplied for the initial distribution process.
  --
  --   /Why @t ()@ is needed?/
  --
  --   In some linear-typed system, conjuring up @t ()@ from nothing is impossible. In such a system, to start the
  --   distribution process, a nil value is provided, instead.
  linearDistributeNP :: forall. NP (MapList t xs) -> t () %1 -> t (NP xs)
  -- ^ The default implementation for 'linearDistributeNP' when it is also an 'constructibleNP'.
  default linearDistributeNP :: forall x' xs'.
    ( x':xs' ~ xs
    , ConstructibleNP t x' xs' One
    , LinearDistributiveNP t xs'
    ) =>
    NP (MapList t xs) -> t () %1 -> t (NP xs)
  linearDistributeNP (x :* xs) tnil = consNP x (linearDistributeNP xs tnil)

--
-- Eq insatnces
--
deriving stock instance Eq (NP ('[]))
deriving stock instance (Eq x, Eq (NP xs)) => Eq (NP (x:xs))

--
-- Show instances
--
instance Show (NP '[]) where
  show _ = "Nil"
instance (Show x, Show (NP xs)) => Show (NP (x:xs)) where
  show (x :* xs) = "(" ++ show x ++ " :* " ++ show xs ++ ")"
