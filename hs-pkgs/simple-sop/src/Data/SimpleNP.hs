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
  , splitNP
  , ConstructibleNP (consNP, unconsNP)
  , TraversableNP (sequenceNP), DistributiveNP (distributeNP)
  , LinearTraversableNP (linearSequenceNP), LinearDistributiveNP (linearDistributeNP)
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

splitNP :: forall x xs. NP (x : xs) %1 -> (x, NP xs)
splitNP (x :* xs) = (x, xs)

-- | Evaluate the components of NP from left to right within the context of @s@, then produce a new NP with its element
-- in the context of @s@ too.
class ConstructibleNP s x xs p | s -> p where
  consNP :: forall. s x %p -> s (NP xs) %p -> s (NP (x:xs))
  unconsNP :: forall. s (NP (x:xs)) %p -> (s x, s (NP xs))

class TraversableNP s xs where
  sequenceNP :: forall. s (NP xs) -> NP (MapList s xs)
  default sequenceNP :: forall x' xs'.
    ( x':xs' ~ xs
    , ConstructibleNP s x' xs' Many
    , TraversableNP s xs'
    ) =>
    s (NP xs) -> NP (MapList s xs)
  sequenceNP sxxs = let (x, sxs) = unconsNP sxxs in x :* sequenceNP sxs

class DistributiveNP s xs where
  distributeNP :: forall. NP (MapList s xs) -> s (NP xs)
  default distributeNP :: forall x' xs'.
    ( x':xs' ~ xs
    , ConstructibleNP s x' xs' Many
    , DistributiveNP s xs'
    ) =>
    NP (MapList s xs) -> s (NP xs)
  distributeNP (x :* xs) = consNP x (distributeNP xs)

class LinearTraversableNP s xs where
  linearSequenceNP :: forall. s (NP xs) %1 -> (NP (MapList s xs), s ())
  default linearSequenceNP :: forall x' xs'.
    ( x':xs' ~ xs
    , ConstructibleNP s x' xs' One
    , LinearTraversableNP s xs'
    ) =>
    s (NP xs) %1 -> (NP (MapList s xs), s ())
  linearSequenceNP sxxs = let !(x, sxs) = unconsNP sxxs
                              !(xs, snil) = linearSequenceNP sxs
                          in (x :* xs, snil)

class LinearDistributiveNP s xs where
  linearDistributeNP :: forall. NP (MapList s xs) -> s () %1 -> s (NP xs)
  default linearDistributeNP :: forall x' xs'.
    ( x':xs' ~ xs
    , ConstructibleNP s x' xs' One
    , LinearDistributiveNP s xs'
    ) =>
    NP (MapList s xs) -> s () %1 -> s (NP xs)
  linearDistributeNP (x :* xs) snil = consNP x (linearDistributeNP xs snil)

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
