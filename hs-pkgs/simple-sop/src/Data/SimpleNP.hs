{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE LinearTypes       #-}
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
  , SequenceableNP (sequenceNP, unsequenceNP)
  ) where
-- base
import Data.Kind (Type)


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

splitNP :: NP (x : xs) %1 -> (x, NP xs)
splitNP (x :* xs) = (x, xs)

-- | Evaluate the components of NP from left to right within the context of @s@, then produce a new NP with its element
-- in the context of @s@ too.
class ConstructibleNP s x xs where
  consNP :: s x -> s (NP xs) -> s (NP (x:xs))
  unconsNP :: s (NP (x:xs)) -> (s x, s (NP xs))

class SequenceableNP s xs where
  sequenceNP :: forall. s (NP xs) -> NP (MapList s xs)
  default sequenceNP :: forall x' xs'.
    ( x':xs' ~ xs
    , ConstructibleNP s x' xs'
    , SequenceableNP s xs'
    ) =>
    s (NP xs) -> NP (MapList s xs)
  sequenceNP sxxs = let (x, sxs) = unconsNP sxxs in x :* sequenceNP sxs

  unsequenceNP :: forall. NP (MapList s xs) -> s (NP xs)
  default unsequenceNP :: forall x' xs'.
    ( x':xs' ~ xs
    , ConstructibleNP s x' xs'
    , SequenceableNP s xs'
    ) =>
    NP (MapList s xs) -> s (NP xs)
  unsequenceNP (x :* xs) = consNP x (unsequenceNP xs)

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
