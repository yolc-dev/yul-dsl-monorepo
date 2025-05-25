{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE LinearTypes          #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.SimpleNP.ConstructibleNP
  ( ConstructibleNP (nil_NP, cons_NP, uncons_NP)
  , LinearlyConstructibleNP (lunit2nil_NP, lmkunit_NP, lignore_NP, ldiscard_NP, lcons_NP, luncons_NP)
  , lsequence_NonEmptyNP, ldistribute_NonEmptyNP
  ) where
import Data.SimpleNP


--
-- Non-linear
--

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
-- Linear
--

-- | Linearly construct and deconstruct NP within the effect @f@.
class LinearlyConstructibleNP f c | f -> c where
  -- | Create an empty NP from unit.
  lunit2nil_NP :: forall. f () %1 -> f (EmptyNP I)
  -- | Discard any NP to a unit.
  ldiscard_NP :: forall x. c x => f x %1 -> f ()
  -- | Ignore a unit by using another value.
  lignore_NP :: forall x. c x => f () %1 -> f x %1 -> f x
  -- | Create a unit and return the original value.
  lmkunit_NP :: forall x. c x => f x %1 -> (f x, f ())
  -- | Add an element of a NP.
  lcons_NP :: forall x xs. (c x, c (NP I xs)) => f x %1 -> f (NP I xs) %1 -> f (NonEmptyNP I x xs)
  -- | Deconstruct a non-empty NP to its first element and the rest.
  luncons_NP :: forall x xs. (c x, c (NP I xs)) => f (NonEmptyNP I x xs) %1 -> (f x, f (NP I xs))

lsequence_NonEmptyNP :: forall f c x xs.
  ( LinearlyConstructibleNP f c, c x, c (NP I xs)
  , LinearTraversableNP f (x:xs)
  ) =>
  NonEmptyNP f x xs %1 -> f (NonEmptyNP I x xs)
lsequence_NonEmptyNP (x :* xs) = let !(x', u) = lmkunit_NP x in lsequence_NP (x' :* xs) u

ldistribute_NonEmptyNP :: forall f c x xs.
  ( LinearlyConstructibleNP f c, c x, c (NP I xs)
  , LinearDistributiveNP f (x:xs)
  ) =>
  f (NonEmptyNP I x xs) %1 -> NonEmptyNP f x xs
ldistribute_NonEmptyNP fxxs = let !(x :* xs, u) = ldistribute_NP fxxs in lignore_NP u x :* xs

instance LinearlyConstructibleNP f c => LinearTraversableNP f '[] where
  lsequence_NP Nil = lunit2nil_NP

instance (LinearlyConstructibleNP f c, c x, c (NP I xs), LinearTraversableNP f xs) =>
         LinearTraversableNP f (x:xs) where
  lsequence_NP (x :* xs) fnil = lcons_NP x (lsequence_NP xs fnil)

instance (LinearlyConstructibleNP f c, c (EmptyNP I)) => LinearDistributiveNP f '[] where
  ldistribute_NP fnil = (Nil, ldiscard_NP fnil)

instance (LinearlyConstructibleNP f c, c x, c (NP I xs), LinearDistributiveNP f xs) =>
         LinearDistributiveNP f (x:xs) where
  ldistribute_NP fxxs =
    let !(x, fxs) = luncons_NP fxxs
        !(xs, fnil) = ldistribute_NP fxs
    in (x :* xs, fnil)
