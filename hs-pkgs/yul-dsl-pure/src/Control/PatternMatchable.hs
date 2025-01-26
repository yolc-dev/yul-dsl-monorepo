{-# LANGUAGE FunctionalDependencies #-}
{-|

Copyright   : (c) 2024-2025 Miao, ZhiCheng
License     : LGPL-3

Maintainer  : hellwolf@yolc.dev
Stability   : experimental
Portability : GHC2024

-}
module Control.PatternMatchable (PatternMatchable (be, match)) where
-- | Pattern matching type class for the pattern @m p@ and its cases @c@.
--
-- == How To Use
--
-- 1. The 'match' function takes a pattern @m p@ and a case analysis function @c -> m b@, then returns @m b@.
--
-- 2. The 'be' function create the pattern @m p@ from a case of @c@.
--
-- 3. Functional dependencies of @m -> m -> k@ limit @b@ to the category @k@ and the result of the case analysis
-- function to @m b@.
--
-- 4. @c@ is left for the 'PatternMatchable' instance to define as a bijective functional dependency of @m p@. For
-- example, a @m BOOL@ might prefer @c = Bool@, instead.
--
-- == Apply Yoneda Embedding
--
-- In many situations, it is not possible to construct directly the inverse of 'be' function, say @caseOf@:
--
--   @caseOf :: forall. m p -> c@
--
-- However, by applying the yoneda embedding @forall x. (a -> x) -> (b -> x) ≅ b -> a@, we have:
--
--   @(c -> m b) -> (m p -> m b) ≅ m p -> c@
--
-- Upon closer inspection, the 'match' function flips the arguments from the yoneda embedded version for the syntactical
-- reason:
--
--   @
--   m p -> c ≅ (c -> m b) -> (m p -> m b) -- remove irrelevant pair of brackets; flip arguments.
--             ≅ m p -> (c -> m b) -> m b
--             ≅ match
--   @
--
--   @mach pat \case (CaseX x) of -> _; (CaseY y) -> _; ...@
--
-- == Pattern Matching Law
--
-- A lawful instance of 'PatternMatchable' should respect the following instance law:
--
--   @\pat -> match pat be ≅ id {∀ m b k. k b => m b}@
--
-- Thanks to parametricity, this is also a free theorem:
--
-- >>> :type \pat -> match pat be
-- \pat -> match pat be
--   :: forall {k1} {k2 :: k1 -> Constraint} {b :: k1} {m :: k1 -> *}
--             {c}.
--      (k2 b, PatternMatchable m k2 b c) =>
--      m b -> m b
class PatternMatchable m k p c | m -> k, m p -> c, c -> m p where
  -- | Match pattern @m p@ with case analysis function @c -> m b@ that returns the same @m b@.
  match :: forall b. k b => m p -> (c -> m b) -> m b

  -- | Be the case @c@ of the pattern @m p@.
  be :: forall. c -> m p
