{-# LANGUAGE FunctionalDependencies #-}

module Control.PatternMatchable (PatternMatchable (inCase, match)) where

-- | Pattern matching type class for the pattern @p@ and its cases @c@.
--
-- Additionally:
--
-- 1. @m@ can be used to limit @p@ and @b@ to same category @k@.
--
-- 2. In comparison, @c@ is left alone, to give the flexibility of how it is related to @m p@ to their
-- 'PatternMatchable' instance. For example, a @m BOOL@ might prefer @c = Bool@, instead.
--
-- 3. @\mp -> match mp inCase ≅ id{k} @
--
-- >>> :type \mp -> match mp inCase
-- \mp -> match mp inCase
--   :: forall {k1} {k2 :: k1 -> Constraint} {b :: k1} {m :: k1 -> *}
--             {c} {p :: k1}.
--      (k2 b, PatternMatchable m b c k2, PatternMatchable m p c k2) =>
--      m p -> m b
class PatternMatchable m p c k | m -> k, m p -> c, c -> m p where
  -- | Create the pattern @m p@ in the case of @c@.
  inCase :: forall. c -> m p

  -- | Match pattern @m p@ with case analysis function @c -> m b@ that returns a @m b@.
  --
  -- In many cases, it is not possible to construct: @fromCases :: forall. m p -> c@.
  -- However, applying the yoneda embedding @forall x. (a -> x) -> (b -> x) ≅ b -> a@,
  -- then we have: @(c -> m b) -> (m p -> m b) ≅ m p -> c@.
  --
  -- The'match' function flips the arguments from yoneda embedding for the syntactical reason:
  -- @mach p (\c -> case c of -> _)@
  match :: forall b. k b => m p -> (c -> m b) -> m b
