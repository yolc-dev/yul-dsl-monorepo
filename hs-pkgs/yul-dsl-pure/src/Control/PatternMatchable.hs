{-# LANGUAGE DefaultSignatures      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ViewPatterns           #-}
{-|

Copyright   : (c) 2024-2025 Miao, ZhiCheng
License     : LGPL-3

Maintainer  : hellwolf@yolc.dev
Stability   : experimental
Portability : GHC2024

= Description

This module contains a set of generalized pattern type classes to match, view, and create matchable values.

== How To Use

1. Use 'match' function in 'PatternMatchable' to do case analysis.

2. Use 'is' in `SingleCasePattern` as a view pattern function for single-cased matchable values.

3. Use 'be' function in 'InjectivePattern' create the pattern @m p@ from a case of @c@.

4. The context @m@ is used in the matchable value @m p@ and the case analysis result @m b@. Additionally the constraint
@k@, with a functional dependency @m -> k@, applies to both @p@ and @b@.

5. The cases @c@ has a functional dependency of @m p -> c@. It may or may not be similar to @p@. For example, cases for
@m (Maybe a)@ can be @Just (m a)@ or @Nothing; while cases for @m BOOL@ could be the native boolean values.

6. Use 'couldBe' function in 'PatternMatchable' only when @m p@ is clear from the context and 'InjectivePattern' is not
available for 'c -> m p'.

== Apply Yoneda Embedding

Many matchable values have more than one cases. Only the 'SingleCasePattern' instances have the @is@ function:

  @is :: forall. m p -> c@

However, by applying the yoneda embedding @forall x. (a -> x) -> (b -> x) ≅ b -> a@, we have a new function:

  @m p -> c ≅ (c -> m b) -> (m p -> m b)@

By flipping the arguments of above function, we have the 'match' function:

  @
  m p -> c ≅ (c -> m b) -> (m p -> m b) -- remove irrelevant pair of brackets; flip arguments.
           ≅ m p -> (c -> m b) -> m b
           ≅ match
  @

This is because that it is syntactically more convenient to use:

  @match pats \case pat1 of -> _; pat2 -> _; _@

== Pattern Matching Law

A lawful instance of 'PatternMatchable' should respect the following law:

  @\pats -> match pats couldBe ≅ id {∀ m b k. k b => m b}@

Thanks to parametricity, this is also a free theorem:

>>> :type \pats -> match pats couldBe
\pats -> match pats couldBe
  :: forall {k1} {k2 :: k1 -> Constraint} {p :: k1} {b :: k1}
            {m :: k1 -> *} {c}.
     (k2 p, k2 b, PatternMatchable m k2 b c,
      PatternMatchable m k2 p c) =>
     m p -> m b
-}
module Control.PatternMatchable
  ( PatternMatchable (match, couldBe)
  , SingleCasePattern (is)
  , InjectivePattern (be)
  ) where

-- | Case analysis for pattern matchable values.
class PatternMatchable m k p c | m -> k, m p -> c where
  -- | Match the matchable value @m p@ with case analysis function @c -> m b@ that returns the same @m b@.
  match :: forall b. (k p, k b) => m p -> (c -> m b) -> m b
  -- ^ A special implementation of 'match' when @m p@ is a single case pattern.
  default match :: forall b. (k p, k b, SingleCasePattern m k p c) => m p -> (c -> m b) -> m b
  match (is -> c) f = f c

  -- | Make a case @c@ that could be the matchable value.
  couldBe :: forall. k p => c -> m p
  -- ^ A special implementation of 'couldBe' when it is an injective pattern.
  default couldBe :: forall. (k p, InjectivePattern m k p c) => c -> m p
  couldBe = be

-- | A special case for PatternMatchable where a single case @c@ exists without being in the context of @m@.
class PatternMatchable m k p c => SingleCasePattern m k p c | m -> k, m p -> c where
  -- | Return @c@ outside of the context of @m@ as the single case of @m p@. This can be used as a view pattern.
  is :: forall. k p => m p -> c

-- | An injective pattern that has a functional dependency of @c -> m p@.
class PatternMatchable m k p c => InjectivePattern m k p c | m -> k, c -> m p where
  -- | Make the case @c@ for @m p@.
  be :: forall. k p => c -> m p
