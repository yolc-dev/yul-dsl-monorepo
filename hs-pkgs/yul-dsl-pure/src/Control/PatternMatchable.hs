{-# LANGUAGE DefaultSignatures      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LinearTypes            #-}
{-|

Copyright   : (cs) 2024-2025 Miao, ZhiCheng
License     : LGPL-3

Maintainer  : hellwolf@yolc.dev
Stability   : experimental
Portability : GHC2024

= Description

This module contains a set of generalized pattern type classes to match, view, and create matchable values.

== How To Use

1. Use 'match' function in 'PatternMatchable' to do case analysis.

2. Use 'is' in `SingleCasePattern` as a view pattern function for single-cased matchable values.

3. Use 'be' function in 'InjectivePattern' create the pattern @m pat@ from a case of @cs@.

4. The context @m@ is used in the matchable value @m pat@ and the case analysis result @m b@. Additionally the constraint
@k@, with a functional dependency @m -> k@, applies to both @pat@ and @b@.

5. The cases @cs@ has a functional dependency of @m pat -> cs@. It may or may not be similar to @pat@. For example, cases for
@m (Maybe a)@ can be @Just (m a)@ or @Nothing; while cases for @m BOOL@ could be the native boolean values.

6. Use 'couldBe' function in 'PatternMatchable' only when @m pat@ is clear from the context and 'InjectivePattern' is not
available for 'cs -> m pat'.

== Apply Yoneda Embedding

Many matchable values have more than one cases. Only the 'SingleCasePattern' instances have the @is@ function:

  @is :: forall. m pat -> cs@

However, by applying the yoneda embedding @forall x. (a -> x) -> (b -> x) ≅ b -> a@, we have a new function:

  @m pat -> cs ≅ (cs -> m b) -> (m pat -> m b)@

By flipping the arguments of above function, we have the 'match' function:

  @
  m pat -> cs ≅ (cs -> m b) -> (m pat -> m b) -- remove irrelevant pair of brackets; flip arguments.
           ≅ m pat -> (cs -> m b) -> m b
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
  :: forall {k1} {k2 :: k1 -> Constraint} {pat :: k1} {b :: k1}
            {m :: k1 -> *} {cs}.
     (k2 pat, k2 b, PatternMatchable m k2 b cs,
      PatternMatchable m k2 pat cs) =>
     m pat -> m b
-}
module Control.PatternMatchable
  ( PatternMatchable (match, couldBe)
  , SingleCasePattern (is)
  , InjectivePattern (be)
  ) where

-- | Case analysis for pattern matchable values.
class PatternMatchable m pat cs k p | m -> k p, m pat -> cs where
  -- | Match the matchable value @m pat@ with case analysis function @cs -> m b@ that returns the same @m b@.
  match :: forall b. (k pat, k b) => m pat %p -> (cs %p -> m b) %p -> m b
  -- ^ A special implementation of 'match' when @m pat@ is a single case pattern.
  default match :: forall b. (k pat, k b, SingleCasePattern m pat cs k p) => m pat %p -> (cs %p -> m b) %p -> m b
  match mpat f = f (is mpat) -- TODO: view pattern doesn't allow

  -- | Make a case @cs@ that could be the matchable value.
  couldBe :: forall. k pat => cs %p -> m pat
  -- ^ A special implementation of 'couldBe' when it is an injective pattern.
  default couldBe :: forall. (k pat, InjectivePattern m pat cs k p) => cs %p -> m pat
  couldBe = be

-- | A special case for PatternMatchable where a single case @cs@ exists without being in the context of @m@.
class SingleCasePattern m pat cs k p | m -> k p, m pat -> cs where
  -- | Return @cs@ outside of the context of @m@ as the single case of @m pat@. This can be used as a view pattern.
  is :: forall. k pat => m pat %p -> cs

-- | An injective pattern that has a functional dependency of @cs -> m pat@.
class InjectivePattern m pat cs k p | m -> k p, cs -> m pat, m pat -> cs where
  -- | Make the case @cs@ for @m pat@.
  be :: forall. k pat => cs %p -> m pat
