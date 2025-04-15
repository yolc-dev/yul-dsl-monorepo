{-|

Copyright   : (c) 2024 Miao, ZhiCheng
License     : LGPL-3

Maintainer  : hellwolf@yolc.dev
Stability   : experimental
Portability : GHC2024

= Description

Linearly versioned monad (LVM) provides a form of "linear safety" in handling effectful data operations.

A short description of such form of "linear safety" can be found in the documentation of 'LVM'.

This module is designed to work with the QualifiedDo syntax, where when import qualified as "LVM", an expression of
@LVM.do@ can start a do-notation syntax block where statements are de-sugared into'(LVM.>>=)' and '(LVM.>>)'.

There may be something to be said about the difference between parameterized and graded monad. In author's limited
understanding of this subject, it seems more appropriate to call 'LVM' parameterized only. For more study about this
matter, please refer to [Orchard, Dominic, Philip Wadler, and Harley Eades III. "Unifying graded and parameterised
monads." arXiv preprint arXiv:2001.10274 (2020).]

-}
module Control.LinearlyVersionedMonad.LVM
  ( -- $linear_safety
    LVM (MkLVM), unLVM, runLVM
  , pure, (>>=), (>>), (=<<), fail
  , unsafeCoerceLVM, veryUnsafeCoerceLVM
  ) where
-- base
import GHC.TypeLits           (KnownNat, type (<=))
-- constraints
import Data.Constraint.Linear (Dict (Dict), (\\))
import Data.Constraint.Nat    (leTrans)
-- linear-base
import Control.Functor.Linear qualified
import Data.Functor.Linear qualified
import Prelude.Linear         (String, error, flip, lseq)
--
import Data.LinearContext


-- $linear_safety
-- == Linear Safety Through Data Versioning
--
-- 'LVM' is parameterized with context data of type @ctx@, an input version @va@, and an output version @vb@. Given the
-- context, similar to the reader monad, it produces an output of type @a@ and a linearly updated new context.  More
-- importantly, it carries a proof that @va <= vb@. Such a proof is vital to provide the linear safety together with the
-- additional 'LVM' monad laws in relations to the bind operations '(>>=)', '(>>)'.

-- | Linear versioned monad (LVM) is a parameterized reader monad with linear safety.
newtype LVM ctx va vb a = MkLVM (ctx ⊸ (Dict (va <= vb), ctx, a))

-- | Unwrap the LVM linearly; otherwise the GHC default syntax createwith a multiplicity-polymorphic arrow.
unLVM :: forall ctx va vb a.
  LVM ctx va vb a ⊸ ctx ⊸ (Dict (va <= vb), ctx, a)
unLVM (MkLVM fa) = fa

-- | Run a linearly versioned monad.
runLVM :: forall a va vb ctx.
  ctx ⊸ LVM ctx va vb a ⊸ (ctx, a)
runLVM ctx m = let !(lp, ctx', a) = unLVM m ctx in lseq lp (ctx', a)

-- | Lift a value into a LVM.
pure :: forall ctx v a. KnownNat v => a ⊸ LVM ctx v v a
pure = Control.Functor.Linear.pure

-- | Monad bind operator for 'LVM', working with the QualifiedDo syntax.
--
-- _Law of Monad_
--
-- 1) Left identity:  @ pure a \>>= h ≡ h a @
--
-- 2) Right identity: @ m \>>= pure ≡ m @
--
-- 3) Associativity:  @ (m \>>= g) \>>= h ≡ m \>>= (\x -> g x \>>= h) @
--
-- _Additional Law of Linearly Versioned Monad_
--
-- Additionally, each 'LVM' carries a proof of monotonic growth of data versions, denoted as such @m [va \<= vb]@. Then
-- we have:
--
-- 1) Law of linearly versioned monad: @ ma [va \<= vb] \>>= mb [vb <= vc] ≡ mc [va <= vc] @
(>>=) :: forall ctx va vb vc a b.
  (KnownNat va, KnownNat vb, KnownNat vc) =>
  LVM ctx va vb a ⊸ (a ⊸ LVM ctx vb vc b) ⊸ LVM ctx va vc b
ma >>= f = MkLVM \ctx -> let !(aleb, ctx', a) = unLVM ma ctx
                             !(blec, ctx'', a') = unLVM (f a) ctx'
                         in  (Dict \\ leTrans @va @vb @vc \\ aleb \\ blec, ctx'', a')

-- | Reverse monad bind operator for 'LVM'.
(=<<) :: forall ctx va vb vc a b.
  (KnownNat va, KnownNat vb, KnownNat vc) =>
  (a ⊸ LVM ctx vb vc b) ⊸ LVM ctx va vb a ⊸ LVM ctx va vc b
(=<<) = flip (>>=)

-- | Monad bind & discard operator, working with the QualifiedDo syntax.
(>>) :: forall ctx va vb vc a b.
  ( KnownNat va, KnownNat vb, KnownNat vc
  , ContextualConsumable ctx a) =>
  LVM ctx va vb a ⊸ LVM ctx vb vc b ⊸ LVM ctx va vc b
ma >> mb = ma >>= \a -> MkLVM \ctx -> let !(bltec, ctx', b) = unLVM mb ctx
                                      in (bltec, contextualConsume ctx' a, b)

-- | This is to handle pattern matching failures in the LVM.do notation. For now we propagate the error as GHC pleases.
fail :: String -> LVM ctx va vb b
fail = error

infixl 1 >>=, >>
infixr 1 =<<

-- Unsafely coerce version proofs, with the same initial version @va@.
unsafeCoerceLVM :: forall va vb vc ctx a.
  va <= vc =>
  LVM ctx va vb a ⊸ LVM ctx va vc a
unsafeCoerceLVM (MkLVM f) = MkLVM \ctx ->
  let !(d, ctx', a) = f ctx
  in (lseq d Dict, ctx', a)

-- More unsafely coerce version proofs than 'unsafeCoerceLVM'.
veryUnsafeCoerceLVM :: forall va vb vp vq ctx a.
  (va <= vb, vp <= vq) =>
  LVM ctx va vb a ⊸ LVM ctx vp vq a
veryUnsafeCoerceLVM (MkLVM f) = MkLVM \ctx ->
  let !(d, ctx', a) = f ctx
  in (lseq d Dict, ctx', a)


--
-- Instances for linear-base
--

instance (KnownNat va, KnownNat vb) => Data.Functor.Linear.Functor (LVM ctx va vb) where
  fmap f ma = ma >>= \a -> MkLVM (Dict, , f a)
instance (KnownNat va, KnownNat vb) => Control.Functor.Linear.Functor (LVM ctx va vb) where
  fmap f ma = ma >>= \a -> MkLVM (Dict, , f a)

instance KnownNat v => Data.Functor.Linear.Applicative (LVM ctx v v) where
  pure a = MkLVM (Dict, , a)
  liftA2 f ma mb = ma >>= \a -> mb >>= \b -> Control.Functor.Linear.pure (f a b)

instance KnownNat v => Control.Functor.Linear.Applicative (LVM ctx v v) where
  pure a = MkLVM (Dict, , a)
  liftA2 f ma mb = ma >>= \a -> mb >>= \b -> Control.Functor.Linear.pure (f a b)

instance KnownNat v => Control.Functor.Linear.Monad (LVM ctx v v) where
  (>>=) = (>>=)
