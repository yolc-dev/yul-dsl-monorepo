{-|

Copyright   : (c) 2024-2025 Miao, ZhiCheng
License     : LGPL-3

Maintainer  : hellwolf@yolc.dev
Stability   : experimental
Portability : GHC2024

= Description

The module provides a set of common combinators for working with linearly versioned monad.

These combinators should be reexported by the contextualized module of 'Control.LinearlyVersionedMonad.LVM'.

-}
module Control.LinearlyVersionedMonad.Combinators
  ( embed, eject
  , toss1, tossN
  , pass1, pass1_, passN, passN_
  ) where
-- base
import GHC.TypeLits                       (KnownNat (natSing), fromSNat)
import Prelude                            qualified as BasePrelude
-- constraints
import Data.Constraint.Linear             (Dict (Dict))
--
import Prelude.Linear                     (Ur (Ur))
-- simple-sop
import Data.TupleN                        (ConvertibleTupleNtoNP, Solo (MkSolo), TupleNtoNP, fromTupleNtoNP)
--
import Control.LinearlyVersionedMonad.LVM
import Data.LinearContext


-- | Embed a value into the context of a LVM.
embed :: forall ctx m v a.
  ( KnownNat v
  , ContextualEmbeddable ctx m a
  ) =>
  a -> LVM ctx v v (m a)
embed a = MkLVM \ctx -> let !(ctx', ma) = contextualEmbed ctx a in (Dict, ctx', ma)

-- | Eject a single value to become the context-free unit (the terminal object of Hask).
eject :: forall ctx m v a.
  ( KnownNat v
  , ContextualConsumable ctx m a
  ) =>
  a ⊸ LVM ctx v v (Ur ())
eject x = MkLVM \ctx -> (Dict, contextualConsume ctx x, Ur ())

--------------------------------------------------------------------------------
-- toss
--------------------------------------------------------------------------------

-- | Toss a TupleN into a contextual unit.
tossN :: forall ctx m v aN.
  ( KnownNat v
  , ConvertibleTupleNtoNP m aN
  , ContextualConsumable ctx m (TupleNtoNP m aN)
  , ContextualEmbeddable ctx m ()
  ) =>
  aN ⊸ LVM ctx v v (m ())
tossN aN = MkLVM \ctx ->
  let ctx' = contextualConsume ctx (fromTupleNtoNP aN)
      !(ctx'', mu) = contextualEmbed ctx' ()
  in (Dict, ctx'', mu)

-- | Toss a single value into a contextual unit.
toss1 :: forall ctx m v a.
  ( KnownNat v
  , ConvertibleTupleNtoNP m (Solo a)
  , ContextualConsumable ctx m (TupleNtoNP m (Solo a))
  , ContextualEmbeddable ctx m ()
  ) =>
  a ⊸ LVM ctx v v (m ())
toss1 x = tossN (MkSolo x)

--------------------------------------------------------------------------------
-- pass
--------------------------------------------------------------------------------

-- -- | Combinator 'pass' for TupleN.
passN :: forall ctx ma va mb vb aN b.
  ( KnownNat va, KnownNat vb
  , ConvertibleTupleNtoNP ma aN
  , ContextualDupable ctx ma (TupleNtoNP ma aN)
  , ContextualDupable ctx mb b
  , ContextualSeqable ctx mb b ma (TupleNtoNP ma aN)
  ) =>
  aN ⊸ (aN ⊸ LVM ctx va vb b) ⊸ LVM ctx va vb (aN, b)
passN aN mb = MkLVM \ctx ->
  let !(ctx1, (aN1, aN2)) = contextualDupTupleN ctx aN
      !(alteb, ctx2, b) = unLVM (mb aN1) ctx1
  in if fromSNat (natSing @va) BasePrelude.== fromSNat (natSing @vb)
     then (alteb, ctx2, (aN2, b))
     else let !(ctx3, (b1, b2)) = contextualDup ctx2 b
              !(ctx4, aN3) = contextualSeqN ctx3 b1 aN2
          in (alteb, ctx4, (aN3, b2))

-- | Combinator 'pass_' for TupleN.
passN_ :: forall ctx ma va mb vb aN b.
  ( KnownNat va, KnownNat vb
  , ConvertibleTupleNtoNP ma aN, ContextualDupable ctx ma (TupleNtoNP ma aN)
  , ContextualDupable ctx mb b
  , ContextualConsumable ctx mb b, ContextualSeqable ctx mb b ma (TupleNtoNP ma aN)
  ) =>
  aN ⊸ (aN ⊸ LVM ctx va vb b) ⊸ LVM ctx va vb aN
passN_ aN mb = passN aN mb >>= (\(aN', b) -> eject b >> pure aN')

-- | Pass the copied data to the next process, then pass both the original data and the result to the next stage.
pass1 :: forall ctx ma va mb vb a b.
  ( KnownNat va, KnownNat vb
  , ConvertibleTupleNtoNP ma (Solo a)
  , ContextualDupable ctx ma (TupleNtoNP ma (Solo a))
  , ContextualDupable ctx mb b
  , ContextualSeqable ctx mb b ma (TupleNtoNP ma (Solo a))
  ) =>
  a ⊸ (a ⊸ LVM ctx va vb b) ⊸ LVM ctx va vb (a, b)
pass1 a mb = passN (MkSolo a) (\(MkSolo a') -> mb a') >>= \(MkSolo a'', b) -> pure (a'', b)

-- | Pass the copied data to the next process, then pass the original data to the next stage and discard the restart.
pass1_ :: forall ctx ma va mb vb a b.
  ( KnownNat va, KnownNat vb
  , ConvertibleTupleNtoNP ma (Solo a)
  , ContextualDupable ctx ma (TupleNtoNP ma (Solo a))
  , ContextualDupable ctx mb b
  , ContextualSeqable ctx mb b ma (TupleNtoNP ma (Solo a))
  ) =>
  a ⊸ (a ⊸ LVM ctx va vb b) ⊸ LVM ctx va vb a
pass1_ a mb = pass1 a mb >>= \(a', b) -> eject b >> pure a'
