{-|

Copyright   : (c) 2024-2025 Miao, ZhiCheng
License     : LGPL-3

Maintainer  : hellwolf@yolc.dev
Stability   : experimental
Portability : GHC2024

= Description

Type classes required by the linear context that works with the 'Control.LinearlyVersionedMonad.LVM'.

-}
module Data.LinearContext
  ( ContextualConsumable (contextualConsume)
  , ContextualDupable (contextualDup), contextualDupTupleN
  , ContextualSeqable (contextualSeq), contextualSeqN
  , ContextualEmbeddable (contextualEmbed)
  ) where
-- linear-base
import Prelude.Linear (lseq)
-- eth-abi
import Data.SimpleNP  (NP (..))
import Data.TupleN


--------------------------------------------------------------------------------
-- ContextualConsumable
--------------------------------------------------------------------------------

-- | Providing a linear context @ctx@ for consuming @a@.
class ContextualConsumable ctx a where
  -- | Consume @a@ linearly.
  contextualConsume :: forall. ctx ⊸ a ⊸ ctx

instance ContextualConsumable ctx () where
  contextualConsume ctx u = lseq u ctx

instance ContextualConsumable ctx (NP '[]) where
  contextualConsume ctx Nil = ctx

instance ( ContextualConsumable ctx x
         , ContextualConsumable ctx (NP xs)
         ) => ContextualConsumable ctx (NP (x:xs)) where
  contextualConsume ctx (x :* xs) = let ctx' = contextualConsume ctx x
                                        ctx'' = contextualConsume ctx' xs
                                    in ctx''

--------------------------------------------------------------------------------
-- ContextualDupable
--------------------------------------------------------------------------------

-- | Providing a linear context @ctx@ for duplicate=ing @a@.
class ContextualDupable ctx a where
  -- | Duplicate @a@ linearly.
  contextualDup :: ctx ⊸ a ⊸ (ctx, (a, a))

instance ContextualDupable ctx (NP '[]) where
  contextualDup ctx Nil = (ctx, (Nil, Nil))

instance ( ContextualDupable ctx x
         , ContextualDupable ctx (NP xs)
         ) => ContextualDupable ctx (NP (x:xs)) where
  contextualDup ctx (x :* xs) =
    let !(ctx', (x', x'')) = contextualDup ctx x
        !(ctx'', (xs', xs'')) = contextualDup ctx' xs
    in (ctx'', (x' :* xs', x'' :* xs''))

-- | Utility function to contextually duplicate a TupleN.
contextualDupTupleN :: forall ctx aN.
  ( ConvertibleTupleNtoNP aN
  , ContextualDupable ctx (TupleNtoNP (aN))
  ) => ctx ⊸ aN ⊸ (ctx, (aN, aN))
contextualDupTupleN ctx aN = let aNP = fromTupleNtoNP aN
                                 !(ctx', (aNP1, aNP2)) = contextualDup ctx aNP
                              in (ctx', (fromNPtoTupleN aNP1, fromNPtoTupleN aNP2))

--------------------------------------------------------------------------------
-- ContextualSeqable
--------------------------------------------------------------------------------

class ContextualConsumable ctx a => ContextualSeqable ctx a b where
  contextualSeq :: ctx ⊸ a ⊸ b ⊸ (ctx, b)

instance ContextualConsumable ctx a => ContextualSeqable ctx a () where
  contextualSeq ctx a b = (contextualConsume ctx a, b)

instance ContextualConsumable ctx a => ContextualSeqable ctx a (NP '[]) where
  contextualSeq ctx a Nil = (contextualConsume ctx a, Nil)

instance ( ContextualDupable ctx a
         , ContextualSeqable ctx a x
         , ContextualSeqable ctx a (NP xs)
         ) => ContextualSeqable ctx a (NP (x:xs)) where
  contextualSeq ctx a (x :* xs) =
    let !(ctx', (a1, a2)) = contextualDup ctx a
        !(ctx'', x') = contextualSeq ctx' a1 x
        !(ctx''', xs') = contextualSeq ctx'' a2 xs
    in (ctx''', x' :* xs')

contextualSeqN :: forall ctx a bN.
  ( ConvertibleTupleNtoNP bN
  , ContextualSeqable ctx a (TupleNtoNP (bN))
  ) => ctx ⊸ a ⊸ bN ⊸ (ctx, bN)
contextualSeqN ctx a bN =
  let bNP = fromTupleNtoNP bN
      !(ctx', bNP') = contextualSeq ctx a bNP
  in (ctx', fromNPtoTupleN bNP')

--------------------------------------------------------------------------------
-- ContextualEmbeddable
--------------------------------------------------------------------------------

-- | Providing a linear context @ctx@ for embedding a pure value @a@ in @m@.
class ContextualEmbeddable ctx m a where
  -- | Consume @a@ linearly.
  contextualEmbed :: ctx ⊸ a -> (ctx, m a)
