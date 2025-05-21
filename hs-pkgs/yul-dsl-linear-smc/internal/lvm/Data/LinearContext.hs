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
import Prelude.Linear (Ur (Ur))
-- eth-abi
import Data.SimpleNP  (NP (..))
import Data.TupleN


--------------------------------------------------------------------------------
-- ContextualConsumable
--------------------------------------------------------------------------------

-- | Providing a linear context @ctx@ for consuming @a@.
class ContextualConsumable ctx m a | a -> m where
  -- | Consume @a@ linearly.
  contextualConsume :: forall. ctx ⊸ a ⊸ ctx

instance ContextualConsumable ctx Ur (Ur a) where
  contextualConsume ctx (Ur _) = ctx

instance ContextualConsumable ctx m (NP m '[]) where
  contextualConsume ctx Nil = ctx

instance ( ContextualConsumable ctx m (m x)
         , ContextualConsumable ctx m (NP m xs)
         ) => ContextualConsumable ctx m (NP m (x:xs)) where
  contextualConsume ctx (x :* xs) = let ctx' = contextualConsume ctx x
                                        ctx'' = contextualConsume ctx' xs
                                    in ctx''

--------------------------------------------------------------------------------
-- ContextualDupable
--------------------------------------------------------------------------------

-- | Providing a linear context @ctx@ for duplicate=ing @a@.
class ContextualDupable ctx m a | a -> m where
  -- | Duplicate @a@ linearly.
  contextualDup :: ctx ⊸ a ⊸ (ctx, (a, a))

instance ContextualDupable ctx m (NP m '[]) where
  contextualDup ctx Nil = (ctx, (Nil, Nil))

instance ( ContextualDupable ctx m (m x)
         , ContextualDupable ctx m (NP m xs)
         ) => ContextualDupable ctx m (NP m (x:xs)) where
  contextualDup ctx (x :* xs) =
    let !(ctx', (x', x'')) = contextualDup ctx x
        !(ctx'', (xs', xs'')) = contextualDup ctx' xs
    in (ctx'', (x' :* xs', x'' :* xs''))

-- | Utility function to contextually duplicate a TupleN.
contextualDupTupleN :: forall ctx m aN.
  ( ConvertibleTupleNtoNP m aN
  , ContextualDupable ctx m (TupleNtoNP m (aN))
  ) => ctx ⊸ aN ⊸ (ctx, (aN, aN))
contextualDupTupleN ctx aN = let aNP = fromTupleNtoNP aN
                                 !(ctx', (aNP1, aNP2)) = contextualDup ctx aNP
                              in (ctx', (fromNPtoTupleN aNP1, fromNPtoTupleN aNP2))

--------------------------------------------------------------------------------
-- ContextualSeqable
--------------------------------------------------------------------------------

class ContextualConsumable ctx ma a => ContextualSeqable ctx ma a mb b | b -> mb where
  contextualSeq :: ctx ⊸ a ⊸ b ⊸ (ctx, b)

instance ContextualConsumable ctx Ur a =>
         ContextualSeqable ctx Ur a Ur (Ur ()) where
  contextualSeq ctx a u = (contextualConsume ctx a, u)

instance ContextualConsumable ctx ma a =>
         ContextualSeqable ctx ma a mb (NP mb '[]) where
  contextualSeq ctx a Nil = (contextualConsume ctx a, Nil)

instance ( ContextualDupable ctx ma a
         , ContextualSeqable ctx ma a mb (mb x)
         , ContextualSeqable ctx ma a mb (NP mb xs)
         ) =>
         ContextualSeqable ctx ma a mb (NP mb (x:xs)) where
  contextualSeq ctx a (x :* xs) =
    let !(ctx', (a1, a2)) = contextualDup ctx a
        !(ctx'', x') = contextualSeq ctx' a1 x
        !(ctx''', xs') = contextualSeq ctx'' a2 xs
    in (ctx''', x' :* xs')

contextualSeqN :: forall ctx ma a mb bN.
  ( ConvertibleTupleNtoNP mb bN
  , ContextualSeqable ctx ma a mb (TupleNtoNP mb bN)
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
