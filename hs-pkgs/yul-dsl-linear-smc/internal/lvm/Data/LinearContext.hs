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
