{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE UndecidableInstances #-}
{-|

Copyright   : (c) 2024-2025 Miao, ZhiCheng
License     : LGPL-3
Maintainer  : hellwolf@yolc.dev
Stability   : experimental

= Description

This module provides the operations for working with the 'Pure' kind of effect for the yul category morphisms.

-}
module YulDSL.Haskell.Effects.Pure
  (
    -- $PureEffectKind
    PureEffectKind (Pure)
    -- $PureFn
  , PureFn (MkPureFn)
  , pureFn
  ) where
-- template-haskell
-- TO BE MOVED
-- yul-dsl
import YulDSL.Core


------------------------------------------------------------------------------------------------------------------------
-- $PureEffectKind
-- * Pure Effect Kind
------------------------------------------------------------------------------------------------------------------------

-- | Data kind for pure morphisms in the yul category.
data PureEffectKind = Pure  -- ^ Pure morphism, may not be total

type instance IsEffectNotPure (eff :: PureEffectKind) = False
type instance MayEffectWorld  (eff :: PureEffectKind) = False


-- | Function without side effects, hence pure.
data PureFn f where
  MkPureFn :: forall f xs b. YulCat Pure (NP xs) b -> PureFn f

pureFn :: (PureFn fn) -> String
pureFn (MkPureFn fn) = show fn

