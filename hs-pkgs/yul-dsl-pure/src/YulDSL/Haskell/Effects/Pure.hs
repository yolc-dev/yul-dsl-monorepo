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
    PureEffectKind (Pure, Total)
    -- $PureFn
  , PureFn (MkPureFn)
  ) where
-- template-haskell
-- TO BE MOVED
import Data.Type.Function
-- yul-dsl
import YulDSL.Core


------------------------------------------------------------------------------------------------------------------------
-- $PureEffectKind
-- * Pure Effect Kind
------------------------------------------------------------------------------------------------------------------------

-- | Data kind for pure morphisms in the yul category.
data PureEffectKind = Pure  -- ^ Pure morphism, may not be total
                    | Total -- ^ TODO, to further distinguish totality from other pure morphism.

type instance IsEffectNotPure (eff :: PureEffectKind) = False
type instance MayEffectWorld  (eff :: PureEffectKind) = False


-- | Function without side effects, hence pure.
data PureFn f where
  MkPureFn :: forall f xs b.
    ( EquivalentNPOfFunction f xs b
    , YulO2 (NP xs) b
    ) =>
    NamedYulCat Pure (NP xs) b -> PureFn f

instance EquivalentNPOfFunction f xs b => ClassifiedYulCat (PureFn f) PureEffect (NP xs) b where
  withClassifiedYulCat (MkPureFn f) g = g f

