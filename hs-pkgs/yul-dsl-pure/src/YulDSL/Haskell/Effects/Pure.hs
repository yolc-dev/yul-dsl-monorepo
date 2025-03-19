{-|

Copyright   : (c) 2024-2025 Miao, ZhiCheng
License     : LGPL-3
Maintainer  : hellwolf@yolc.dev
Stability   : experimental

= Description

This module provides the operations for working with the 'Pure' kind of effect for the yul category morphisms.

-}
module YulDSL.Haskell.Effects.Pure
  ( -- * Pure Effect Kind
    -- $PureEffectKind
    PureEffectKind (Pure, Total)
  , PureY, YulCat'P
  ) where
-- yul-dsl
import YulDSL.Core.YulCat


------------------------------------------------------------------------------------------------------------------------
-- $PureEffectKind
------------------------------------------------------------------------------------------------------------------------

-- | Data kind for pure morphisms in the yul category.
data PureEffectKind = Pure  -- ^ Pure morphism, may not be total
                    | Total -- ^ TODO, to further distinguish totality from other pure morphism.

instance KnownYulCatEffect Pure where classifyYulCatEffect = PureEffect
instance KnownYulCatEffect Total where classifyYulCatEffect = PureEffect

type instance IsEffectNotPure (eff :: PureEffectKind) = False
type instance MayEffectWorld  (eff :: PureEffectKind) = False

type PureY f = Y Pure f

-- | Pure yul category morphisms.
type YulCat'P = YulCat Pure
