{-# LANGUAGE AllowAmbiguousTypes #-}
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
    PureEffectKind (Pure, Total), PureFn (MkPureFn), YulCat'P
    -- * Build And Call PureFn
    -- $PureFn
  , fn, callFn
    -- * Technical Notes
    -- $yulCatVal
  ) where
-- eth-abi
import Ethereum.ContractABI
--
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

-- | Function without side effects, hence pure.
data PureFn f where
  MkPureFn :: Fn Pure f -> PureFn f

-- -- | Function without side effects and bottom, hence total.
-- newtype TotalFn f = MkPureFn (Fn Total f)

instance ClassifiedFn PureFn PureEffect where
  withClassifiedFn g (MkPureFn f) = g f

-- | Pure yul category morphisms.
type YulCat'P = YulCat Pure

------------------------------------------------------------------------------------------------------------------------
-- $PureFn
------------------------------------------------------------------------------------------------------------------------

-- | Create a 'PureFn' by uncyrrying a currying function @f@ of pure yul categorical values.
--
-- __Note: How to use__
--
-- @
--   -- Use type application to resolve the type @f@:
--   bar = fn "bar" $ uncurry'p @(U256 -> U256)
--     \a -> a + a
-- @
--
-- __Note: How to Read This Type Signature__
--
-- When given:
--
--   * @NP xs = (x1, x2 ... xn)@
--   * @x1' = Pure (NP xs ⤳ x1), x2' = Pure (NP xs ↝ x2), ... xn' = Pure (NP xs ⤳ xn)@
--   * @f = λ x1' -> λ x2' -> ... λ xn' -> Pure (NP xs ↝ b)@
--
-- It returns: @Pure (NP xs ↝ b)@
fn :: forall f xs b m.
       ( YulO2 (NP xs) b
       , EquivalentNPOfFunction f xs b
       , YulCat'P (NP xs) ~ m
       , UncurryingNP f xs b m m m m Many
       , LiftFunction b m m Many ~ m b
       )
    => String
    -> LiftFunction f m m Many    -- ^ uncurrying function type
    -> PureFn (CurryNP (NP xs) b) -- ^ result type, or its short form @m b@
fn cid f = let cat = uncurryingNP @f @xs @b @m @m @m @m f YulId
           in MkPureFn (MkFn (cid, cat))

-- | Call a 'PureFn' by currying it with pure yul categorical values of @r ↝ xn@ until a pure yul categorical value of
-- @r ↝ b@ is returned.
callFn :: forall f xs b r m.
          ( YulO3 (NP xs) b r
          , EquivalentNPOfFunction f xs b
          , YulCat'P r ~ m
          , CurryingNP xs b m m m Many
          , LiftFunction b m m Many ~ m b
          )
       => PureFn f                -- ^ a 'PureFn' of function type @f@
       -> LiftFunction f m m Many -- ^ a currying function type
callFn (MkPureFn (MkFn (cid, cat))) =
  curryingNP @xs @b @m @m @m @Many
  (\xs -> xs >.> YulJmpU (cid, cat))

-- $yulCatVal
--
-- = Yul Categorical Value
--
-- A yul categorical value of @r ⤳ a@ is another way of saying all morphisms that leads to @a@ in the category of
-- 'YulCat'.
--
-- One may also wrap it around an effect kind, e.g. @Pure (r ⤳ a)@ means a pure yul categorical value of @r ⤳ a@.
--
-- From category theory perspective, it is a hom-set @YulCat(-, a)@ that is contravariant of @a@.
--
