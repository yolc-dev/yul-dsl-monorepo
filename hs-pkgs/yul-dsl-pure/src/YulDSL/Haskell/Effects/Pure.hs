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
  ( -- $PureEffectKind
    PureEffectKind (Pure, Total)
  , PureY, YulCat'P
    -- $PureFn
  , PureFn (MkPureFn), fn', fn, call0
    -- * Template Haskell Support
  , locId
    -- * Technical Notes
    -- $yulCatVal
  ) where
-- template-haskell
import Language.Haskell.TH qualified as TH
-- yul-dsl
import YulDSL.Core

------------------------------------------------------------------------------------------------------------------------
-- $PureEffectKind
-- * Pure Effect Kind
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

------------------------------------------------------------------------------------------------------------------------
-- $PureFn
-- * Pure Functions
------------------------------------------------------------------------------------------------------------------------

-- | Function without side effects, hence pure.
newtype PureFn f = MkPureFn (Fn Pure f)

instance ClassifiedFn PureFn PureEffect where
  withClassifiedFn g (MkPureFn f) = g f

-- -- | Function without side effects and bottom, hence total.
-- newtype TotalFn f = MkPureFn (Fn Total f)

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
fn' :: forall f xs b m.
  ( YulO2 (NP xs) b
  , YulCat'P (NP xs) ~ m
  , UncurriableNP f xs b m m m m Many
  ) =>
  String ->
  LiftFunction f m m Many -> -- ^ uncurrying function type
  PureFn (CurryNP (NP xs) b) -- ^ result type, or its short form @m b@
fn' cid f = let cat = uncurryNP @f @xs @b @m @m @m @m f YulId in MkPureFn (MkFn (cid, cat))

-- | Create a 'PureFn' with automatic id based on function definition source location.
fn :: TH.Q TH.Exp
fn = [e| fn' $locId |]

instance forall f x xs b g a.
         ( YulO4 x (NP xs) b a
         , EquivalentNPOfFunction f (x:xs) b
         , CurriableNP g xs b (YulCat'P a) (YulCat'P a) (YulCat'P a) Many
         ) =>
         CallableFunctionNP PureFn f x xs b (YulCat'P a) (YulCat'P a) Many where
  call (MkPureFn (MkFn (cid, cat))) x = curryNP @g @xs @b @(YulCat'P a) @(YulCat'P a) @(YulCat'P a)
    (\xs -> consNP x xs >.> YulJmpU (cid, cat))

call0 :: forall b a.
  ( YulO2 b a
  , EquivalentNPOfFunction b '[] b
  ) => PureFn b -> YulCat'P a b
call0 f = callN f ()

instance forall f xs b r.
         ( YulO3 (NP xs) b r
         , EquivalentNPOfFunction f xs b
         , ConvertibleNPtoTupleN (NP (MapList (YulCat'P r) xs))
         , DistributiveNP (YulCat'P r) xs
         ) =>
         CallableFunctionN PureFn f xs b (YulCat'P r) (YulCat'P r) Many where
  callN (MkPureFn (MkFn (cid, cat))) tpl = distributeNP (fromTupleNtoNP tpl) >.> YulJmpU (cid, cat)

-- | Automatically generate a source location based id using template haskell.
locId :: TH.Q TH.Exp
locId = do
  loc <- TH.location
  let modname = TH.loc_module loc
      -- normalize module name: replace "."
      modname' = fmap (\x -> if x `elem` "." then '_' else x) modname
      (s1, s2) = TH.loc_start loc
  TH.litE (TH.StringL (modname' ++ "_" ++ show s1 ++ "_" ++ show s2))

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
